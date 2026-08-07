{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  PHASE 5: FROM LINEAR CONTEXTS TO INSTRUCTIONS, AND THE HOARE TRIPLE
  THAT SAYS THE EMITTED CODE IS RIGHT.

  Two developments in this repository stop one step short of each other.

    * `LinLam/Codegen` takes a linear λ-term to a HEAP.  Its `layout`
      sends variable position `i` to location `i`, and `layPres` proves
      that a context splitting `Use⊎ u₁ u₂ u` becomes a DISJOINT heap
      splitting -- the source's missing `(true,true)` constructor
      manufacturing the target's `_#_` conjunct.  It never emits an
      instruction.

    * `ISA.Interp` derives the Hoare rules -- sequencing, the empty
      program, consequence, framing -- from an abstract splitting-
      preserving interpretation, and `ISA.Program` supplies the free
      monoid of instruction sequences.  It never mentions a source
      language.

  This file joins them.  It emits instructions, and it proves the
  triple.

  ------------------------------------------------------------------
  WHAT IS COMPILED, AND WHY IT DEPENDS ONLY ON THE USAGE
  ------------------------------------------------------------------

  A linear term's FRAME is `layout u`: one cell per live variable, at the
  variable's own position.  The code that builds it is

      code i []          = []
      code i (true  ∷ u) = putI i v1 ∷ code (suc i) u
      code i (false ∷ u) = code (suc i) u

  -- one `putI` per live position, in increasing address order, and the
  offset argument is what makes the recursion go through, exactly as it
  does for `lay`.  Note that this recurses on the USAGE, not on the term:
  the emitted code is a function of the index, which is why `compile`
  below can be `LinLam/Codegen.emit`'s shape (`⊕ᴰ-I` at the index itself)
  rather than a fold over `Tm`.  That is not a shortcut; it is what
  `layout` already told us.  A binder SHIFTS every address by one
  (`layout (true ∷ u)` is `(0,v1) ∷ lay 1 u`), so a term-directed
  compilation would have to renumber at every `tlam`, whereas the
  usage-directed one addresses the whole scope once.

  ------------------------------------------------------------------
  THE TRIPLE, AND WHAT IT COST
  ------------------------------------------------------------------

      codeTriple : ⟪ ⌈ h ⌉ ⟫ code i u ⟪ ⌈ layAt h i u ⌉ ⟫ᵖ

  Three clauses.  The `[]` clause is `emptyRule`; the `false` clause is
  the induction hypothesis unchanged; the `true` clause is

      seq∷ (putI i v1) (code (suc i) u)
        (instrRule (putI i v1) (putAx i v1 h))
        (codeTriple u (suc i) (h ++h single i v1))

  and every name in it comes from `ISA.Program`.  `seq∷` is `seq++` at
  the head/tail splitting, `seq++` is `ISA.Interp.seq` at `splitAll`, and
  `ISA.Interp.seq` is

      wp-⊑ (⟦⟧-⨟ r sp) Q ∘g seqCmd ⟦ r₁ ⟧ ⟦ r₂ ⟧ t₁ t₂

  i.e. (`sem` is a monoid homomorphism) ∙ (`wp` is contravariant) ∙
  (`wp` inverts `⨟`).  NOTHING about sequencing is proved here.  The
  accounting, in the same form `ISA.Program` states it:

      Hoare sequencing proved in this file:        0
      Hoare framing proved in this file:           0
      inductions over a program in this file:      0
      inductions over a USAGE in this file:        2   (`code`'s triple,
                                                        and `layAt ≡ lay`)

  ------------------------------------------------------------------
  NO-ALIASING, AS A POSTCONDITION
  ------------------------------------------------------------------

  The point of compiling a LINEAR source language is that the two
  premises of an application own disjoint memory.  Here that is a Hoare
  postcondition and not a side argument:

      noAlias : Use⊎ u₁ u₂ u
              → ⟪ ⌈ [] ⌉ ⟫ code 0 u ⟪ ⌈ layout u₁ ⌉ ∗ ⌈ layout u₂ ⌉ ⟫ᵖ

  `∗` is `⊗ˢ appop` at `heapFib`, so its very inhabitation carries the
  `_#_` conjunct.  And the term that provides it is

      splitPost s = ⌈⌉-E (layJoin s),
      layJoin  s = ⊗ˢ-I appop (layout u) (layPres appop .homSplit u …) …

  -- Yoneda applied to a single point, and the point is `layPres`.  So
  the disjointness in the postcondition is not established here; it is
  `LinLam/Codegen`'s split preservation, transported across `⌈⌉-E`.  The
  missing constructor of `Use⊎` is doing the work, four modules away.

  ------------------------------------------------------------------
  THE FRAME RULE, USED
  ------------------------------------------------------------------

  `spill` allocates a scratch cell after the frame is built, and states
  that the variables' cells are untouched:

      ⟪ ⌈ [] ⌉ ⟫ code 0 u ++ (newI v1 ∷ [])
      ⟪ (⊕ᴰ Loc λ l → ⌈ single l v1 ⌉) ∗ ⌈ layout u ⌉ ⟫ᵖ

  built from `seq++` and `ISA.Interp.frameRule`, whose hypothesis
  `Local (sem allocProg)` is `local-⨟` applied to `ISA.Toy.localAlloc`.
  The frame is `⌈ layout u ⌉` -- the compiler's own output -- so this is
  the frame rule doing the job it exists for.  It is `newI` and not
  `putI` that appears, and `Machine.noPutLocal` says why it has to be.

  ------------------------------------------------------------------
  END TO END
  ------------------------------------------------------------------

  `Machine.observe` turns a triple between representables into an
  equation about the FUNCTION `exec`, using `exec-sound` -- the only exit
  from the calculus, and it appears in exactly one definition, `runU`.
  Then

      runU (true ∷ true ∷ [])  :  exec (code 0 …) []  Eq.≡  layout (…)

  is the compiler's correctness for a two-variable term, DERIVED from the
  triple rather than recomputed, and the `refl` block at the bottom
  evaluates the whole chain: term ↦ instructions ↦ heap.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1, all marked: `code`, `layAt`, `codeTriple`, `detCode` and the
  three `++h` lemmas -- all of them recursions on a usage or a heap,
  i.e. on a carrier, which is what building a pass is allowed to do.
  Everything from `compileTriple` down is a composite of `seq∷`,
  `seq++`, `instrRule`, `emptyRule`, `consequenceᵖ`, `frameRule`,
  `⌈⌉-E`, `⌈⌉-pt`, `⊗ˢ-I`, `⊕ᴰ-I`, `boolΠ` and `idg`.
-}
open import Cubical.Foundations.Prelude

module Compile.LinToISA.Codegen where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.List using (List; []; _∷_; _++_)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Theories.Monoid
-- qualified: `SplitPresAt`'s `homSplit` and `ISA.Interp`'s `homSplit`
-- are the same shape at two promodels, and both are in scope here
import TheoryGrammar.CarrierMap as CM

-- the TARGET, unqualified: the Hoare layer is what most of this file
-- speaks
open import Compile.LinToISA.Machine public

-- the SOURCE, qualified -- `LinLam/Codegen` re-exports the linear
-- context promodel's own `⊢`, `⊗ˢ`, `⌈⌉`, `boolΠ`, ... and the two
-- theories' combinators must not collide.  Exactly the discipline
-- `LinLam/Codegen` itself uses, with the sides swapped.
import TheoryGrammar.Instances.LinLam.Codegen as L

-- ==================================================================
-- THE EMITTED CODE.  PRIMITIVE (phase 1): recursion on the usage, in
-- lockstep with `lay`.
-- ==================================================================

code : ℕ → L.Usage → Program
code i []          = []
code i (true  ∷ u) = putI i v1 ∷ code (suc i) u
code i (false ∷ u) = code (suc i) u

compileU : L.Usage → Program
compileU = code 0

-- PRIMITIVE (phase 1): the heap the code builds, written with the SAME
-- recursion so that the triple's induction is definitional at every
-- clause.  `layAt≡` below identifies it with `h ++h lay i u`.
layAt : Heap → ℕ → L.Usage → Heap
layAt h i []          = h
layAt h i (true  ∷ u) = layAt (h ++h single i v1) (suc i) u
layAt h i (false ∷ u) = layAt h (suc i) u

-- ==================================================================
-- THE TRIPLE.  THE RESULT OF THE PHASE.
--
-- Every name on the right-hand side is from `ISA.Program`, and
-- `ISA.Program` got them from `ISA.Interp` for every instruction set at
-- once.  This file contributes the induction on the usage and nothing
-- else.
-- ==================================================================

-- PRIMITIVE (phase 1): the recursion is on `u`, exactly as `code`'s is.
codeTriple : (u : L.Usage) (i : ℕ) (h : Heap)
           → ⟪ ⌈ h ⌉ ⟫ code i u ⟪ ⌈ layAt h i u ⌉ ⟫ᵖ
codeTriple []          i h = emptyRule ⌈ h ⌉
codeTriple (true  ∷ u) i h =
  seq∷ (putI i v1) (code (suc i) u)
       (instrRule (putI i v1) (putAx i v1 h))
       (codeTriple u (suc i) (h ++h single i v1))
codeTriple (false ∷ u) i h = codeTriple u (suc i) h

-- ==================================================================
-- ... AND ITS POSTCONDITION IS `LinLam/Codegen`'s LAYOUT.
--
-- Three `++h` lemmas, all of them the monoid laws of the free monoid on
-- cells.  `eqTrans` is `ISA.Machine`'s.
-- ==================================================================

-- PRIMITIVE (phase 1)
app-nil : (h : Heap) → (h ++h []) Eq.≡ h
app-nil []            = Eq.refl
app-nil ((l , x) ∷ h) = Eq.ap ((l , x) ∷_) (app-nil h)

-- PRIMITIVE (phase 1)
app-snoc : (h : Heap) (c : Cell) (k : Heap)
         → ((h ++h (c ∷ [])) ++h k) Eq.≡ (h ++h (c ∷ k))
app-snoc []            c k = Eq.refl
app-snoc ((l , x) ∷ h) c k = Eq.ap ((l , x) ∷_) (app-snoc h c k)

-- PRIMITIVE (phase 1)
layAt≡ : (u : L.Usage) (i : ℕ) (h : Heap) → layAt h i u Eq.≡ (h ++h L.lay i u)
layAt≡ []          i h = Eq.sym (app-nil h)
layAt≡ (true  ∷ u) i h =
  eqTrans (layAt≡ u (suc i) (h ++h single i v1))
          (app-snoc h (i , v1) (L.lay (suc i) u))
layAt≡ (false ∷ u) i h = layAt≡ u (suc i) h

layAt0 : (u : L.Usage) → layAt [] 0 u Eq.≡ L.layout u
layAt0 u = layAt≡ u 0 []

-- coercion of a representable along `Eq` -- `⌈⌉-E` at the equation
-- itself, since `⌈ b ⌉ a` IS `a Eq.≡ b`.  Yoneda, one more time.
coe⌈⌉ : {a b : Heap} → a Eq.≡ b → ⌈ a ⌉ ⊢ ⌈ b ⌉
coe⌈⌉ {a} {b} e = ⌈⌉-E {a = a} {B = ⌈ b ⌉} e

-- THE COMPILER'S CORRECTNESS, as a Hoare triple about program text.
compileTriple : (u : L.Usage) → ⟪ ⌈ [] ⌉ ⟫ compileU u ⟪ ⌈ L.layout u ⌉ ⟫ᵖ
compileTriple u =
  consequenceᵖ (compileU u) idg (coe⌈⌉ (layAt0 u)) (codeTriple u 0 [])

-- ==================================================================
-- COMPILATION AS A TERM OF THE CALCULUS.
--
-- `Obj` is the internal existential over PROGRAM TEXT whose payload is
-- the triple, so a point of `Obj u` is "a program, together with a proof
-- that running it from the empty heap builds `u`'s frame".  `compile` is
-- `⊕ᴰ-I` at the index itself -- `LinLam/Codegen.emit`'s shape with
-- `Heap` replaced by `Program`.
--
-- `L._⊢_` preserves the usage, so a term of this type cannot compile a
-- term at one usage into code for another: the postcondition of the
-- payload is `⌈ layout u ⌉` at the SAME `u` the source term has.  That
-- is the "cannot invent or drop a variable" of `Syntax.agda`, cashed at
-- the level of emitted instructions.
-- ==================================================================

Triple : Program → L.Usage → Type₀
Triple p u = ⟪ ⌈ [] ⌉ ⟫ p ⟪ ⌈ L.layout u ⌉ ⟫ᵖ

Obj : L.Ctx
Obj = L.⊕ᴰ Program Triple

compile : {B : L.Ctx} → B L.⊢ Obj
compile u _ = L.⊕ᴰ-I Program {A = Triple} (compileU u) u (compileTriple u)

-- the compilation of a linear λ-term, as a term of the calculus
compileTm : L.TmG L.⊢ Obj
compileTm = compile

-- ==================================================================
-- NO-ALIASING, AS A POSTCONDITION.
--
-- `layPres appop .homSplit` is the whole content: it turns the context
-- splitting into a DISJOINT heap splitting of `layout u`, and `⊗ˢ-I`
-- packages that as a point of `⌈ layout u₁ ⌉ ∗ ⌈ layout u₂ ⌉`.  `⌈⌉-E`
-- then makes it an entailment, and `consequenceᵖ` a triple.
--
-- Nothing about disjointness is proved here.  It arrived from four
-- modules away as the constructor `Use⊎` does not have.
-- ==================================================================

layJoin : {u₁ u₂ u : L.Usage} → L.Use⊎ u₁ u₂ u
        → (⌈ L.layout u₁ ⌉ ∗ ⌈ L.layout u₂ ⌉) (L.layout u)
layJoin {u₁} {u₂} {u} s =
  ⊗ˢ-I appop {A = boolΠ {M = λ _ → Gr} ⌈ L.layout u₁ ⌉ ⌈ L.layout u₂ ⌉}
       (L.layout u) spl
       (boolΠ {M = λ a → boolΠ {M = λ _ → Gr}
                               ⌈ L.layout u₁ ⌉ ⌈ L.layout u₂ ⌉ a
                               (heapFib .parts appop (L.layout u) spl a)}
              (⌈⌉-pt (L.layout u₁)) (⌈⌉-pt (L.layout u₂)))
  where
  spl : heapFib .Split appop (L.layout u)
  spl = CM.SplitPresAt.homSplit (L.layPres appop) u (u₁ , u₂ , s)

splitPost : {u₁ u₂ u : L.Usage} → L.Use⊎ u₁ u₂ u
          → ⌈ L.layout u ⌉ ⊢ (⌈ L.layout u₁ ⌉ ∗ ⌈ L.layout u₂ ⌉)
splitPost s = ⌈⌉-E (layJoin s)

-- THE HEADLINE.  The code emitted for an application establishes the two
-- premises' frames as SEPARATE regions.
noAlias : {u₁ u₂ u : L.Usage} (s : L.Use⊎ u₁ u₂ u)
        → ⟪ ⌈ [] ⌉ ⟫ compileU u ⟪ ⌈ L.layout u₁ ⌉ ∗ ⌈ L.layout u₂ ⌉ ⟫ᵖ
noAlias {u = u} s =
  consequenceᵖ (compileU u) idg (splitPost s) (compileTriple u)

-- ==================================================================
-- THE FRAME RULE, USED ON THE COMPILER'S OWN OUTPUT.
-- ==================================================================

allocProg : Program
allocProg = newI v1 ∷ []

allocTriple : ⟪ ⌈ [] ⌉ ⟫ allocProg ⟪ ⊕ᴰ Loc (λ l → ⌈ single l v1 ⌉) ⟫ᵖ
allocTriple = instrRule (newI v1) (newAx v1 [])

-- `local-⨟` and `local-skip` are `ISA.Machine`'s; `newLocal` is
-- `ISA.Toy.localAlloc`.  No locality is proved here.
localAllocProg : Local (sem allocProg)
localAllocProg = local-⨟ (liStep (newI v1)) skip (newLocal v1) local-skip

framedAlloc : (R : Gr)
            → ⟪ ⌈ [] ⌉ ∗ R ⟫ allocProg ⟪ (⊕ᴰ Loc λ l → ⌈ single l v1 ⌉) ∗ R ⟫ᵖ
framedAlloc R = frameRule R allocProg localAllocProg allocTriple

-- the unit law of `∗`, as a point plus Yoneda
unitL : (h : Heap) → ⌈ h ⌉ ⊢ (⌈ [] ⌉ ∗ ⌈ h ⌉)
unitL h =
  ⌈⌉-E (⊗ˢ-I appop {A = boolΠ {M = λ _ → Gr} ⌈ [] ⌉ ⌈ h ⌉} h spl
              (boolΠ {M = λ a → boolΠ {M = λ _ → Gr} ⌈ [] ⌉ ⌈ h ⌉ a
                                      (heapFib .parts appop h spl a)}
                     (⌈⌉-pt []) (⌈⌉-pt h)))
  where
  spl : heapFib .Split appop h
  spl = [] , h , ilv-nilL h , tt

-- BUILD THE FRAME, THEN ALLOCATE BESIDE IT.  `seq++` sequences the two
-- programs; `frameRule` says the second leaves `⌈ layout u ⌉` alone.
spill : (u : L.Usage)
      → ⟪ ⌈ [] ⌉ ⟫ compileU u ++ allocProg
        ⟪ (⊕ᴰ Loc λ l → ⌈ single l v1 ⌉) ∗ ⌈ L.layout u ⌉ ⟫ᵖ
spill u =
  seq++ (compileU u) allocProg
    (consequenceᵖ (compileU u) idg (unitL (L.layout u)) (compileTriple u))
    (framedAlloc ⌈ L.layout u ⌉)

-- ==================================================================
-- THE EXECUTABLE FRAGMENT, AND THE EXIT.
-- ==================================================================

-- PRIMITIVE (phase 1): the compiler emits only `putI`.
detCode : (i : ℕ) (u : L.Usage) → Dets (code i u)
detCode i []          = tt
detCode i (true  ∷ u) = tt , detCode (suc i) u
detCode i (false ∷ u) = detCode (suc i) u

-- THE END-TO-END THEOREM.  `observe` is the one exit from the calculus,
-- and this equation is DERIVED from `compileTriple` -- the machine is
-- not run and then compared, it is run inside the triple.
runU : (u : L.Usage) → exec (compileU u) [] Eq.≡ L.layout u
runU u = observe (compileU u) (detCode 0 u) [] (L.layout u) (compileTriple u)

-- ... and at a TERM, where `compileTm u t .fst` is the emitted code
runTm : (u : L.Usage) (t : L.Tm u) → exec (compileTm u t .fst) [] Eq.≡ L.layout u
runTm u t = runU u

-- ==================================================================
-- OBSERVATION.  `refl` lines only, as the house rule says.
-- ==================================================================

-- the code, from a usage
_ : code 0 [] ≡ []
_ = refl

_ : code 0 (true ∷ true ∷ []) ≡ putI 0 v1 ∷ putI 1 v1 ∷ []
_ = refl

-- dead positions emit nothing, and the live ones keep their addresses
_ : code 0 (true ∷ false ∷ true ∷ []) ≡ putI 0 v1 ∷ putI 2 v1 ∷ []
_ = refl

-- CODE EMITTED FROM CLOSED LINEAR TERMS.  `idLin` and `selfApp` are
-- closed, so they allocate nothing -- the compiled program is EMPTY.
_ : compileTm [] L.idLin .fst ≡ []
_ = refl

_ : compileTm [] L.selfApp .fst ≡ []
_ = refl

-- ... and from an open one: `twoVar` is `x y` at two live variables
_ : compileTm (true ∷ true ∷ []) L.twoVar .fst ≡ putI 0 v1 ∷ putI 1 v1 ∷ []
_ = refl

_ : compileTm (true ∷ []) L.xVar .fst ≡ putI 0 v1 ∷ []
_ = refl

-- ==================================================================
-- THE MACHINE ACTUALLY RUNS.  `exec` on the emitted code, from the
-- empty heap, is the layout -- and this is a `refl`, i.e. the whole
-- chain (term ↦ usage ↦ instructions ↦ heap) reduces.
-- ==================================================================

_ : exec (compileTm (true ∷ true ∷ []) L.twoVar .fst) [] ≡ (0 , v1) ∷ (1 , v1) ∷ []
_ = refl

_ : exec (compileTm (true ∷ true ∷ []) L.twoVar .fst) []
  ≡ L.layout (true ∷ true ∷ [])
_ = refl

-- a term over a scope of THREE with the middle variable dead: the
-- emitted code skips position 1, and the two live cells keep their
-- own addresses
gapSplit : L.Use⊎ (true ∷ false ∷ false ∷ []) (false ∷ false ∷ true ∷ [])
                  (true ∷ false ∷ true ∷ [])
gapSplit = L.uleft (L.uskip (L.uright L.unil))

gapTm : L.Tm (true ∷ false ∷ true ∷ [])
gapTm = L.tapp gapSplit (L.tvar tt) (L.tvar tt)

_ : exec (compileTm (true ∷ false ∷ true ∷ []) gapTm .fst) []
  ≡ (0 , v1) ∷ (2 , v1) ∷ []
_ = refl

-- a closed term compiles to the empty program, which runs to the empty heap
_ : exec (compileTm [] L.selfApp .fst) [] ≡ []
_ = refl

-- ==================================================================
-- ... AND THE DERIVED EQUATION REDUCES TOO.  `runU` is the triple
-- applied to `exec-sound`; that it is `Eq.refl` on the nose says the
-- Hoare proof is not merely inhabited but COMPUTES.
-- ==================================================================

_ : runU (true ∷ true ∷ []) ≡ Eq.refl
_ = refl

_ : runTm (true ∷ true ∷ []) L.twoVar ≡ Eq.refl
_ = refl

-- ==================================================================
-- THE NO-ALIASING SPLIT, EVALUATED.  The splitting `layPres` hands the
-- postcondition of `noAlias` at `twoVar`'s application: two singleton
-- regions, and a `_#_` proof that is a nest of `tt`.
-- ==================================================================

_ : layJoin L.twoSplit .fst
  ≡ ( single 0 v1 , single 1 v1 , left (right nil) , ((tt , tt) , tt) )
_ = refl

-- ... AND THE SAME SPLIT READ OFF THE HEAP THE MACHINE ACTUALLY
-- PRODUCED.  `noAliasRun` runs the compiled code (via `exec-sound`) and
-- returns the postcondition AT THE RESULTING HEAP, so its first
-- component is a disjoint decomposition of a heap that was computed by
-- `exec`, not one that was assumed.
noAliasRun : {u₁ u₂ u : L.Usage} → L.Use⊎ u₁ u₂ u
           → (⌈ L.layout u₁ ⌉ ∗ ⌈ L.layout u₂ ⌉) (exec (compileU u) [])
noAliasRun {u = u} s =
  noAlias s [] (⌈⌉-pt []) (exec (compileU u) [])
          (exec-sound (compileU u) (detCode 0 u) [])

_ : noAliasRun L.twoSplit .fst
  ≡ ( single 0 v1 , single 1 v1 , left (right nil) , ((tt , tt) , tt) )
_ = refl
