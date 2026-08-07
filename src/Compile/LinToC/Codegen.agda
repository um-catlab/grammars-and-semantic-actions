{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE C BACKEND: FROM LINEAR CONTEXTS TO C DECLARATIONS, AND THE HOARE
  TRIPLE THAT SAYS THE EMITTED SOURCE IS RIGHT.

  This is the C sibling of `Compile.LinToISA.Codegen`, and it is built to
  the SAME specification, deliberately:

      evalC (compileC u) []  Eq.≡  LinLam.Codegen.layout u

  The assembly backend proves `exec (compileU u) [] Eq.≡ layout u`; a
  Rust backend proves the same equation with its own evaluator.  Three
  backends, one observable (`Heap` from `Instances/Heap/Base`), one
  right-hand side.  Relational equivalence of the three is then a
  composition of equations and needs no new argument.

  ------------------------------------------------------------------
  WHAT IS COMPILED, AND WHY IT DEPENDS ONLY ON THE USAGE
  ------------------------------------------------------------------

  A linear term's FRAME is `layout u`: one object per live variable, at
  the variable's own position.  The C that builds it is

      code i []          = []
      code i (true  ∷ u) = cdecl i v1 ∷ code (suc i) u
      code i (false ∷ u) = code (suc i) u

  -- one declaration per live position, in increasing address order.  The
  recursion is on the USAGE, not on the term, exactly as
  `LinLam/Codegen.emit` and `LinToISA.Codegen.code` are: a binder SHIFTS
  every address by one (`layout (true ∷ u)` is `(0,v1) ∷ lay 1 u`), so a
  term-directed compilation would renumber at every `tlam`, whereas the
  usage-directed one addresses the whole scope once.

  Printed (`Compile.LinToC.Print`), `code 0 (true ∷ false ∷ true ∷ [])` is

      val_t x0 = V1;
      val_t x2 = V1;

  -- the dead middle position leaves a GAP in the numbering, and that gap
  is `lay`'s "positions are addresses" showing up in real source text.

  ------------------------------------------------------------------
  THE TRIPLE, AND WHAT IT COST
  ------------------------------------------------------------------

      codeTriple : ⟪ ⌈ h ⌉ ⟫ code i u ⟪ ⌈ layAt h i u ⌉ ⟫ᵖ

  Three clauses.  `[]` is `emptyRule`; `false` is the induction
  hypothesis unchanged; `true` is `seq∷` of `instrRule (declAx …)` with
  the hypothesis.  Every name in it comes from `ISA.Program`, which got
  them from `ISA.Interp`, which proved them once for every instruction
  set and every resource model.  The accounting, in the form
  `ISA.Program` states it:

      Hoare sequencing proved in this file:        0
      Hoare framing proved in this file:           0
      inductions over a program in this file:      0
      inductions over a USAGE in this file:        4   (`codeTriple`,
                                                        `layAt ≡ lay`,
                                                        `detCode`,
                                                        `layWF`)

  ------------------------------------------------------------------
  NO-ALIASING: WHERE IT COMES FROM, AND WHERE IT CANNOT COME FROM
  ------------------------------------------------------------------

  This is the reason to build a C backend beside the Rust one.

  A Rust backend is sound partly because the TARGET refuses the bad
  programs: affine ownership matches the source's linearity, so two
  premises of an application cannot be handed the same place.  C refuses
  nothing.  `Machine.noOwnership` proves that a declaration and a store
  through an alias have the SAME denotation, so no invariant of a C
  program's meaning can say "this write owns its object".

  So the disjointness has to be a theorem about the COMPILER, and it is,
  in two forms:

    (1) AS A HOARE POSTCONDITION, exactly as in the ISA backend:

            noAliasC : Use⊎ u₁ u₂ u
                     → ⟪ ⌈ [] ⌉ ⟫ compileC u
                       ⟪ ⌈ layout u₁ ⌉ ∗ ⌈ layout u₂ ⌉ ⟫ᵖ

        `∗` is `⊗ˢ appop` at `heapFib`, so its very inhabitation carries
        the `_#_` conjunct.  The term that provides it is `⌈⌉-E (layJoin
        s)` and `layJoin` is `⊗ˢ-I` at

            LinLam/Codegen.layPres appop .homSplit

        -- so the disjointness is not established here.  It is
        `LinLam/Codegen`'s SPLIT PRESERVATION, transported across Yoneda.
        `layPres` is the theorem doing the work, and what it turns on is
        the constructor `Use⊎` does NOT have: there is no clause taking
        `true` on both sides, so no two premises reach the same position,
        so no two emitted declarations name the same object.  (`layRefl`
        gives the converse, so splittings correspond BIJECTIVELY -- the
        layout is a strong monoidal functor from linear contexts to
        separation logic.)

    (2) AS A PROPERTY OF THE EMITTED SOURCE TEXT:

            emittedNoAlias : (u : Usage) → NoAlias (compileC u)

        where `NoAlias p = WF (evalC p [])` and `WF` says every location
        is named once.  This is the statement a C programmer would want:
        the generated file declares pairwise-distinct objects.  It is
        proved by transporting `layWF` -- "a layout never repeats an
        address", which is `LinLam/Codegen.freshLay` -- along the
        headline equation `runC`.

  And the counterweight, which is the honest half:

            noSourceForAlias : (u : Usage)
                             → evalC Machine.aliasC [] Eq.≡ layout u → ⊥

  `aliasC` is a perfectly ordinary program of the fragment -- it
  typechecks as C, it runs, `Print` prints it -- and it is the
  compilation of NO source term at any usage.  Nothing in C rules it out;
  only the compiler does.  In Rust the corresponding program is rejected
  by the target's own type system, and that is precisely the difference
  between the two backends.

  ------------------------------------------------------------------
  THE FRAME RULE, USED
  ------------------------------------------------------------------

  `spill` mallocs a scratch cell after the frame is built and states that
  the variables' objects are untouched.  It is `cmalloc` and not `cdecl`
  that appears, and `Machine.noDeclLocal` says why it has to be: a
  statement that NAMES its address is not `Local`.

  ------------------------------------------------------------------
  END TO END
  ------------------------------------------------------------------

  `Machine.observe` turns a triple between representables into an
  equation about the FUNCTION `evalC`.  It is the only exit from the
  calculus and appears in exactly one definition, `runC`.  The `refl`
  block at the bottom evaluates the whole chain -- term ↦ usage ↦ C
  statements ↦ C SOURCE TEXT ↦ heap -- and the last of those is a string
  literal you could paste into a file and compile.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1, all marked: `code`, `layAt`, `codeTriple`, `detCode`, `layWF`
  and the two `++h` lemmas -- recursions on a usage or a heap, which is
  what building a pass is allowed to do.  Everything from `compileTriple`
  down is a composite of `seq∷`, `seq++`, `instrRule`, `emptyRule`,
  `consequenceᵖ`, `frameRule`, `⌈⌉-E`, `⌈⌉-pt`, `⊗ˢ-I`, `⊕ᴰ-I`, `boolΠ`
  and `idg`.
-}
open import Cubical.Foundations.Prelude

module Compile.LinToC.Codegen where

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
open import Compile.LinToC.Machine public
open import Compile.LinToC.Print public

-- the SOURCE, qualified -- `LinLam/Codegen` re-exports the linear
-- context promodel's own `⊢`, `⊗ˢ`, `⌈⌉`, `boolΠ`, ... and the two
-- theories' combinators must not collide.
import TheoryGrammar.Instances.LinLam.Codegen as L

-- ==================================================================
-- THE EMITTED C.  PRIMITIVE (phase 1): recursion on the usage, in
-- lockstep with `lay`.
-- ==================================================================

code : ℕ → L.Usage → CProg
code i []          = []
code i (true  ∷ u) = cdecl i v1 ∷ code (suc i) u
code i (false ∷ u) = code (suc i) u

compileC : L.Usage → CProg
compileC = code 0

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
-- Every name on the right-hand side is from `ISA.Program`.  This file
-- contributes the induction on the usage and nothing else.
-- ==================================================================

-- PRIMITIVE (phase 1): the recursion is on `u`, exactly as `code`'s is.
codeTriple : (u : L.Usage) (i : ℕ) (h : Heap)
           → ⟪ ⌈ h ⌉ ⟫ code i u ⟪ ⌈ layAt h i u ⌉ ⟫ᵖ
codeTriple []          i h = emptyRule ⌈ h ⌉
codeTriple (true  ∷ u) i h =
  seq∷ (cdecl i v1) (code (suc i) u)
       (instrRule (cdecl i v1) (declAx i v1 h))
       (codeTriple u (suc i) (h ++h single i v1))
codeTriple (false ∷ u) i h = codeTriple u (suc i) h

-- ==================================================================
-- ... AND ITS POSTCONDITION IS `LinLam/Codegen`'s LAYOUT.
--
-- Two `++h` lemmas, both the monoid laws of the free monoid on cells.
-- `eqTrans` is `ISA.Machine`'s.
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

-- THE COMPILER'S CORRECTNESS, as a Hoare triple about C source text.
compileTriple : (u : L.Usage) → ⟪ ⌈ [] ⌉ ⟫ compileC u ⟪ ⌈ L.layout u ⌉ ⟫ᵖ
compileTriple u =
  consequenceᵖ (compileC u) idg (coe⌈⌉ (layAt0 u)) (codeTriple u 0 [])

-- ==================================================================
-- COMPILATION AS A TERM OF THE CALCULUS.
--
-- `Obj` is the internal existential over C PROGRAM TEXT whose payload is
-- the triple, so a point of `Obj u` is "a C program, together with a
-- proof that running it from the empty heap builds `u`'s frame".
-- `compile` is `⊕ᴰ-I` at the index itself -- `LinLam/Codegen.emit`'s
-- shape with `Heap` replaced by `CProg`.
--
-- `L._⊢_` preserves the usage, so a term of this type CANNOT compile a
-- term at one usage into C for another: the postcondition of the payload
-- is `⌈ layout u ⌉` at the SAME `u` the source term has.  That is
-- `Syntax.agda`'s "cannot invent or drop a variable", cashed at the level
-- of emitted declarations.
--
-- Note that no `String` occurs in any of these types.  Rendering happens
-- in a `refl` line, never in a definition.
-- ==================================================================

Triple : CProg → L.Usage → Type₀
Triple p u = ⟪ ⌈ [] ⌉ ⟫ p ⟪ ⌈ L.layout u ⌉ ⟫ᵖ

Obj : L.Ctx
Obj = L.⊕ᴰ CProg Triple

compile : {B : L.Ctx} → B L.⊢ Obj
compile u _ = L.⊕ᴰ-I CProg {A = Triple} (compileC u) u (compileTriple u)

-- the compilation of a linear λ-term to C, as a term of the calculus
compileTm : L.TmG L.⊢ Obj
compileTm = compile

-- ==================================================================
-- NO-ALIASING (1): AS A POSTCONDITION.
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

-- THE HEADLINE OF THE NO-ALIASING HALF.  The C emitted for an
-- application establishes the two premises' frames as SEPARATE regions.
noAliasC : {u₁ u₂ u : L.Usage} (s : L.Use⊎ u₁ u₂ u)
         → ⟪ ⌈ [] ⌉ ⟫ compileC u ⟪ ⌈ L.layout u₁ ⌉ ∗ ⌈ L.layout u₂ ⌉ ⟫ᵖ
noAliasC {u = u} s =
  consequenceᵖ (compileC u) idg (splitPost s) (compileTriple u)

-- ==================================================================
-- THE FRAME RULE, USED ON THE COMPILER'S OWN OUTPUT.
--
-- `cmalloc` and not `cdecl`, because `Machine.noDeclLocal` says a
-- statement that names its address is not `Local`.
-- ==================================================================

mallocProg : CProg
mallocProg = cmalloc v1 ∷ []

mallocTriple : ⟪ ⌈ [] ⌉ ⟫ mallocProg ⟪ ⊕ᴰ Loc (λ l → ⌈ single l v1 ⌉) ⟫ᵖ
mallocTriple = instrRule (cmalloc v1) (mallocAx v1 [])

-- `local-⨟` and `local-skip` are `ISA.Machine`'s; `mallocLocal` is
-- `ISA.Toy.localAlloc`.  No locality is proved here.
localMallocProg : Local (sem mallocProg)
localMallocProg =
  local-⨟ (cStep (cmalloc v1)) skip (mallocLocal v1) local-skip

framedMalloc : (R : Gr)
             → ⟪ ⌈ [] ⌉ ∗ R ⟫ mallocProg
               ⟪ (⊕ᴰ Loc λ l → ⌈ single l v1 ⌉) ∗ R ⟫ᵖ
framedMalloc R = frameRule R mallocProg localMallocProg mallocTriple

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

-- DECLARE THE FRAME, THEN MALLOC BESIDE IT.  `seq++` sequences the two
-- programs; `frameRule` says the second leaves `⌈ layout u ⌉` alone.
spill : (u : L.Usage)
      → ⟪ ⌈ [] ⌉ ⟫ compileC u ++ mallocProg
        ⟪ (⊕ᴰ Loc λ l → ⌈ single l v1 ⌉) ∗ ⌈ L.layout u ⌉ ⟫ᵖ
spill u =
  seq++ (compileC u) mallocProg
    (consequenceᵖ (compileC u) idg (unitL (L.layout u)) (compileTriple u))
    (framedMalloc ⌈ L.layout u ⌉)

-- ==================================================================
-- THE EXECUTABLE FRAGMENT, AND THE EXIT.
-- ==================================================================

-- PRIMITIVE (phase 1): the compiler emits only `cdecl`.
detCode : (i : ℕ) (u : L.Usage) → Dets (code i u)
detCode i []          = tt
detCode i (true  ∷ u) = tt , detCode (suc i) u
detCode i (false ∷ u) = detCode (suc i) u

-- ==================================================================
-- THE HEADLINE THEOREM.
--
--     evalC (compileC u) []  Eq.≡  layout u
--
-- `observe` is the one exit from the calculus, and this equation is
-- DERIVED from `compileTriple` -- the C is not run and then compared, it
-- is run inside the triple.  The ISA backend's `runU` and the Rust
-- backend's evaluator prove the same statement with the same right-hand
-- side, so the three agree by composition.
-- ==================================================================

runC : (u : L.Usage) → evalC (compileC u) [] Eq.≡ L.layout u
runC u = observe (compileC u) (detCode 0 u) [] (L.layout u) (compileTriple u)

-- ... and at a TERM, where `compileTm u t .fst` is the emitted C
runTm : (u : L.Usage) (t : L.Tm u)
      → evalC (compileTm u t .fst) [] Eq.≡ L.layout u
runTm u t = runC u

-- ==================================================================
-- NO-ALIASING (2): AS A PROPERTY OF THE EMITTED SOURCE TEXT.
--
-- `layWF` is "a layout never repeats an address", and its only content
-- is `LinLam/Codegen.freshLay` -- everything `lay i u` allocates sits at
-- a location ≥ i.  Transporting it along the headline equation gives the
-- statement a C programmer would want: the generated translation unit
-- declares pairwise-distinct objects.
--
-- PRIMITIVE (phase 1): recursion on the usage.
-- ==================================================================

layWF : (u : L.Usage) (i : ℕ) → WF (L.lay i u)
layWF []          i = tt
layWF (true  ∷ u) i = L.freshLay u (suc i) i (L.below-suc i) , layWF u (suc i)
layWF (false ∷ u) i = layWF u (suc i)

-- THE EMITTED C DOES NOT ALIAS.
emittedNoAlias : (u : L.Usage) → NoAlias (compileC u)
emittedNoAlias u = coeWF (runC u) (layWF u 0)

-- ... and at a term
emittedNoAliasTm : (u : L.Usage) (t : L.Tm u) → NoAlias (compileTm u t .fst)
emittedNoAliasTm u t = emittedNoAlias u

-- ==================================================================
-- ... AND THE COUNTERWEIGHT: THE TARGET DOES NOT GIVE YOU THIS.
--
-- `Machine.aliasC` is a program of the fragment which C accepts, runs,
-- and cannot object to -- `Machine.noOwnership` says its second
-- statement is indistinguishable from a declaration.  It is the
-- compilation of NO source term at ANY usage, and the proof is the
-- contrapositive of `layWF`.
--
-- In Rust the analogous program does not typecheck: the property lives
-- in the TARGET.  Here it lives in the MAP, and this pair of theorems is
-- exactly the difference.
-- ==================================================================

noSourceForAlias : (u : L.Usage) → evalC aliasC [] Eq.≡ L.layout u → ⊥
noSourceForAlias u e = aliasNotWF (coeWF e (layWF u 0))

-- ==================================================================
-- OBSERVATION.  `refl` lines only, as the house rule says.
-- ==================================================================

-- the C, from a usage
_ : code 0 [] ≡ []
_ = refl

_ : code 0 (true ∷ true ∷ []) ≡ cdecl 0 v1 ∷ cdecl 1 v1 ∷ []
_ = refl

-- dead positions emit nothing, and the live ones keep their addresses
_ : code 0 (true ∷ false ∷ true ∷ []) ≡ cdecl 0 v1 ∷ cdecl 2 v1 ∷ []
_ = refl

-- C EMITTED FROM CLOSED LINEAR TERMS.  `idLin` and `selfApp` are closed,
-- so they declare nothing -- the compiled program is EMPTY.
_ : compileTm [] L.idLin .fst ≡ []
_ = refl

_ : compileTm [] L.selfApp .fst ≡ []
_ = refl

-- ... and from open ones
_ : compileTm (true ∷ true ∷ []) L.twoVar .fst ≡ cdecl 0 v1 ∷ cdecl 1 v1 ∷ []
_ = refl

_ : compileTm (true ∷ []) L.xVar .fst ≡ cdecl 0 v1 ∷ []
_ = refl

-- ==================================================================
-- REAL C SOURCE TEXT.  This is the point of the printer: the string
-- below is a complete C99 translation unit, produced from a linear
-- λ-term, and the equation is `refl`.
-- ==================================================================

-- a closed term: an empty function body
_ : emitUnit (compileTm [] L.idLin .fst)
  ≡ "#include <stdlib.h>\n\ntypedef enum { V0, V1, V2 } val_t;\nstatic val_t mem[64];\n\nvoid frame(void) {\n}\n"
_ = refl

-- two live variables
_ : emitUnit (compileTm (true ∷ true ∷ []) L.twoVar .fst)
  ≡ "#include <stdlib.h>\n\ntypedef enum { V0, V1, V2 } val_t;\nstatic val_t mem[64];\n\nvoid frame(void) {\n  val_t x0 = V1;\n  val_t x1 = V1;\n}\n"
_ = refl

-- ... and the body alone, which is easier to read
_ : body (compileTm (true ∷ true ∷ []) L.twoVar .fst)
  ≡ "  val_t x0 = V1;\n  val_t x1 = V1;\n"
_ = refl

-- ==================================================================
-- THE MACHINE ACTUALLY RUNS.  `evalC` on the emitted C, from the empty
-- heap, is the layout -- and this is a `refl`, i.e. the whole chain
-- (term ↦ usage ↦ C statements ↦ heap) reduces.
-- ==================================================================

_ : evalC (compileTm (true ∷ true ∷ []) L.twoVar .fst) []
  ≡ (0 , v1) ∷ (1 , v1) ∷ []
_ = refl

_ : evalC (compileTm (true ∷ true ∷ []) L.twoVar .fst) []
  ≡ L.layout (true ∷ true ∷ [])
_ = refl

-- a closed term compiles to the empty program, which runs to the empty heap
_ : evalC (compileTm [] L.selfApp .fst) [] ≡ []
_ = refl

-- ==================================================================
-- A SCOPE OF THREE WITH THE MIDDLE VARIABLE DEAD.  The emitted C skips
-- position 1, the two live objects keep their own addresses, and the GAP
-- is visible in the source text: there is no `x1`.
-- ==================================================================

gapSplit : L.Use⊎ (true ∷ false ∷ false ∷ []) (false ∷ false ∷ true ∷ [])
                  (true ∷ false ∷ true ∷ [])
gapSplit = L.uleft (L.uskip (L.uright L.unil))

gapTm : L.Tm (true ∷ false ∷ true ∷ [])
gapTm = L.tapp gapSplit (L.tvar tt) (L.tvar tt)

_ : compileTm (true ∷ false ∷ true ∷ []) gapTm .fst
  ≡ cdecl 0 v1 ∷ cdecl 2 v1 ∷ []
_ = refl

_ : body (compileTm (true ∷ false ∷ true ∷ []) gapTm .fst)
  ≡ "  val_t x0 = V1;\n  val_t x2 = V1;\n"
_ = refl

_ : evalC (compileTm (true ∷ false ∷ true ∷ []) gapTm .fst) []
  ≡ (0 , v1) ∷ (2 , v1) ∷ []
_ = refl

-- ==================================================================
-- ... AND THE DERIVED EQUATION REDUCES TOO.  `runC` is the triple
-- applied to `evalC-sound`; that it is `Eq.refl` on the nose says the
-- Hoare proof is not merely inhabited but COMPUTES.
-- ==================================================================

_ : runC (true ∷ true ∷ []) ≡ Eq.refl
_ = refl

_ : runTm (true ∷ true ∷ []) L.twoVar ≡ Eq.refl
_ = refl

_ : runC (true ∷ false ∷ true ∷ []) ≡ Eq.refl
_ = refl

-- ==================================================================
-- THE NO-ALIASING SPLIT, EVALUATED.  The splitting `layPres` hands the
-- postcondition of `noAliasC` at `twoVar`'s application: two singleton
-- regions, and a `_#_` proof that is a nest of `tt`.
-- ==================================================================

_ : layJoin L.twoSplit .fst
  ≡ ( single 0 v1 , single 1 v1 , left (right nil) , ((tt , tt) , tt) )
_ = refl

-- ... AND THE SAME SPLIT READ OFF THE HEAP THE EMITTED C ACTUALLY
-- PRODUCED.  `noAliasRun` runs the compiled program (via `evalC-sound`)
-- and returns the postcondition AT THE RESULTING HEAP, so its first
-- component is a disjoint decomposition of a heap that was COMPUTED by
-- `evalC`, not one that was assumed.
noAliasRun : {u₁ u₂ u : L.Usage} → L.Use⊎ u₁ u₂ u
           → (⌈ L.layout u₁ ⌉ ∗ ⌈ L.layout u₂ ⌉) (evalC (compileC u) [])
noAliasRun {u = u} s =
  noAliasC s [] (⌈⌉-pt []) (evalC (compileC u) [])
           (evalC-sound (compileC u) (detCode 0 u) [])

_ : noAliasRun L.twoSplit .fst
  ≡ ( single 0 v1 , single 1 v1 , left (right nil) , ((tt , tt) , tt) )
_ = refl

-- the alias-freedom of the emitted text, evaluated: a nest of `tt`
_ : emittedNoAlias (true ∷ false ∷ true ∷ []) ≡ ((tt , tt) , (tt , tt))
_ = refl
