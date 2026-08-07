{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE RUST BACKEND: FROM A LINEAR λ-TERM TO RUST SOURCE TEXT, AND THE
  HOARE TRIPLE THAT SAYS THE TEXT IS RIGHT.

  ------------------------------------------------------------------
  THE SHARED SPECIFICATION
  ------------------------------------------------------------------

  Three backends are being built against one specification, so that
  their agreement is a composition and not a negotiation:

      SOURCE      `TheoryGrammar.Instances.LinLam.Syntax`'s `TmG`, at a
                  `Usage`
      OBSERVABLE  `TheoryGrammar.Instances.Heap.Base.Heap`
      THE SPEC    evaluating the compiled output from the empty heap
                  yields `LinLam.Codegen.layout u`

  and the headline of this file is exactly that, for Rust:

      runRust : (u : Usage) → evalRust (compileRust u) [] Eq.≡ L.layout u

  `Compile.LinToISA.Codegen.runU` is the same statement for a three-
  instruction ISA; a sibling agent is proving it for C.  Nothing here
  invents an observable, and nothing here weakens the spec.

  ------------------------------------------------------------------
  WHY RUST IS A SOUND TARGET, IN ONE LINE
  ------------------------------------------------------------------

  `Box::new` is an OWNING allocation and Rust's ownership discipline is
  AFFINE.  `TheoryGrammar.Instances.Affine.Contrast` proves
  `linTm→aff : Tm u → ATm u` -- every LINEAR term is an affine term at
  the SAME usage -- and `lin⊊aff` proves the inclusion strict, the
  witness being `adrop`, the splitting in which the whole owns a
  variable and neither premise claims it.  So:

      linear ⊂ affine, and the extra affine constructor is exactly the
      one that would force a `drop`.

  Hence in this fragment no value is ever dropped, no box is ever
  cloned, and nothing is ever borrowed.  The emitted Rust needs none of
  those constructs, and that is a theorem about the source language, not
  a convenience of the printer.  `Machine`'s header spells this out
  alongside the list of what the model deliberately omits (`if`,
  `while`, borrows, lifetimes, `drop`, every type but `Box<u8>`).

  ------------------------------------------------------------------
  WHAT IS COMPILED, AND WHY IT DEPENDS ONLY ON THE USAGE
  ------------------------------------------------------------------

  A linear term's FRAME is `layout u`: one owned box per live variable,
  at the variable's own position.  The code that builds it is

      code i []          = []
      code i (true  ∷ u) = letS i v1 ∷ code (suc i) u
      code i (false ∷ u) = code (suc i) u

  -- one `let xI: Box<u8> = Box::new(1u8);` per live position, in
  increasing address order.  The recursion is on the USAGE, not on the
  term: `layout` already told us that a binder SHIFTS every address by
  one, so a term-directed compilation would renumber at every `tlam`,
  whereas the usage-directed one addresses the whole scope once.

  ------------------------------------------------------------------
  THE TRIPLE, AND WHAT IT COST
  ------------------------------------------------------------------

      codeTriple : ⟪ ⌈ h ⌉ ⟫ code i u ⟪ ⌈ layAt h i u ⌉ ⟫ᵖ

  Three clauses.  The `[]` clause is `emptyRule`; the `false` clause is
  the induction hypothesis unchanged; the `true` clause is `seq∷`
  applied to `instrRule (letS i v1) (letAx i v1 h)` and the hypothesis.
  Every name in it comes from `ISA.Program`, which got them from
  `ISA.Interp` for every statement set at once.  The accounting, in the
  form `ISA.Program` and `LinToISA/Codegen` state it:

      Hoare sequencing proved in this file:        0
      Hoare framing proved in this file:           0
      Hoare consequence proved in this file:       0
      locality proved in this file:                0
      inductions over a program in this file:      0
      inductions over a USAGE in this file:        3   (`code`'s triple,
                                                        `layAt ≡ lay`,
                                                        `AllPlaced`)

  ------------------------------------------------------------------
  COMPILATION IS A TERM OF THE CALCULUS
  ------------------------------------------------------------------

      compileTm : L.TmG L.⊢ Obj,     Obj = ⊕ᴰ RustProg Triple

  `L._⊢_` PRESERVES THE USAGE, so a term of this type cannot compile a
  source term at one usage into Rust for another: the postcondition
  inside `Obj` is `⌈ layout u ⌉` at the SAME `u` the source term has.
  That is where the linearity guarantee lives -- "cannot invent or drop
  a variable", cashed at the level of emitted `let` bindings.

  ------------------------------------------------------------------
  THE SOURCE TEXT, EXTERNALISED LATE
  ------------------------------------------------------------------

  No producer in this file mentions `String` in its type.  The
  text-level producer is

      srcTm : L.TmG L.⊢ Δ String
      srcTm = Δ-map renderProg ∘g progA ∘g compileTm

  -- `Δ` is `TheoryGrammar.SemanticAction`'s discrete type, `progA` is
  `⊕ᴰ-E` reading the program out of `Obj`, and `renderProg` (phase 1,
  `Emit`) is applied INSIDE `Δ-map`, i.e. as a semantic action rather
  than as an exit.  The only exit is `runAt`, and it occurs solely in
  the `refl` block at the bottom, where the emitted Rust is quoted as a
  literal.

  ------------------------------------------------------------------
  NO-ALIASING, AND THE FRAME RULE ON REAL `Box::new`
  ------------------------------------------------------------------

  `noAlias` is the postcondition `⌈ layout u₁ ⌉ ∗ ⌈ layout u₂ ⌉`, whose
  very inhabitation carries the `_#_` conjunct: the two premises of an
  application own DISJOINT boxes.  It is `LinLam/Codegen.layPres`
  transported across `⌈⌉-E`; nothing about disjointness is proved here.

  `spill` builds the frame and then performs a genuine allocator-chosen
  `Box::new` beside it, with the variables' boxes as the FRAME.  It is
  `boxS` and not `letS` that appears there, and `Machine.noLetLocal`
  says why it has to be: a `Box` is framable precisely because the
  program does not choose its address.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1, all marked: `code`, `layAt`, `codeTriple`, `placedCode` and
  the two `++h` lemmas -- recursions on a usage or on a heap, i.e. on a
  carrier, which is what building a pass is allowed to do.  Everything
  from `compileTriple` down is a composite of `seq∷`, `seq++`,
  `instrRule`, `emptyRule`, `consequenceᵖ`, `frameRule`, `⌈⌉-E`,
  `⌈⌉-pt`, `⊗ˢ-I`, `⊕ᴰ-I`, `⊕ᴰ-E`, `Δ-map`, `boolΠ` and `idg`.
-}
open import Cubical.Foundations.Prelude

module Compile.LinToRust.Alloc.Codegen where

open import Agda.Builtin.String using (String)
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
import TheoryGrammar.SemanticAction as SA

-- the TARGET, unqualified: the Hoare layer is what most of this file
-- speaks
open import Compile.LinToRust.Alloc.Machine public
open import Compile.LinToRust.Alloc.Emit public

-- the SOURCE, qualified -- `LinLam/Codegen` re-exports the linear
-- context promodel's own `⊢`, `⊗ˢ`, `⌈⌉`, `boolΠ`, ... and the two
-- theories' combinators must not collide.
import TheoryGrammar.Instances.LinLam.Codegen as L

-- the discrete type at the SOURCE theory: `Δ X u = X × Unit*`, a
-- payload that does not depend on the usage.  This is how a `String`
-- gets to be the codomain of a `⊢` without appearing in one.
module LA = SA.Act {σ = monoidSig} (L.linFib .carrier)
open LA using (Δ)

-- ==================================================================
-- THE EMITTED CODE.  PRIMITIVE (phase 1): recursion on the usage, in
-- lockstep with `lay`.
-- ==================================================================

code : ℕ → L.Usage → RustProg
code i []          = []
code i (true  ∷ u) = letS i v1 ∷ code (suc i) u
code i (false ∷ u) = code (suc i) u

compileRust : L.Usage → RustProg
compileRust = code 0

-- PRIMITIVE (phase 1): the heap the code builds, written with the SAME
-- recursion so that the triple's induction is definitional at every
-- clause.  `layAt≡` below identifies it with `h ++h lay i u`.
layAt : Heap → ℕ → L.Usage → Heap
layAt h i []          = h
layAt h i (true  ∷ u) = layAt (h ++h single i v1) (suc i) u
layAt h i (false ∷ u) = layAt h (suc i) u

-- ==================================================================
-- THE TRIPLE.  This file contributes the induction on the usage and
-- nothing else; every combinator is `ISA.Program`'s.
-- ==================================================================

-- PRIMITIVE (phase 1): the recursion is on `u`, exactly as `code`'s is.
codeTriple : (u : L.Usage) (i : ℕ) (h : Heap)
           → ⟪ ⌈ h ⌉ ⟫ code i u ⟪ ⌈ layAt h i u ⌉ ⟫ᵖ
codeTriple []          i h = emptyRule ⌈ h ⌉
codeTriple (true  ∷ u) i h =
  seq∷ (letS i v1) (code (suc i) u)
       (instrRule (letS i v1) (letAx i v1 h))
       (codeTriple u (suc i) (h ++h single i v1))
codeTriple (false ∷ u) i h = codeTriple u (suc i) h

-- ==================================================================
-- ... AND ITS POSTCONDITION IS `LinLam/Codegen`'s LAYOUT.
-- Two `++h` lemmas, both monoid laws of the free monoid on cells.
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
-- itself, since `⌈ b ⌉ a` IS `a Eq.≡ b`.  Yoneda.
coe⌈⌉ : {a b : Heap} → a Eq.≡ b → ⌈ a ⌉ ⊢ ⌈ b ⌉
coe⌈⌉ {a} {b} e = ⌈⌉-E {a = a} {B = ⌈ b ⌉} e

-- THE COMPILER'S CORRECTNESS, as a Hoare triple about Rust text.
compileTriple : (u : L.Usage) → ⟪ ⌈ [] ⌉ ⟫ compileRust u ⟪ ⌈ L.layout u ⌉ ⟫ᵖ
compileTriple u =
  consequenceᵖ (compileRust u) idg (coe⌈⌉ (layAt0 u)) (codeTriple u 0 [])

-- ==================================================================
-- COMPILATION AS A TERM OF THE CALCULUS.
--
-- A point of `Obj u` is "a Rust program, together with a proof that
-- running it from the empty heap builds `u`'s frame".  `compile` is
-- `⊕ᴰ-I` at the index itself -- `LinLam/Codegen.emit`'s shape with
-- `Heap` replaced by `RustProg`.
--
-- `L._⊢_` preserves the usage, so this type FORBIDS compiling a term
-- at one usage into Rust for another.
-- ==================================================================

Triple : RustProg → L.Usage → Type₀
Triple p u = ⟪ ⌈ [] ⌉ ⟫ p ⟪ ⌈ L.layout u ⌉ ⟫ᵖ

Obj : L.Ctx
Obj = L.⊕ᴰ RustProg Triple

compile : {B : L.Ctx} → B L.⊢ Obj
compile u _ = L.⊕ᴰ-I RustProg {A = Triple} (compileRust u) u (compileTriple u)

-- the compilation of a linear λ-term, as a term of the calculus
compileTm : L.TmG L.⊢ Obj
compileTm = compile

-- ==================================================================
-- THE SOURCE TEXT, AS A `⊢`-TERM INTO `Δ String`.
--
-- `progA` forgets the proof (`⊕ᴰ-E` into the discrete type), `Δ-map`
-- applies the printer as a SEMANTIC ACTION.  No producer in this file
-- has `String` in its type, and `renderProg` never appears outside a
-- `Δ-map`.
-- ==================================================================

progA : LA.Action Obj RustProg
progA = L.⊕ᴰ-E {Y = RustProg} {A = Triple} (λ p → LA.pureA RustProg p)

srcTm : L.TmG L.⊢ Δ String
srcTm = LA.Δ-map renderProg L.∘g progA L.∘g compileTm

-- THE EXIT.  `SemanticAction.run` is `⊤G ⊢ Δ X → Car s → X`; a producer
-- whose domain is a nonempty grammar exits at a POINT of that grammar
-- instead, which is the same projection.  Used only in `refl` lines.
runAt : {X : Type₀} {A : L.Ctx} → A L.⊢ Δ X → (u : L.Usage) → A u → X
runAt f u a = f u a .fst

-- ==================================================================
-- NO-ALIASING, AS A POSTCONDITION.
--
-- `layPres appop .homSplit` is the whole content: it turns the context
-- splitting into a DISJOINT heap splitting of `layout u`, and `⊗ˢ-I`
-- packages that as a point of `⌈ layout u₁ ⌉ ∗ ⌈ layout u₂ ⌉`.
-- Nothing about disjointness is proved here: it arrived from four
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

-- THE HEADLINE OF THE LINEARITY ARGUMENT.  The Rust emitted for an
-- application establishes the two premises' boxes as SEPARATE regions.
noAlias : {u₁ u₂ u : L.Usage} (s : L.Use⊎ u₁ u₂ u)
        → ⟪ ⌈ [] ⌉ ⟫ compileRust u ⟪ ⌈ L.layout u₁ ⌉ ∗ ⌈ L.layout u₂ ⌉ ⟫ᵖ
noAlias {u = u} s =
  consequenceᵖ (compileRust u) idg (splitPost s) (compileTriple u)

-- ==================================================================
-- THE FRAME RULE, USED ON THE COMPILER'S OWN OUTPUT.
--
-- `boxProg` is a real `Box::new` -- the allocator picks the address --
-- so its postcondition is an existential and its locality is
-- `ISA.Toy.localAlloc`.  The frame is `⌈ layout u ⌉`, the compiler's
-- own output: allocating a scratch box leaves every variable's box
-- untouched.
-- ==================================================================

boxProg : RustProg
boxProg = boxS v1 ∷ []

boxProgTriple : ⟪ ⌈ [] ⌉ ⟫ boxProg ⟪ ⊕ᴰ Loc (λ l → ⌈ single l v1 ⌉) ⟫ᵖ
boxProgTriple = instrRule (boxS v1) (boxAx v1 [])

-- `local-⨟` and `local-skip` are `ISA.Machine`'s; `boxLocal` is
-- `ISA.Toy.localAlloc`.  No locality is proved here.
localBoxProg : Local (sem boxProg)
localBoxProg = local-⨟ (rstep (boxS v1)) skip (boxLocal v1) local-skip

framedBox : (R : Gr)
          → ⟪ ⌈ [] ⌉ ∗ R ⟫ boxProg ⟪ (⊕ᴰ Loc λ l → ⌈ single l v1 ⌉) ∗ R ⟫ᵖ
framedBox R = frameRule R boxProg localBoxProg boxProgTriple

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

-- BUILD THE FRAME, THEN ALLOCATE BESIDE IT.
spill : (u : L.Usage)
      → ⟪ ⌈ [] ⌉ ⟫ compileRust u ++ boxProg
        ⟪ (⊕ᴰ Loc λ l → ⌈ single l v1 ⌉) ∗ ⌈ L.layout u ⌉ ⟫ᵖ
spill u =
  seq++ (compileRust u) boxProg
    (consequenceᵖ (compileRust u) idg (unitL (L.layout u)) (compileTriple u))
    (framedBox ⌈ L.layout u ⌉)

-- ==================================================================
-- THE EXECUTABLE FRAGMENT, AND THE HEADLINE THEOREM.
-- ==================================================================

-- PRIMITIVE (phase 1): the compiler emits only `letS`.
placedCode : (i : ℕ) (u : L.Usage) → AllPlaced (code i u)
placedCode i []          = tt
placedCode i (true  ∷ u) = tt , placedCode (suc i) u
placedCode i (false ∷ u) = placedCode (suc i) u

-- ==================================================================
-- THE END-TO-END THEOREM -- THE SHARED SPECIFICATION, FOR RUST.
--
-- `observe` is the one exit from the Hoare layer, and this equation is
-- DERIVED from `compileTriple`: the program is not run and then
-- compared, it is run INSIDE the triple.
-- ==================================================================

runRust : (u : L.Usage) → evalRust (compileRust u) [] Eq.≡ L.layout u
runRust u =
  observe (compileRust u) (placedCode 0 u) [] (L.layout u) (compileTriple u)

-- ... and at a TERM, where `compileTm u t .fst` is the emitted Rust
runTm : (u : L.Usage) (t : L.Tm u)
      → evalRust (compileTm u t .fst) [] Eq.≡ L.layout u
runTm u t = runRust u

-- ==================================================================
-- OBSERVATION.  `refl` lines only, as the house rule says.
-- ==================================================================

-- the code, from a usage
_ : compileRust [] ≡ []
_ = refl

_ : compileRust (true ∷ true ∷ []) ≡ letS 0 v1 ∷ letS 1 v1 ∷ []
_ = refl

-- dead positions emit nothing, and the live ones keep their addresses
_ : compileRust (true ∷ false ∷ true ∷ []) ≡ letS 0 v1 ∷ letS 2 v1 ∷ []
_ = refl

-- CODE EMITTED FROM CLOSED LINEAR TERMS.  `idLin` and `selfApp` are
-- closed, so they allocate nothing -- the compiled program is EMPTY.
_ : compileTm [] L.idLin .fst ≡ []
_ = refl

_ : compileTm [] L.selfApp .fst ≡ []
_ = refl

-- ... and from an open one: `twoVar` is `x y` at two live variables
_ : compileTm (true ∷ true ∷ []) L.twoVar .fst ≡ letS 0 v1 ∷ letS 1 v1 ∷ []
_ = refl

_ : compileTm (true ∷ []) L.xVar .fst ≡ letS 0 v1 ∷ []
_ = refl

-- ==================================================================
-- THE MACHINE ACTUALLY RUNS.  `evalRust` on the emitted code, from the
-- empty heap, is the layout -- and this is a `refl`, i.e. the whole
-- chain (term ↦ usage ↦ Rust ↦ heap) reduces.
-- ==================================================================

_ : evalRust (compileTm (true ∷ true ∷ []) L.twoVar .fst) []
  ≡ (0 , v1) ∷ (1 , v1) ∷ []
_ = refl

_ : evalRust (compileTm (true ∷ true ∷ []) L.twoVar .fst) []
  ≡ L.layout (true ∷ true ∷ [])
_ = refl

-- a term over a scope of THREE with the middle variable dead: the
-- emitted Rust skips position 1, and the two live boxes keep their own
-- addresses -- the ADDRESS GAP survives compilation.
gapSplit : L.Use⊎ (true ∷ false ∷ false ∷ []) (false ∷ false ∷ true ∷ [])
                  (true ∷ false ∷ true ∷ [])
gapSplit = L.uleft (L.uskip (L.uright L.unil))

gapTm : L.Tm (true ∷ false ∷ true ∷ [])
gapTm = L.tapp gapSplit (L.tvar tt) (L.tvar tt)

_ : compileTm (true ∷ false ∷ true ∷ []) gapTm .fst ≡ letS 0 v1 ∷ letS 2 v1 ∷ []
_ = refl

_ : evalRust (compileTm (true ∷ false ∷ true ∷ []) gapTm .fst) []
  ≡ (0 , v1) ∷ (2 , v1) ∷ []
_ = refl

-- a closed term compiles to the empty program, which runs to the empty heap
_ : evalRust (compileTm [] L.selfApp .fst) [] ≡ []
_ = refl

-- ==================================================================
-- ... AND THE DERIVED EQUATION REDUCES TOO.  `runRust` is the triple
-- applied to `evalRust-sound`; that it is `Eq.refl` on the nose says
-- the Hoare proof is not merely inhabited but COMPUTES.
-- ==================================================================

_ : runRust (true ∷ true ∷ []) ≡ Eq.refl
_ = refl

_ : runTm (true ∷ true ∷ []) L.twoVar ≡ Eq.refl
_ = refl

_ : runRust (true ∷ false ∷ true ∷ []) ≡ Eq.refl
_ = refl

-- ==================================================================
-- THE EMITTED RUST, AS SOURCE TEXT.
--
-- `runAt srcTm u t` is the exit; everything to its left is a `⊢`-term.
-- These are the lines a `rustc` invocation would receive.
-- ==================================================================

-- a closed linear term allocates nothing: an empty function body
_ : runAt srcTm [] L.idLin ≡ "fn frame() {\n}\n"
_ = refl

_ : runAt srcTm [] L.selfApp ≡ "fn frame() {\n}\n"
_ = refl

-- one live variable, one owned box
_ : runAt srcTm (true ∷ []) L.xVar
  ≡ "fn frame() {\n    let x0: Box<u8> = Box::new(1u8);\n}\n"
_ = refl

-- TWO live variables: `x y`, whose two premises own DISJOINT boxes
-- (`noAlias`), emitted as two independent `Box::new` bindings
_ : runAt srcTm (true ∷ true ∷ []) L.twoVar
  ≡ "fn frame() {\n\
    \    let x0: Box<u8> = Box::new(1u8);\n\
    \    let x1: Box<u8> = Box::new(1u8);\n\
    \}\n"
_ = refl

-- ... and the DEAD MIDDLE POSITION: no `x1` binding, and the second
-- live variable is still at address 2.  The gap `LinLam/Codegen.lay`
-- leaves in the heap is visible in the source text.
_ : runAt srcTm (true ∷ false ∷ true ∷ []) gapTm
  ≡ "fn frame() {\n\
    \    let x0: Box<u8> = Box::new(1u8);\n\
    \    let x2: Box<u8> = Box::new(1u8);\n\
    \}\n"
_ = refl

-- ==================================================================
-- THE NO-ALIASING SPLIT, EVALUATED, AND READ OFF THE HEAP THE EMITTED
-- RUST ACTUALLY PRODUCED.  `noAliasRun` runs the compiled program (via
-- `evalRust-sound`) and returns the postcondition AT THE RESULTING
-- HEAP, so its first component is a disjoint decomposition of a heap
-- that was COMPUTED, not assumed.
-- ==================================================================

_ : layJoin L.twoSplit .fst
  ≡ ( single 0 v1 , single 1 v1 , left (right nil) , ((tt , tt) , tt) )
_ = refl

noAliasRun : {u₁ u₂ u : L.Usage} → L.Use⊎ u₁ u₂ u
           → (⌈ L.layout u₁ ⌉ ∗ ⌈ L.layout u₂ ⌉) (evalRust (compileRust u) [])
noAliasRun {u = u} s =
  noAlias s [] (⌈⌉-pt []) (evalRust (compileRust u) [])
          (evalRust-sound (compileRust u) (placedCode 0 u) [])

_ : noAliasRun L.twoSplit .fst
  ≡ ( single 0 v1 , single 1 v1 , left (right nil) , ((tt , tt) , tt) )
_ = refl

-- and at the GAP term: the two owned boxes are at addresses 0 and 2,
-- and the `_#_` proof is still a nest of `tt`
_ : noAliasRun gapSplit .fst
  ≡ ( single 0 v1 , single 2 v1 , left (right nil) , ((tt , tt) , tt) )
_ = refl
