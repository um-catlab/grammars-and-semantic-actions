{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE CONTROL-FLOW RULES, RUN.

  `ISA.Control.Base` derives `condRule` and two `while` rules generically.
  This file instantiates them at `ISA.Toy`'s machine -- `heapFib`, and
  the instruction set `nop`/`alloc`/`store` -- and checks that the
  derived triples COMPUTE, by `refl`.

  ------------------------------------------------------------------
  THE PROGRAM
  ------------------------------------------------------------------

  The heap is an association list, so the only state a toy instruction
  can decrease is the VALUE in a cell (`alloc` only grows the heap).  So
  the variant is read off the head cell:

      rk h = 0 , 1 , 2   according as the head cell holds v0 , v1 , v2

  and the program is

      while (rk ≠ 0) { if (head = v2) then store 0 v1 else store 0 v0 }

  which is a `while` whose body is an `if` whose branches are literal
  `ISA.Toy` instructions.  From `[0 ↦ v2]` it runs two iterations,
  `v2 → v1 → v0`, and `rk` strictly decreases at each -- which is
  `decBody`, the ONLY thing `whileRule` asks beyond the body triple.

  The invariant is

      Inv = ⊕ᴰ Val (λ y → ⌈ single 0 y ⌉)          "the heap is one cell at 0"

  and it is preserved because `storeAx`'s postcondition is a
  representable, so `⊕ᴰ-I` re-enters `Inv` with no reasoning at all.

  ------------------------------------------------------------------
  WHAT THE `refl` TESTS SHOW
  ------------------------------------------------------------------

  * `_ : ifTriple … ≡ (v1 , Eq.refl)`  --  the conditional rule computes.
    `condRule` is `wp-sum← ∘ &ᴰ-I ∘ boolΠ ∘ wp-⨟← ∘ wp-assume← ∘ ⇒-I`,
    every step of which is a projection or a currying, so the derived
    triple evaluates on a concrete run to the concrete postcondition.

  * `_ : loopTripleInd … ≡ ((v0 , Eq.refl) , Eq.refl)`  --  the route-A
    loop rule computes, through both iterations.

  * the same `≡ ((v0 , Eq.refl) , Eq.refl)` for `loopTriple`, the route-B
    rule -- so `löb` at a ℕ-valued variant COMPUTES here, which is not
    automatic; see the note there.

  * `descentIsNecessary`  --  `ISA.Control.Base.noDescent` at `[]`.  The
    invariant rule WITHOUT the descent hypothesis proves `⊥`, so `↓` is
    not decoration.
-}
open import Cubical.Foundations.Prelude

module ISA.Control.Toy where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Nat.Order using (_<_)
open import Cubical.Data.Unit
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Instances.Heap.Base
  using (Loc; Val; v0; v1; v2; Cell; Heap; single; heapFib)

open import ISA.Toy
  using (ToyI; nop; alloc; store; Alloc; Store; toyStep; storeAx; allocAx; sem)

open import ISA.Control.Base heapFib

-- ==================================================================
-- THE VARIANT AND THE TWO TESTS.
--
-- PRIMITIVE (phase 1): these read the representation, which is what a
-- flag register is.  Nothing else in the file matches on a heap.
-- ==================================================================

topV : Heap → Val
topV []            = v0
topV ((_ , x) ∷ _) = x

rkV : Val → ℕ
rkV v0 = 0
rkV v1 = 1
rkV v2 = 2

rk : Heap → ℕ
rk h = rkV (topV h)

nz : ℕ → Bool
nz zero    = false
nz (suc _) = true

eqV2 : Val → Bool
eqV2 v0 = false
eqV2 v1 = false
eqV2 v2 = true

-- the loop guard: "the head cell has not reached v0 yet"
busy : Test
busy h = nz (rk h)

-- the branch guard: "the head cell holds v2"
isV2 : Test
isV2 h = eqV2 (topV h)

-- ==================================================================
-- THE BODY: an `if` between two `ISA.Toy` instructions.
-- ==================================================================

body : Cmd
body = ifC isV2 (Store 0 v1) (Store 0 v0)

-- the invariant: "the heap is a single cell at location 0"
Inv : Gr
Inv = ⊕ᴰ Val (λ y → ⌈ single 0 y ⌉)

-- `store` re-enters the invariant: its postcondition is a representable,
-- so `⊕ᴰ-I` is the whole of it.  A composite.
storeI : (x : Val) → ⟪ Inv ⟫ Store 0 x ⟪ Inv ⟫
storeI x = ⊕ᴰ-E λ y →
  consequence (Store 0 x) idg
    (⊕ᴰ-I Val {A = λ z → ⌈ single 0 z ⌉} x)
    (storeAx 0 x y)

-- ==================================================================
-- THE CONDITIONAL RULE, USED.
-- ==================================================================

ifTriple : ⟪ Inv ⟫ body ⟪ Inv ⟫
ifTriple = condRule isV2 (Store 0 v1) (Store 0 v0)
             (storeI v1 ∘g &-E₁) (storeI v0 ∘g &-E₁)

-- a concrete run of the conditional: at `[0 ↦ v2]` the guard fires
-- `true`, so the `store 0 v1` branch is taken
runIf : body (single 0 v2) (single 0 v1)
runIf = true , single 0 v2 , (Eq.refl , Eq.refl) , v2 , Eq.refl , Eq.refl

-- THE CONDITIONAL RULE COMPUTES.
_ : ifTriple (single 0 v2) (v2 , Eq.refl) (single 0 v1) runIf ≡ (v1 , Eq.refl)
_ = refl

-- ... and the other branch, at `[0 ↦ v1]`
runIf' : body (single 0 v1) (single 0 v0)
runIf' = false , single 0 v1 , (Eq.refl , Eq.refl) , v1 , Eq.refl , Eq.refl

_ : ifTriple (single 0 v1) (v1 , Eq.refl) (single 0 v0) runIf' ≡ (v0 , Eq.refl)
_ = refl

-- ==================================================================
-- STRAIGHT-LINE CODE AND A BRANCH, MIXED.  `seqCmd` is `ISA.Machine`'s,
-- untouched: a conditional is just another command to sequence with.
-- ==================================================================

mixed : ⟪ Inv ⟫ sem (nop ∷ []) ⨟ body ⟪ Inv ⟫
mixed = seqCmd (sem (nop ∷ [])) body
          (seqCmd skip skip (skipRule Inv) (skipRule Inv))
          ifTriple

-- ==================================================================
-- THE BODY TRIPLE, WITH THE LOOP GUARD IN THE PRECONDITION.
-- ==================================================================

bodyTriple : ⟪ Inv & Tst busy true ⟫ body ⟪ Inv ⟫
bodyTriple = ifTriple ∘g &-E₁

-- ==================================================================
-- THE VARIANT DISCHARGED.  PRIMITIVE (phase 1): the one place a run of
-- the body is destructured, and the only arithmetic in the file.
-- ==================================================================

open Variant rk

goT : (y : Val) → eqV2 y Eq.≡ true → 1 < rkV y
goT v0 ()
goT v1 ()
goT v2 _ = 0 , refl

goF : (y : Val) → nz (rkV y) Eq.≡ true → 0 < rkV y
goF v0 ()
goF v1 _ = 0 , refl
goF v2 _ = 1 , refl

decBody : Decreasing busy body
decBody h h₁ e (true  , _ , (e2 , Eq.refl) , y , Eq.refl , Eq.refl) = goT y e2
decBody h h₁ e (false , _ , (e2 , Eq.refl) , y , Eq.refl , Eq.refl) = goF y e

-- ==================================================================
-- THE TWO LOOP RULES, USED.  Same statement, different hypotheses:
-- route A reads the descent off the inductive derivation, route B is
-- given it as `decBody`.
-- ==================================================================

loopTripleInd : ⟪ Inv ⟫ While busy body ⟪ Inv & Tst busy false ⟫
loopTripleInd = whileRuleInd busy body Inv bodyTriple

loopTriple : ⟪ Inv ⟫ While busy body ⟪ Inv & Tst busy false ⟫
loopTriple = whileRule busy body Inv decBody bodyTriple

-- ==================================================================
-- A CONCRETE RUN: v2 → v1 → v0, two iterations then the guard fails.
-- ==================================================================

run2 : While busy body (single 0 v2) (single 0 v0)
run2 =
  wh-step {h₁ = single 0 v1} Eq.refl
    (true , single 0 v2 , (Eq.refl , Eq.refl) , v2 , Eq.refl , Eq.refl)
    (wh-step {h₁ = single 0 v0} Eq.refl
      (false , single 0 v1 , (Eq.refl , Eq.refl) , v1 , Eq.refl , Eq.refl)
      (wh-stop Eq.refl Eq.refl))

-- THE ROUTE-A LOOP RULE COMPUTES, through both iterations.
_ : loopTripleInd (single 0 v2) (v2 , Eq.refl) (single 0 v0) run2
    ≡ ((v0 , Eq.refl) , Eq.refl)
_ = refl

-- ==================================================================
-- THE DESCENT IS NOT DECORATION.
-- ==================================================================

descentIsNecessary :
  ((t : Test) (c w : Cmd) (Inv' : Gr)
   → w ⊑ ifC t (c ⨟ w) skip
   → ⟪ Inv' & Tst t true ⟫ c ⟪ Inv' ⟫
   → ⟪ Inv' ⟫ w ⟪ Inv' & Tst t false ⟫)
  → ⊥
descentIsNecessary = noDescent []

-- ... AND SO DOES THE ROUTE-B ONE.  This is worth a line: `whileRule`
-- goes through `löb`, i.e. `WFI.induction` at the accessibility of
-- `rk h`, and abstract well-founded recursion notoriously fails to
-- reduce (see `Grammar/Later`'s Eq-vs-transp note).  It reduces here
-- because the order is pulled back from ℕ along `rk` and every index in
-- the test is a NUMERAL, so `<-wellfounded` unfolds to a canonical
-- `acc`.  A variant valued in a non-computing order would lose this.
_ : loopTriple (single 0 v2) (v2 , Eq.refl) (single 0 v0) run2
    ≡ ((v0 , Eq.refl) , Eq.refl)
_ = refl
