{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  SEPARATION LOGIC, AS THE GENERIC CONNECTIVES AT A PARTIAL PROMODEL.

  Nothing in this file is new machinery.  `∗`, `emp` and `─∗` are `⊗ˢ`,
  `⊗ˢ empOp` and `⊸ˢ` from `RulesFib`, renamed; the frame rule is
  `⊗ˢ-map`; the adjunction between `∗` and `─∗` is `⊸ˢ-app`.  That is the
  claim being demonstrated: separation logic is what the dependent Lambek
  calculus BECOMES at a promodel whose operation is partial, and it costs
  no new infrastructure whatsoever.

  Worth stating precisely which of these are phase 1 and why.  `∗`, `emp`,
  `─∗` and `frame` are phase 2 -- composites of `RulesF` combinators, with
  no heap ever matched on.  `∗-comm` and `∗-assoc`-style facts ARE phase 1,
  because commutativity and associativity of disjoint union are properties
  of `Disj` and have to be proved by recursion on it.  That is the right
  split: the LOGIC is generic, the ALGEBRA of heaps is not.
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Heap.Connectives where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.List
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib

open import TheoryGrammar.Instances.Heap.Base public

-- ==================================================================
-- The separation-logic connectives.
-- ==================================================================

-- `emp` -- the nullary case.  Its arity is `⊥`, so there is no payload:
-- `emp w` is exactly `Emp w`, modulo the vacuous function.
emp : Hp
emp = ⊗ˢ empOp (λ ())

-- SEPARATING CONJUNCTION.  This is `⊗ˢ` at `joinOp`, and it is where
-- partiality does its work: `(A ∗ B) w` is inhabited only when `w`
-- actually splits, and `Disj` has no clause for overlapping heaps.
_∗_ : Hp → Hp → Hp
A ∗ B = ⊗ˢ joinOp (λ b → if b then A else B)

infixr 20 _∗_

-- MAGIC WAND.  `⊸ˢ` at slot `false`: the index sits in the second slot,
-- an `A` sits in the first, and the result is a `B` at the join.  The
-- `⊤G` in the second component is because that slot IS the index -- the
-- residual must not demand a payload there.
_─∗_ : Hp → Hp → Hp
A ─∗ B = ⊸ˢ joinOp false (λ b → if b then A else ⊤G) B

infixr 19 _─∗_

-- ==================================================================
-- THE FRAME RULE is the functorial action of `∗`, i.e. `⊗ˢ-map`.  The
-- families are pinned explicitly: `⊗ˢ joinOp (λ b → if b then A else C)`
-- unfolds to a Σ in which `A` occurs only under `parts`, so no
-- first-order unifier recovers it (the trap in CLAUDE.md).
-- ==================================================================

frame : {A B : Hp} (C : Hp) → A ⊢ B → (A ∗ C) ⊢ (B ∗ C)
frame {A} {B} C f =
  ⊗ˢ-map joinOp {A = λ b → if b then A else C}
                {B = λ b → if b then B else C}
                (λ { true → f ; false → idg })

-- ... and symmetrically on the right.
frameL : {A B : Hp} (C : Hp) → A ⊢ B → (C ∗ A) ⊢ (C ∗ B)
frameL {A} {B} C f =
  ⊗ˢ-map joinOp {A = λ b → if b then C else A}
                {B = λ b → if b then C else B}
                (λ { true → idg ; false → f })

-- ==================================================================
-- THE ADJUNCTION.  `⊸ˢ-app` is exactly modus ponens for the wand:
-- from `A ⊢ (B ─∗ C)` conclude `A ∗ B ⊢ C`.  Generic, no heap matched.
-- ==================================================================

-- PRIMITIVE (phase 1), and pure plumbing -- compare `intoQ` in
-- Bags/Quicksort.  `⊸ˢ` demands a payload at EVERY slot including the
-- focused one, so the wand (which asks for `⊤G` there) has to be weakened
-- to the family `⊸ˢ-app` expects.  Nothing is discarded but a `tt`.
private
  wandWeaken : {A B : Hp}
             → (A ─∗ B) ⊢ ⊸ˢ joinOp false (λ b → if b then A else (A ─∗ B)) B
  wandWeaken x w m sp e k = w m sp e (λ { true → k true ; false → tt })

-- MODUS PONENS for the wand, and it really is `⊸ˢ-app`.
wand-mp : {A B : Hp} → (A ∗ (A ─∗ B)) ⊢ B
wand-mp {A} {B} =
  ⊸ˢ-app joinOp false {A = λ b → if b then A else (A ─∗ B)} {B = B} wandWeaken

-- ==================================================================
-- COMMUTATIVITY.  PHASE 1 -- this is a fact about `Disj`, not about the
-- logic, and it is a three-line structural recursion because the
-- splittings are DATA.  Note the constructors swap in pairs, which is
-- precisely "disjointness is symmetric".
-- ==================================================================

-- PRIMITIVE (phase 1)
disjSwap : ∀ {u v w} → Disj u v w → Disj v u w
disjSwap dnil       = dnil
disjSwap (dl d)     = dr (disjSwap d)
disjSwap (dr d)     = dl (disjSwap d)
disjSwap (dnone d)  = dnone (disjSwap d)

-- PRIMITIVE (phase 1): the only place a splitting is matched.
∗-comm : {A B : Hp} → (A ∗ B) ⊢ (B ∗ A)
∗-comm w ((u , v , d) , h) =
  (v , u , disjSwap d) , λ { true → h false ; false → h true }

-- an involution, and `disjSwap` is one too
disjSwap² : ∀ {u v w} (d : Disj u v w) → disjSwap (disjSwap d) ≡ d
disjSwap² dnil      = refl
disjSwap² (dl d)    = cong dl (disjSwap² d)
disjSwap² (dr d)    = cong dr (disjSwap² d)
disjSwap² (dnone d) = cong dnone (disjSwap² d)
