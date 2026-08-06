{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The tensor decision rule, stated in the language rather than by the
   evidence used to establish it.

   `DecReadable` exposes `splitProp`; `DecEnumerable` exposes a `List`
   with a completeness proof.  Both are WITNESSES.  What a client needs
   is the conclusion -- excluded middle for the multiplicative -- and
   the two records are then constructors for one interface, with a
   derivative law a third. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Decidable.Rule where

open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Rules
open import TheoryGrammar.RulesFib
open import TheoryGrammar.Par
open import TheoryGrammar.Decidable.Additive
open import TheoryGrammar.Decidable.Tensor
open import TheoryGrammar.Decidable.Enumerated

private variable ℓS ℓ ℓ' ℓX ℓP ℓA : Level

module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (Fib : Fibered σ ℓX ℓP) where

  open DecFib Fib
  open ParS Fib using (⊗-EM)

  -- THE INTERFACE.  Slotwise decisions yield a decision of the tensor,
  -- whose refuting side is (by `¬⊗-curry`) a product of refutations,
  -- one per decomposition.
  DecTensorRule : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓX (ℓ-max ℓP (ℓ-suc ℓA)))))
  DecTensorRule {ℓA = ℓA} =
    (o : σ .ops) (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
    → ((m : Fib .carrier (σ .resultSort o)) (sp : Fib .Split o m)
       (a : σ .arities o) → Dec⟨ A a ⟩ (Fib .parts o m sp a))
    → ⊗-EM o A

-- ==================================================================
-- Constructor 1: unique readability.  At most one decomposition, so
-- there is nothing to search.  Holds for a free signature.
-- ==================================================================

fromUnique : {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} {Fib : Fibered σ ℓX ℓP}
           → DecReadable Fib ℓA → DecTensorRule Fib {ℓA = ℓA}
fromUnique {Fib = Fib} DR o A d m _ = DecTensor.dec-⊗ DR o A m (d m)

-- ==================================================================
-- Constructor 2: enumerable decompositions.  Finitely many, so the
-- search terminates and completeness turns exhaustion into refutation.
-- Holds for the monoid (length+1 cuts) and for bags (2^n).
-- ==================================================================

fromEnumerable : {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} {Fib : Fibered σ ℓX ℓP}
               → DecEnumerable Fib ℓA → DecTensorRule Fib {ℓA = ℓA}
fromEnumerable DE o A d = enum→⊗EM DE o A d

-- ==================================================================
-- Constructor 3, NOT built: a derivative law.
--
--   δ_c (A ⊗ B) ≅ (δ_c A ⊗ B) ⊕ (ν A & δ_c B)
--
-- an isomorphism of grammars (see Grammar/SplitExperiment.agda for the
-- string case).  This establishes the same conclusion with NO search at
-- all -- the `length w + 1` decompositions are the unfolding of a
-- two-case law along the word, so a derivative-based instance would not
-- pay for the enumeration.  It needs a unary operation to differentiate
-- along, and fails for bags, where Levi's lemma fails and δ does not
-- lift.  That is exactly the boundary: derivative where available,
-- enumeration as the fallback.
-- ==================================================================
