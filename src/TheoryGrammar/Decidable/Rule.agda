{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The tensor decision rule, stated in the language rather than by the
   evidence used to establish it. -}
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
open import TheoryGrammar.Decidable.Splittings as DS using (DecSplittings)

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

-- Constructor 1: unique readability.  At most one decomposition, so
-- there is nothing to search.  Holds for a free signature.

-- FIRST, THE PROJECTION FROM `DecSplittings`.

toRule : {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} {Fib : Fibered σ ℓX ℓP}
       → DecSplittings Fib ℓA → DecTensorRule Fib {ℓA = ℓA}
toRule DS o A d m _ = DS .DS.dec-⊗ˢ o A m (d m)

fromUnique : {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} {Fib : Fibered σ ℓX ℓP}
           → DecReadable Fib ℓA → DecTensorRule Fib {ℓA = ℓA}
fromUnique DR = toRule (DS.fromReadable DR)

-- Constructor 2: enumerable decompositions.  Finitely many, so the
-- search terminates and completeness turns exhaustion into refutation.
-- Holds for the monoid (length+1 cuts) and for bags (2^n).

fromEnumerable : {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} {Fib : Fibered σ ℓX ℓP}
               → DecEnumerable Fib ℓA → DecTensorRule Fib {ℓA = ℓA}
fromEnumerable DE = toRule (DS.fromEnumerable DE)

-- Constructor 3: a derivative law. BUILT, but only per-`Fibered`. δ_c (A ⊗
-- B) ≅ (A ε & δ_c B) ⊕ (δ_c A ⊗ B) establishes the same conclusion with NO
-- search: the `length w + 1` decompositions are the unfolding of this two-
-- case law along the word, so a derivative-based decider does not pay for
-- the...
