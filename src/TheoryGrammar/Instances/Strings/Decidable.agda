{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Strings satisfy the tensor decision rule, by the enumerable route:
   `cuts` is complete, and the arity is `Bool` so slotwise decisions
   combine. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Strings.Decidable (Char : Type₀) where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.List

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Enumerable
open import TheoryGrammar.Decidable.Additive
open import TheoryGrammar.Decidable.Tensor
open import TheoryGrammar.Decidable.Enumerated hiding (enumSplit; enumComplete)
open import TheoryGrammar.Decidable.Rule

open import TheoryGrammar.Instances.Strings.Enumeration Char public

open DecEnum strFib using (⊗at; Refutes)
open DecFib  strFib using (Dec⟨_⟩)

-- `DecEnumerable` has FIELDS named `enumSplit` / `enumComplete`, and
-- `Enumeration` (opened above) has DEFINITIONS of the same names, both
-- unqualified.
strDecEnum : DecEnumerable strFib ℓ-zero
strDecEnum .DecEnumerable.enumSplit    = enumSplit
strDecEnum .DecEnumerable.enumComplete = enumComplete
-- nullary: the empty product of slots is inhabited outright
strDecEnum .decAt nilop A m sp d = inl λ ()
-- binary: two slots, so `decΠBool`
strDecEnum .decAt appop A m sp d = decΠBool (d true) (d false)

-- ... and hence the rule, stated in the language
strDecTensor : DecTensorRule strFib {ℓA = ℓ-zero}
strDecTensor = fromEnumerable strDecEnum
