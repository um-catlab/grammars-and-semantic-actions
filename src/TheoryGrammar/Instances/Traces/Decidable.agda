{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  Traces satisfy the tensor decision rule, by the enumerable route.

  `splitProp` is false here (a word shuffles many ways), so
  `Decidable.Tensor.dec-⊗` is out of reach and `DecSplittings` is the
  interface that survives; `fromEnumerable` is the constructor that
  applies.  The arity is `Bool`, so slotwise decisions combine by
  `decΠBool` exactly as at `Strings`.
-}
open import Cubical.Foundations.Prelude

open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import TheoryGrammar.Enumerable using (No)

module TheoryGrammar.Instances.Traces.Decidable
  (Letter : Type₀) (Ind : Letter → Letter → Type₀)
  (decInd    : (x y : Letter) → Ind x y ⊎ No (Ind x y))
  (isPropInd : (x y : Letter) → isProp (Ind x y))
  where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Unit
open import Cubical.Data.List

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Enumerable
open import TheoryGrammar.Decidable.Additive
open import TheoryGrammar.Decidable.Tensor
open import TheoryGrammar.Decidable.Enumerated hiding (enumSplit; enumComplete)
open import TheoryGrammar.Decidable.Rule
import TheoryGrammar.Decidable.Splittings as DS

open import TheoryGrammar.Instances.Traces.Enumeration
       Letter Ind decInd isPropInd public

-- The copatterns on the left are projections and resolve on their own;
-- the right-hand sides would be ambiguous against `Enumeration`'s
-- definitions of the same names, so the fields are qualified there.
trDecEnum : DecEnumerable trFib ℓ-zero
trDecEnum .DecEnumerable.enumSplit    = enumSplit
trDecEnum .DecEnumerable.enumComplete = enumComplete
trDecEnum .decAt nilop A m sp d = inl λ ()
trDecEnum .decAt appop A m sp d = decΠBool (d true) (d false)

-- the interface everything downstream sees
trDecSplittings : DS.DecSplittings trFib ℓ-zero
trDecSplittings = DS.fromEnumerable trDecEnum

-- ... and the same fact stated in the language, as `⊗-EM`
trDecTensor : DecTensorRule trFib {ℓA = ℓ-zero}
trDecTensor = fromEnumerable trDecEnum
