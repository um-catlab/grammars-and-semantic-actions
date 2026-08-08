{- THE TENSOR RULE FOR DECISIONS, AS AN INTERFACE. `Decidable.Tensor`
   derives `dec-⊗` from UNIQUE READABILITY: at most one splitting, so a
   refutation at one slot refutes the whole tensor. -}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Decidable.Splittings where

open import Cubical.Foundations.Prelude

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Decidable.Tensor
open import TheoryGrammar.Decidable.Enumerated

private variable ℓS ℓ ℓ' ℓX ℓP ℓA : Level

-- A `DecSplittings Fib ℓA` denotes: over this `Fibered`, decidability is
-- closed under the tensor.
record DecSplittings {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
                     (Fib : Fibered σ ℓX ℓP) ℓA
  : Type (ℓ-max ℓS (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓX (ℓ-max ℓP (ℓ-suc ℓA)))))) where
  open DecFib Fib
  field
    -- Given, at EVERY splitting of `m`, a decision at every slot, decide
    -- the tensor at `m`.
    dec-⊗ˢ : (o : σ .ops)
             (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
             (m : Fib .carrier (σ .resultSort o))
           → ((sp : Fib .Split o m) (a : σ .arities o)
              → Dec⟨ A a ⟩ (Fib .parts o m sp a))
           → Dec⟨ ⊗ˢ o A ⟩ m

open DecSplittings public

-- Route 1: unique readability.  This is `Decidable.Tensor` verbatim.
fromReadable : {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} {Fib : Fibered σ ℓX ℓP}
             → DecReadable Fib ℓA → DecSplittings Fib ℓA
fromReadable DR .dec-⊗ˢ = DecTensor.dec-⊗ DR

-- Route 2: finite enumeration of the splittings.
fromEnumerable : {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} {Fib : Fibered σ ℓX ℓP}
               → DecEnumerable Fib ℓA → DecSplittings Fib ℓA
fromEnumerable DE .dec-⊗ˢ o A m d = DecTensorEnum.dec-⊗-enum DE o A m d

-- `DecSplittings` IS STRICTLY STRONGER THAN `DecTensorRule`.

-- ROUTE 3: THE DERIVATIVE. Not a function here, and the reason is worth
-- stating, because the obvious `fromDerivative` does not exist.
