{-
  THE TENSOR RULE FOR DECISIONS, AS AN INTERFACE.

  `Decidable.Tensor` derives `dec-⊗` from UNIQUE READABILITY: at most one
  splitting, so a refutation at one slot refutes the whole tensor.  That
  is a property of a SYNTAX promodel and it fails for every substructural
  context promodel -- a bag splits into two fib-bags in exponentially
  many ways.  Yet the tensor is still decidable there, because the
  splittings, though many, are finitely enumerable.

  So the reusable notion is the CONCLUSION of `dec-⊗`, not its proof.
  `fromReadable` records that unique readability is one route to it, and
  `fromEnumerable` that finite enumeration of the splittings is another
  -- the one the resource promodels need.  Both routes end at the same
  field, and everything downstream sees only the field.
-}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Decidable.Splittings where

open import Cubical.Foundations.Prelude

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Decidable.Additive
open import TheoryGrammar.Decidable.Tensor
open import TheoryGrammar.Decidable.Enumerated

private variable ℓS ℓ ℓ' ℓX ℓP ℓA : Level

record DecSplittings {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
                     (Fib : Fibered σ ℓX ℓP) ℓA
  : Type (ℓ-max ℓS (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓX (ℓ-max ℓP (ℓ-suc ℓA)))))) where
  open DecFib Fib
  field
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

-- Route 2: finite enumeration of the splittings.  This is the route the
-- resource promodels need -- a bag splits exponentially many ways, so
-- `splitProp` is false there, but the splittings are still listable.
-- Both routes land on the same field, and everything downstream sees
-- only the field.
fromEnumerable : {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} {Fib : Fibered σ ℓX ℓP}
               → DecEnumerable Fib ℓA → DecSplittings Fib ℓA
fromEnumerable DE .dec-⊗ˢ o A m d = DecTensorEnum.dec-⊗-enum DE o A m d
