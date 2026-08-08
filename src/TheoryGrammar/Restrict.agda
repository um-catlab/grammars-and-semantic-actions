{- RESTRICTION ALONG AN INJECTION OF OPERATIONS. A `Fibered` for a
   signature is one for any SUB-signature, by composition -- no data is
   invented, so `Split` and `parts` are literally reused. -}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Restrict where

open import Cubical.Foundations.Prelude

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered

private variable ℓS ℓ ℓ' ℓ₂ ℓX ℓP : Level

module _ {S : Type ℓS} (σ : SortedSig S ℓ ℓ') {O : Type ℓ₂} (ι : O → σ .ops) where

  restrictSig : SortedSig S ℓ₂ ℓ'
  restrictSig .ops          = O
  restrictSig .arities o    = σ .arities (ι o)
  restrictSig .sortOf o a   = σ .sortOf (ι o) a
  restrictSig .resultSort o = σ .resultSort (ι o)

  restrictFib : Fibered σ ℓX ℓP → Fibered restrictSig ℓX ℓP
  restrictFib Fib .carrier  = Fib .carrier
  restrictFib Fib .Split o  = Fib .Split (ι o)
  restrictFib Fib .parts o  = Fib .parts (ι o)
