{-
  RESTRICTION ALONG AN INJECTION OF OPERATIONS.

  A promodel for a signature is one for any SUB-signature, by
  composition -- no data is invented, so `Split` and `parts` are
  literally reused.  That is what makes

      "the ring fragment has a total point, the field does not"
      "the unit of the separation algebra is total, the join is not"

  statements about ONE promodel rather than about two unrelated ones:
  the localisation of an obstruction is a statement about `ι`.

  MAIN: `restrictSig` (the sub-signature) and `restrictFib` (its
  promodel, whose `Split` and `parts` are the original's, precomposed).

  GENERIC over any `SortedSig`/`Fibered`; nothing here mentions an
  instance.  It lived in `Instances/Field/Base.agda` and was imported
  from outside the field by `Instances/Heap/Located.agda`, so a HEAP
  file depended on the FIELD instance.  Both users now read it here.

  PRIMITIVE: none.
-}
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
