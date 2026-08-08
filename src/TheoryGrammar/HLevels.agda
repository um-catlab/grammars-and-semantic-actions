{-# OPTIONS --lossy-unification #-}
{- SET-VALUED GRAMMARS, and why the hypothesis belongs on the WORLDS. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.HLevels where

open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; isSet⊎)
open import Cubical.Data.Unit
open import Cubical.Data.Empty as E using ()

import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered

private variable ℓS ℓ ℓ' ℓX ℓP ℓA ℓB ℓY : Level

module SetG {S : Type ℓS} (X : S → Type ℓX) where

  open CarrierNotation X

  isSetGrammar : {s : S} → TheoryTy ℓA s → Type (ℓ-max ℓX ℓA)
  isSetGrammar {s = s} A = (w : X s) → isSet (A w)

  -- REPRESENTABLES ARE PROPOSITIONS -- this is the base case, and the
  -- reason the hypothesis belongs on the worlds.

  ⌈⌉-isProp : {s : S} → isSet (X s) → (a w : X s) → isProp (⌈ a ⌉ w)
  ⌈⌉-isProp sx a w = subst isProp Eq.PathPathEq (sx w a)

  ⌈⌉-isSet : {s : S} → isSet (X s) → (a : X s) → isSetGrammar (⌈ a ⌉)
  ⌈⌉-isSet sx a w = isProp→isSet (⌈⌉-isProp sx a w)

  -- CLOSURE.  Nothing here is surprising; the point is that the list
  -- is complete, so a grammar written in the connectives never needs
  -- its own set-ness proof.

  isSet-⊤ : {s : S} → isSetGrammar (⊤G {s})
  isSet-⊤ _ = isSetUnit

  isSet-⊥ : {s : S} → isSetGrammar (⊥G {s})
  isSet-⊥ _ = isProp→isSet (λ ())

  isSet-⊕ : {s : S} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s}
          → isSetGrammar A → isSetGrammar B → isSetGrammar (A ⊕ B)
  isSet-⊕ sa sb w = isSet⊎ (sa w) (sb w)

  isSet-& : {s : S} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s}
          → isSetGrammar A → isSetGrammar B → isSetGrammar (A & B)
  isSet-& sa sb w = isSet× (sa w) (sb w)

  isSet-⇒ : {s : S} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s}
          → isSetGrammar B → isSetGrammar (A ⇒ B)
  isSet-⇒ sb w = isSet→ (sb w)

  isSet-⊕ᴰ : {s : S} {Y : Type ℓY} {F : Y → TheoryTy ℓA s}
           → isSet Y → ((y : Y) → isSetGrammar (F y))
           → isSetGrammar (⊕ᴰ Y F)
  isSet-⊕ᴰ sy sf w = isSetΣ sy (λ y → sf y w)

  isSet-&ᴰ : {s : S} {Y : Type ℓY} {F : Y → TheoryTy ℓA s}
           → ((y : Y) → isSetGrammar (F y)) → isSetGrammar (&ᴰ Y F)
  isSet-&ᴰ sf w = isSetΠ (λ y → sf y w)

-- ... and the convolution, which needs the SPLITTINGS to be a set as well
-- as the slots.
module SetFib {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (Fib : Fibered σ ℓX ℓP)
  where

  open FibNotation Fib
  open SetG (Fib .carrier) public

  isSetSplit : Type (ℓ-max ℓ (ℓ-max ℓX ℓP))
  isSetSplit = (o : σ .ops) (m : Fib .carrier (σ .resultSort o))
             → isSet (Fib .Split o m)

  isSet-⊗ˢ : isSetSplit → (o : σ .ops)
             {A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a)}
           → ((a : σ .arities o) → isSetGrammar (A a))
           → isSetGrammar (⊗ˢ o A)
  isSet-⊗ˢ ss o sa m =
    isSetΣ (ss o m) (λ sp → isSetΠ (λ a → sa a (Fib .parts o m sp a)))
