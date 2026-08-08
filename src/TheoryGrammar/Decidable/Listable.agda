{- DECIDING THE INDEXED ADDITIVES. `dec-⊕` and `dec-&` (Decidable.Additive)
   are combinator composites and need no hypothesis, because a binary sum
   has two summands and both are in hand. -}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Decidable.Listable where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.List

open import TheoryGrammar.Base
open import TheoryGrammar.Enumerable
open import TheoryGrammar.Decidable.Additive

private variable ℓS ℓX ℓA ℓY : Level

module DecList {S : Type ℓS} (Car : S → Type ℓX) where

  open DecAdd Car

  private variable s : S

  -- The indexed SUM, over a listable tag type.

  dec-⊕ᴰ : (Y : Type ℓY) (A : Y → TheoryTy ℓA s)
           (ys : List Y) → ((y : Y) → y ∈L ys)
         → &ᴰ Y (λ y → Dec⟨ A y ⟩) ⊢ Dec⟨ ⊕ᴰ Y A ⟩
  dec-⊕ᴰ Y A ys complete m d = decΣ ys complete d

  -- The indexed PRODUCT, at the arity `Bool`.

  dec-&ᴰ : (A : Bool → TheoryTy ℓA s)
         → &ᴰ Bool (λ b → Dec⟨ A b ⟩) ⊢ Dec⟨ &ᴰ Bool A ⟩
  dec-&ᴰ A m d = decΠBool (d true) (d false)

  -- ... and the indexed PRODUCT at a listable index.  `findΠ` returns
  -- the OFFENDING tag, which is what turns "this component fails" into
  -- a refutation of the product.
  dec-&ᴰL : (Y : Type ℓY) (A : Y → TheoryTy ℓA s)
            (ys : List Y) → ((y : Y) → y ∈L ys)
          → &ᴰ Y (λ y → Dec⟨ A y ⟩) ⊢ Dec⟨ &ᴰ Y A ⟩
  dec-&ᴰL Y A ys complete m d = out (findΠ ys complete d)
    where out : _ → Dec⟨ &ᴰ Y A ⟩ m
          out (inl h)       = inl h
          out (inr (y , k)) = inr λ f → k (f y)
