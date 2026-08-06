{-
  DISTRIBUTIVITY OF THE INDEXED SUM, internally.

  `⊕ᴰ Y` commutes with `⊕` and with `&` on both sides.  Every proof is a
  composite of `Rules`' intro/elim; the direction that has to move an
  index OUT of a conjunct is the same trick `dist&` uses -- eliminate
  under a `⇒` and uncurry -- so no case split on a sum appears anywhere.

  This is what lets a synthesis grammar `⊕ᴰ Ty (λ A → ...)` be pushed
  through the unfolding of a judgment without ever matching on it.
-}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Distributive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import TheoryGrammar.Base
open import TheoryGrammar.Rules
open import TheoryGrammar.Decidable.Additive

private variable ℓS ℓ ℓ' ℓX ℓA ℓB ℓC ℓD ℓY : Level

module Dist {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (M : Model σ ℓX) where

  open Notation M
  open Rules M
  open DecAdd M using (&-swap; dist&)

  private variable s : S

  -- functorial action of ⊕ᴰ
  ⊕ᴰ-map : (Y : Type ℓY) {A : Y → TheoryTy ℓA s} {B : Y → TheoryTy ℓB s}
         → (∀ y → A y ⊢ B y) → ⊕ᴰ Y A ⊢ ⊕ᴰ Y B
  ⊕ᴰ-map Y {B = B} f = ⊕ᴰ-E λ y → ⊕ᴰ-I Y {A = B} y ∘⊢ f y

  -- reindexing along a bijection of index types, in the one shape used:
  -- an iterated ⊕ᴰ is a ⊕ᴰ at the product
  module _ (Y : Type ℓY) (Z : Type ℓY) {A : Y → Z → TheoryTy ℓA s} where

    ⊕ᴰ-swap : ⊕ᴰ Y (λ y → ⊕ᴰ Z (λ z → A y z)) ⊢ ⊕ᴰ Z (λ z → ⊕ᴰ Y (λ y → A y z))
    ⊕ᴰ-swap = ⊕ᴰ-E λ y → ⊕ᴰ-E λ z →
                ⊕ᴰ-I Z {A = λ z' → ⊕ᴰ Y (λ y' → A y' z')} z
                ∘⊢ ⊕ᴰ-I Y {A = λ y' → A y' z} y

  -- ⊕ᴰ over ⊕
  module _ (Y : Type ℓY) {B : Y → TheoryTy ℓB s} {C : Y → TheoryTy ℓC s} where

    ⊕ᴰ-⊕-out : ⊕ᴰ Y (λ y → B y ⊕ C y) ⊢ (⊕ᴰ Y B ⊕ ⊕ᴰ Y C)
    ⊕ᴰ-⊕-out = ⊕ᴰ-E λ y → ⊕-E (⊕-I₁ ∘⊢ ⊕ᴰ-I Y {A = B} y)
                              (⊕-I₂ ∘⊢ ⊕ᴰ-I Y {A = C} y)

    ⊕ᴰ-⊕-in : (⊕ᴰ Y B ⊕ ⊕ᴰ Y C) ⊢ ⊕ᴰ Y (λ y → B y ⊕ C y)
    ⊕ᴰ-⊕-in = ⊕-E (⊕ᴰ-E λ y → ⊕ᴰ-I Y {A = λ y' → B y' ⊕ C y'} y ∘⊢ ⊕-I₁)
                  (⊕ᴰ-E λ y → ⊕ᴰ-I Y {A = λ y' → B y' ⊕ C y'} y ∘⊢ ⊕-I₂)

  -- ⊕ᴰ over &, with the constant factor on the left
  module _ (Y : Type ℓY) {A : TheoryTy ℓA s} {P : Y → TheoryTy ℓB s} where

    ⊕ᴰ-&-out : ⊕ᴰ Y (λ y → A & P y) ⊢ (A & ⊕ᴰ Y P)
    ⊕ᴰ-&-out = &-I (⊕ᴰ-E λ _ → &-E₁) (⊕ᴰ-E λ y → ⊕ᴰ-I Y {A = P} y ∘⊢ &-E₂)

    ⊕ᴰ-&-in : (A & ⊕ᴰ Y P) ⊢ ⊕ᴰ Y (λ y → A & P y)
    ⊕ᴰ-&-in =
      Iso.inv ⇒-UP (⊕ᴰ-E λ y → ⇒-I (⊕ᴰ-I Y {A = λ y' → A & P y'} y ∘⊢ &-swap))
      ∘⊢ &-swap

  -- the four-way distribution, from `dist&` twice
  dist&r : {A : TheoryTy ℓA s} {C : TheoryTy ℓC s} {D : TheoryTy ℓD s}
         → (A & (C ⊕ D)) ⊢ ((A & C) ⊕ (A & D))
  dist&r = ⊕-E (⊕-I₁ ∘⊢ &-swap) (⊕-I₂ ∘⊢ &-swap) ∘⊢ (dist& ∘⊢ &-swap)

  dist&₂ : {A : TheoryTy ℓA s} {B : TheoryTy ℓB s}
           {C : TheoryTy ℓC s} {D : TheoryTy ℓD s}
         → ((A ⊕ B) & (C ⊕ D))
         ⊢ (((A & C) ⊕ (A & D)) ⊕ ((B & C) ⊕ (B & D)))
  dist&₂ = ⊕-E (⊕-I₁ ∘⊢ dist&r) (⊕-I₂ ∘⊢ dist&r) ∘⊢ dist&
