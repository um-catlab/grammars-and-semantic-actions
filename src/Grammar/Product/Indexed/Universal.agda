{-# OPTIONS --lossy-unification #-}
{- `&ᴰ` is the X-indexed product in `|GRAMMAR| ℓ` (Term.Category), recaptured
   as a c-c-l `IndexedProduct`.

   `ΠTy C c⟨x⟩ = UniversalElement C (ΠTyPsh (λ x → C [-, c⟨x⟩ x ]))`, where
   `ΠTyPsh ⟨-⟩` is the presheaf `Γ ↦ ∀ x → C[Γ , c⟨x⟩ x]`. The universal
   element has vertex `&ᴰ`, element the projections `π`, and the inverse to
   "compose with the element" is `&ᴰ-intro`, with β componentwise `refl` and η
   from `&ᴰ≡`.

   Level uniformity: the index `X : Type ℓ` lives at the *same* level `ℓ` as the
   grammars, so the vertex `&ᴰ` (at `ℓ-max ℓ ℓ ≡ ℓ`) is again an object of
   `|GRAMMAR| ℓ`. This is exactly `IndexedProducts (|GRAMMAR| ℓ) ℓ`.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

module Grammar.Product.Indexed.Universal (Alphabet : hSet ℓ-zero) where

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Limits.IndexedProduct.Base

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Product.Base Alphabet
open import Grammar.Product.Properties Alphabet
open import Term.Base Alphabet
open import Term.Category Alphabet

private
  variable
    ℓ : Level

open Category
open Functor
open UniversalElement

&ᴰSetGrammar : {X : Type ℓ} → (X → SetGrammar ℓ) → SetGrammar ℓ
&ᴰSetGrammar c = (&ᴰ λ x → ⟨ c x ⟩) , isSetGrammar&ᴰ (λ x → c x .snd)

module _ {X : Type ℓ} (c : X → SetGrammar ℓ) where
  &ᴰ-ΠTy : ΠTy (|GRAMMAR| ℓ) c
  &ᴰ-ΠTy .vertex = &ᴰSetGrammar c
  &ᴰ-ΠTy .element x = π x
  &ᴰ-ΠTy .universal Γ =
    isoToIsEquiv (iso
      (λ f x → π x ∘g f)
      (λ g → &ᴰ-intro g)
      (λ g → funExt (λ x → refl))    -- β: π x ∘g &ᴰ-intro g ≡ g x  (refl)
      (λ f → &ᴰ≡ _ f (λ x → refl)))  -- η: &ᴰ-intro (λ x → π x ∘g f) ≡ f

|GRAMMAR|-IndexedProducts : IndexedProducts (|GRAMMAR| ℓ) ℓ
|GRAMMAR|-IndexedProducts X c = &ᴰ-ΠTy c
