{-# OPTIONS --lossy-unification #-}
{- `⊕ᴰ` is the X-indexed coproduct in `|GRAMMAR| ℓ` (Term.Category). c-c-l has
   no `IndexedCoProduct`, so we recapture it as a c-c-l `IndexedProduct` in the
   opposite category `(|GRAMMAR| ℓ) ^op`.

   `ΠTy C c⟨x⟩ = UniversalElement C (ΠTyPsh (λ x → C [-, c⟨x⟩ x ]))`. For
   `C = (|GRAMMAR| ℓ) ^op` this presheaf is `Γ ↦ ∀ x → c⟨x⟩ x ⊢ Γ`. The
   universal element has vertex `⊕ᴰ`, element the injections `σ`, and the
   inverse to "compose with the element" is `⊕ᴰ-elim`, with β componentwise
   `refl` and η from `⊕ᴰ≡`.

   Restrictions:
   * Level uniformity: the index `X : Type ℓ` lives at the same level `ℓ` as the
     grammars (so the vertex `⊕ᴰ`, at `ℓ-max ℓ ℓ ≡ ℓ`, is again an object).
   * The coproduct vertex `⊕ᴰ` is set-valued only when `X` is an `hSet`
     (`isSetGrammar⊕ᴰ` needs `isSet X`). Hence — unlike the product side — we do
     NOT get a full `IndexedProducts ((|GRAMMAR| ℓ) ^op) ℓ` (which would quantify
     over *all* `X : Type ℓ`); we provide the `ΠTy` for `hSet` indices instead.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

module Grammar.Sum.Indexed.Universal (Alphabet : hSet ℓ-zero) where

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Opposite
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Limits.IndexedProduct.Base

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Sum.Base Alphabet
open import Grammar.Sum.Properties Alphabet
open import Term.Base Alphabet
open import Term.Category Alphabet

private
  variable
    ℓ : Level

open Category
open Functor
open UniversalElement

⊕ᴰSetGrammar : {X : Type ℓ} → isSet X → (X → SetGrammar ℓ) → SetGrammar ℓ
⊕ᴰSetGrammar isSetX c =
  (⊕ᴰ λ x → ⟨ c x ⟩) , isSetGrammar⊕ᴰ isSetX (λ x → c x .snd)

module _ {X : Type ℓ} (isSetX : isSet X) (c : X → SetGrammar ℓ) where
  ⊕ᴰ-ΠTy : ΠTy ((|GRAMMAR| ℓ) ^op) c
  ⊕ᴰ-ΠTy .vertex = ⊕ᴰSetGrammar isSetX c
  ⊕ᴰ-ΠTy .element x = σ x
  ⊕ᴰ-ΠTy .universal Γ =
    isoToIsEquiv (iso
      (λ f x → f ∘g σ x)
      (λ g → ⊕ᴰ-elim g)
      (λ g → funExt (λ x → refl))    -- β: ⊕ᴰ-elim g ∘g σ x ≡ g x  (refl)
      (λ f → ⊕ᴰ≡ _ f (λ x → refl)))  -- η: ⊕ᴰ-elim (λ x → f ∘g σ x) ≡ f

-- Indexed coproducts of `|GRAMMAR| ℓ` over `hSet` indices, presented as the
-- dual (`^op`) indexed products.
|GRAMMAR|-IndexedCoProducts :
  (X : hSet ℓ) (c : X .fst → SetGrammar ℓ) → ΠTy ((|GRAMMAR| ℓ) ^op) c
|GRAMMAR|-IndexedCoProducts X c = ⊕ᴰ-ΠTy (X .snd) c
