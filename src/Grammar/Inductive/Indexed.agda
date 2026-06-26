{- An indexed inductive type is basically just a mutually inductive type -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Inductive.Indexed (Alphabet : hSet ℓ-zero)where

open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Sum.Base Alphabet
open import Grammar.Product.Base Alphabet
open import Grammar.LinearProduct.Base Alphabet
open import Grammar.Lift Alphabet
open import Term.Base Alphabet

open import Grammar.Inductive.Functor Alphabet public

private
  variable ℓA ℓB ℓX : Level

module _ where
  module _ {X : Type ℓX} where
    -- NOTE: this is only needed because ⊗ is opaque. If it's not
    -- opaque this passes the positivity check.
    -- https://github.com/agda/agda/issues/6970
    {-# NO_POSITIVITY_CHECK #-}
    data μ (F : X → SPFunctor X) x : Grammar ℓX where
      roll : ⟦ F x ⟧ (μ F) ⊢ μ F x

  module _ {X : Type ℓX} (F : X → SPFunctor X) where
    -- `initialAlgebra`/`rec`/`recHomo`/`ind` are the computational recursor.
    -- The old `Algebra`/`Homomorphism` aliases are inlined here (they were
    -- removed from `Grammar.Inductive.Functor`); the categorical packaging is
    -- provided semantically by `Grammar.Inductive.Semantic`/`.Algebra`.
    initialAlgebra : ∀ x → ⟦ F x ⟧ (μ F) ⊢ μ F x
    initialAlgebra = λ x → roll

    module _ {A : X → Grammar ℓA} (α : ∀ x → ⟦ F x ⟧ A ⊢ A x) where
      -- The universal-property type of `rec`: an algebra homomorphism out of
      -- the initial algebra `(μ F , roll)` into the algebra `(A , α)`.
      RecHomo : Type _
      RecHomo = Σ[ ϕ ∈ (∀ x → μ F x ⊢ A x) ] (∀ x → ϕ x ∘g roll ≡ α x ∘g map (F x) ϕ)

      {-# TERMINATING #-}
      recHomo : RecHomo
      recHomo .fst x w (roll ._ z) =
        α x w (map (F x) (recHomo .fst) w z)
      recHomo .snd x = refl

      rec : ∀ x → (μ F x) ⊢ A x
      rec = recHomo .fst

      module _ (ϕ : RecHomo) where
        private
          {-# TERMINATING #-}
          μ-η' : ∀ x w z → ϕ .fst x w z ≡ rec x w z
          μ-η' x w (roll _ z) =
            (λ i → ϕ .snd x i w z)
            ∙ λ i → α x w (map (F x) (λ x w z → μ-η' x w z i) w z)
        μ-η : ϕ .fst ≡ rec
        μ-η = funExt (λ x → funExt λ w → funExt λ z → μ-η' x w z)

      ind : (ϕ ϕ' : RecHomo) → ϕ .fst ≡ ϕ' .fst
      ind ϕ ϕ' = μ-η ϕ ∙ sym (μ-η ϕ')

      ind' : ∀ (ϕ ϕ' : RecHomo) → ∀ x → ϕ .fst x ≡ ϕ' .fst x
      ind' ϕ ϕ' = funExt⁻ (ind ϕ ϕ')

    ind-id : ∀ (ϕ : RecHomo initialAlgebra) → ϕ .fst ≡ (λ x → id)
    ind-id ϕ = ind initialAlgebra ϕ
      ((λ x → id) , λ x → cong (roll ∘g_) (sym (map-id (F x))))

    ind-id' : ∀ (ϕ : RecHomo initialAlgebra) x → ϕ .fst x ≡ id
    ind-id' ϕ x = funExt⁻ (ind-id ϕ) x

    -- A retraction of `rec` onto the initial algebra is the identity: if
    -- `(gmap , gpf)` is an algebra homomorphism `(A , α) → (μ F , roll)`, then
    -- `gmap ∘g rec α ≡ id`.  This is the uniqueness principle for `μ F`,
    -- packaged so callers need not mention the (now-deleted) `compHomo`.
    module _ {A : X → Grammar ℓA} (α : ∀ x → ⟦ F x ⟧ A ⊢ A x)
      (gmap : ∀ x → A x ⊢ μ F x)
      (gpf : ∀ x → gmap x ∘g α x ≡ roll ∘g map (F x) gmap) where
      private
        rec-section-homo : RecHomo initialAlgebra
        rec-section-homo .fst x = gmap x ∘g rec α x
        rec-section-homo .snd x =
          cong (gmap x ∘g_) (recHomo α .snd x)
          ∙ cong (_∘g map (F x) (rec α)) (gpf x)
          ∙ cong (roll ∘g_) (sym (map-∘ (F x) gmap (rec α)))
      rec-section : ∀ x → gmap x ∘g rec α x ≡ id
      rec-section = ind-id' rec-section-homo

    unroll : ∀ x → μ F x ⊢ ⟦ F x ⟧ (μ F)
    unroll x w (roll .w z) = z

    -- Lambek's lemma for indexed inductives
    unroll' : ∀ x → μ F x ⊢ ⟦ F x ⟧ (μ F)
    unroll' = rec {A = λ x → ⟦ F x ⟧ (μ F)} alg where
      alg : ∀ x → ⟦ F x ⟧ (λ x → ⟦ F x ⟧ (μ F)) ⊢ ⟦ F x ⟧ (μ F)
      alg x = map (F x) (λ _ → roll)
