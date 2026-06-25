open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Coinductive.Indexed (Alphabet : hSet ℓ-zero)where

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
    -- NOTE: as with μ, the NO_POSITIVITY_CHECK is only needed because ⊗ is
    -- opaque. If it's not opaque this passes the positivity check.
    -- https://github.com/agda/agda/issues/6970
    {-# NO_POSITIVITY_CHECK #-}
    record ν (F : X → SPFunctor X) (x : X) (w : String) : Type ℓX where
      coinductive
      field
        unroll : ⟦ F x ⟧ (ν F) w
    open ν public

  module _ {X : Type ℓX} (F : X → SPFunctor X) where
    finalCoalgebra : Coalgebra F (ν F)
    finalCoalgebra x w t = t .unroll

    module _ {A : X → Grammar ℓA} (α : Coalgebra F A) where
      {-# TERMINATING #-}
      corecHomo : CoHomomorphism F α finalCoalgebra
      corecHomo .fst x w a .unroll =
        map (F x) (corecHomo .fst) w (α x w a)
      corecHomo .snd x = refl

      corec : ∀ x → A x ⊢ ν F x
      corec = corecHomo .fst

      module _ (ϕ : CoHomomorphism F α finalCoalgebra) where
        private
          {-# TERMINATING #-}
          ν-η' : ∀ x w a → ϕ .fst x w a ≡ corec x w a
          ν-η' x w a i .unroll =
            ((λ j → ϕ .snd x (~ j) w a)
            ∙ (λ j → map (F x) (λ y w' a' → ν-η' y w' a' j) w (α x w a))) i
        ν-η : ϕ .fst ≡ corec
        ν-η = funExt (λ x → funExt λ w → funExt λ a → ν-η' x w a)

      coind : (ϕ ϕ' : CoHomomorphism F α finalCoalgebra) → ϕ .fst ≡ ϕ' .fst
      coind ϕ ϕ' = ν-η ϕ ∙ sym (ν-η ϕ')

      coind' : ∀ (ϕ ϕ' : CoHomomorphism F α finalCoalgebra) → ∀ x → ϕ .fst x ≡ ϕ' .fst x
      coind' ϕ ϕ' = funExt⁻ (coind ϕ ϕ')

    coind-id : ∀ (ϕ : CoHomomorphism F finalCoalgebra finalCoalgebra) → ϕ .fst ≡ idCoHomo F finalCoalgebra .fst
    coind-id ϕ = coind finalCoalgebra ϕ (idCoHomo F finalCoalgebra)

    coind-id' : ∀ (ϕ : CoHomomorphism F finalCoalgebra finalCoalgebra) x → ϕ .fst x ≡ id
    coind-id' ϕ x = funExt⁻ (coind-id ϕ) x

    rollν : ∀ x → ⟦ F x ⟧ (ν F) ⊢ ν F x
    rollν = corec {A = λ x → ⟦ F x ⟧ (ν F)} coalg where
      coalg : Coalgebra F (λ x → ⟦ F x ⟧ (ν F))
      coalg x = map (F x) finalCoalgebra
