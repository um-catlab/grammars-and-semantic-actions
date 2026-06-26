{- A strictly-positive code is a semantic functor.

   From a single-sorted code `F : SPFunctor Unit*` (set-valued) we build the
   endofunctor on `|GRAMMAR|` whose object action is `A ↦ ⟦ F ⟧ A`, morphism
   action is `map F`, and whose functor laws are exactly `map-id` / `map-∘`.
   (Its initial algebra is the inductive grammar `μ`; see
   Grammar.Inductive.InitialAlgebra.)
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Inductive.SemanticFunctor (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Unit
open import Cubical.Categories.Category
open import Cubical.Categories.Functor

open import Grammar Alphabet
open import Grammar.HLevels.Base Alphabet
open import Term.Category Alphabet
open import Term Alphabet

private
  variable
    ℓ : Level

open Functor

SPF→Functor : (F : SPFunctor (Unit* {ℓ})) → isSetValued F
            → Functor (|GRAMMAR| ℓ) (|GRAMMAR| ℓ)
SPF→Functor F isSetValF .F-ob A =
  ⟦ F ⟧ (λ _ → A .fst) , isSet⟦F⟧ F isSetValF (λ _ → A)
SPF→Functor F isSetValF .F-hom f       = map F (λ _ → f)
SPF→Functor F isSetValF .F-id          = map-id F
SPF→Functor F isSetValF .F-seq f g     = map-∘ F (λ _ → g) (λ _ → f)
