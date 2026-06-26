{- The linear product `_⊗_` is a bifunctor on `|GRAMMAR|`.

   It is already a bifunctor: it is the monoidal product of the monoidal
   category `GRAMMAR` (see Term.Category).
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.LinearProduct.Bifunctor (Alphabet : hSet ℓ-zero) where

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Instances.BinProduct using (_×C_)

open import Term.Category Alphabet

private
  variable
    ℓ : Level

⊗Bifunctor : Functor (|GRAMMAR| ℓ ×C |GRAMMAR| ℓ) (|GRAMMAR| ℓ)
⊗Bifunctor {ℓ} = MonoidalCategory.─⊗─ (GRAMMAR ℓ)
