{-# OPTIONS --lossy-unification #-}
{- `_&_` is the binary product in `|GRAMMAR| ℓ` (Term.Category).

   `BinProducts C = ∀ cc' → UniversalElement C (BinProductProf ⟅ cc' ⟆)`.
   `BinProductProf ⟅ (A , B) ⟆` is the presheaf `Γ ↦ C[Γ,A] × C[Γ,B]`; the
   universal element has vertex `A & B`, element `(π₁ , π₂)`, and the inverse to
   "compose with the element" is `_,&_`, with β/η from the `&` laws.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

module Grammar.Product.Binary.AsPrimitive.BinProduct (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Limits.BinProduct.More

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Product.Binary.AsPrimitive.Base Alphabet
open import Grammar.Product.Binary.AsPrimitive.Properties Alphabet
open import Term.Base Alphabet
open import Term.Category Alphabet

private
  variable
    ℓ : Level

open Category
open Functor
open UniversalElement

&SetGrammar : SetGrammar ℓ → SetGrammar ℓ → SetGrammar ℓ
&SetGrammar A B =
  (A .fst & B .fst) , isSetGrammar& (A .snd) (B .snd)

module _ (A B : SetGrammar ℓ) where
  private
    P = BinProductProf (|GRAMMAR| ℓ) ⟅ (A , B) ⟆

  &-UniversalElement : UniversalElement (|GRAMMAR| ℓ) P
  &-UniversalElement .vertex = &SetGrammar A B
  &-UniversalElement .element = π₁ , π₂
  &-UniversalElement .universal Γ =
    isoToIsEquiv (iso
      (λ f → (π₁ ∘g f) , (π₂ ∘g f))
      (λ fg → fg .fst ,& fg .snd)
      (λ fg → ΣPathP (&-β₁ (fg .fst) (fg .snd) , &-β₂ (fg .fst) (fg .snd)))
      (λ f → &-η f))

|GRAMMAR|-BinProducts : BinProducts (|GRAMMAR| ℓ)
|GRAMMAR|-BinProducts (A , B) = &-UniversalElement A B
