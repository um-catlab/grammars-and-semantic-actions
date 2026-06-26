{-# OPTIONS --lossy-unification #-}
{- `_⊕_` is the binary coproduct in `|GRAMMAR| ℓ` (Term.Category), and the
   bifunctor on `|GRAMMAR|`.

   `BinCoProducts C = BinProducts (C ^op)`: the coproduct `A ⊕ B` is the product
   in the opposite category — vertex `A ⊕ B`, "projections" `inl`/`inr` (which in
   `C ^op` are arrows into the vertex), pairing `⊕-elim`.  The functorial action
   is `_,⊕p_`.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

module Grammar.Sum.Binary.AsPrimitive.BinCoProduct (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Opposite
open import Cubical.Categories.Instances.BinProduct using (_×C_)
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Limits.BinProduct.More

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Sum.Binary.AsPrimitive.Base Alphabet
open import Grammar.Sum.Binary.AsPrimitive.Properties Alphabet
open import Term.Base Alphabet
open import Term.Category Alphabet

private
  variable
    ℓ : Level

open Category
open Functor
open UniversalElement

⊕SetGrammar : SetGrammar ℓ → SetGrammar ℓ → SetGrammar ℓ
⊕SetGrammar A B =
  (A .fst ⊕ B .fst) , isSetGrammar⊕ (A .snd) (B .snd)

module _ (A B : SetGrammar ℓ) where
  private
    Cop = (|GRAMMAR| ℓ) ^op
    P = BinProductProf Cop ⟅ (A , B) ⟆

  ⊕-UniversalElement : UniversalElement Cop P
  ⊕-UniversalElement .vertex = ⊕SetGrammar A B
  ⊕-UniversalElement .element = inl , inr
  ⊕-UniversalElement .universal Γ =
    isoToIsEquiv (iso
      -- a Cop-arrow Γ ⟶ A⊕B is a term A⊕B ⊢ Γ
      (λ f → (f ∘g inl) , (f ∘g inr))
      (λ fg → ⊕-elim (fg .fst) (fg .snd))
      (λ fg → ΣPathP (⊕-βl (fg .fst) (fg .snd) , ⊕-βr (fg .fst) (fg .snd)))
      (λ f → ⊕-η f))

|GRAMMAR|-BinCoProducts : BinCoProducts (|GRAMMAR| ℓ)
|GRAMMAR|-BinCoProducts (A , B) = ⊕-UniversalElement A B

-- The coproduct is a bifunctor (functorial action `_,⊕p_`).
⊕Bifunctor : Functor (|GRAMMAR| ℓ ×C |GRAMMAR| ℓ) (|GRAMMAR| ℓ)
⊕Bifunctor .F-ob (A , B) = (A .fst ⊕ B .fst) , isSetGrammar⊕ (A .snd) (B .snd)
⊕Bifunctor .F-hom (f , g) = f ,⊕p g
⊕Bifunctor .F-id          = id,⊕id≡id
⊕Bifunctor .F-seq (f , g) (f' , g') = sym ⊕p-seq
