{-# OPTIONS --lossy-unification #-}
{- `_⇒_` gives the exponentials of `|GRAMMAR| ℓ` (Term.Category), so it is a CCC.

   `AllExponentiable C bp = ∀ c d →
      UniversalElement C (((C [-, c ]) , bp(- , c)) ⇒PshSmall (C [-, d ]))`.
   The exponential `c ⇒ d` has vertex `c ⇒ d`, evaluation element `⇒-app`, and
   the universal property is currying `⇒-intro` with β/η from the `⇒` laws.  The
   product structure is reused from `Grammar.Product.Binary.AsPrimitive.BinProduct`.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

module Grammar.Function.AsPrimitive.Exponential (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation hiding (_⇒_)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.Constructions.Exponential
open import Cubical.Categories.Presheaf.Constructions.BinProduct.LocalRepresentability
open import Cubical.Categories.Exponentials.Small

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Product.Binary.AsPrimitive.Base Alphabet
open import Grammar.Product.Binary.AsPrimitive.Properties Alphabet
open import Grammar.Product.Binary.AsPrimitive.BinProduct Alphabet
open import Grammar.Function.AsPrimitive.Base Alphabet
open import Term.Base Alphabet
open import Term.Category Alphabet

private
  variable
    ℓ : Level

open Category
open Functor
open NatTrans
open UniversalElement

opaque
  unfolding _⇒_
  isSetGrammar⇒ : {A : Grammar ℓ} {B : Grammar ℓ}
    → isSetGrammar B → isSetGrammar (A ⇒ B)
  isSetGrammar⇒ isSetB w = isSet→ (isSetB w)

module _ (c d : SetGrammar ℓ) where
  private
    bp = |GRAMMAR|-BinProducts {ℓ}
    -×c : BinProductsWith (|GRAMMAR| ℓ) c
    -×c = λ d' → bp (d' , c)
    P = (((|GRAMMAR| ℓ) [-, c ]) , -×c) ⇒PshSmall ((|GRAMMAR| ℓ) [-, d ])

  ⇒-Exponential : Exponential (|GRAMMAR| ℓ) c d -×c
  ⇒-Exponential .vertex = (c .fst ⇒ d .fst) , isSetGrammar⇒ (d .snd)
  ⇒-Exponential .element = ⇒-app
  ⇒-Exponential .universal Γ =
    subst isEquiv (funExt (λ f → sym (action≡ f))) currying-isEquiv
    where
    G : Functor (|GRAMMAR| ℓ) (|GRAMMAR| ℓ)
    G = LRPsh→Functor (((|GRAMMAR| ℓ) [-, c ]) , -×c)

    -- The presheaf action of ⇒-app on f : Γ ⊢ (c⇒d) coincides with
    -- the ⇒-intro⁻ of f.  The action is ⇒-app ∘g (G .F-hom f), and
    -- G .F-hom f equals the &-pairing ((f ∘g π₁) ,& π₂) by the
    -- BinProduct universal property of (Γ' & c).
    module bpΓ = BinProductNotation (-×c (⇒-Exponential .vertex))

    Ghom≡ : (f : ⟨ Γ ⟩ ⊢ ⟨ ⇒-Exponential .vertex ⟩)
      → G .F-hom f ≡ &-intro (f ∘g π₁) π₂
    Ghom≡ f = &≡ _ _
      (πLRF (((|GRAMMAR| ℓ) [-, c ]) , -×c) .N-hom f
        ∙ sym (&-β₁ (f ∘g π₁) π₂))
      (bpΓ.×β₂ ∙ sym (&-β₂ (f ∘g π₁) π₂))

    action≡ : (f : ⟨ Γ ⟩ ⊢ ⟨ ⇒-Exponential .vertex ⟩)
      → (⇒-app ∘ᴾ⟨ P ⟩ f) ≡ ⇒-intro⁻ f
    action≡ f = cong (⇒-app ∘g_) (Ghom≡ f)

    currying-isEquiv : isEquiv {A = ⟨ Γ ⟩ ⊢ ⟨ ⇒-Exponential .vertex ⟩} ⇒-intro⁻
    currying-isEquiv = isoToIsEquiv (iso ⇒-intro⁻ ⇒-intro ⇒-β ⇒-η)

|GRAMMAR|-AllExponentiable :
  AllExponentiable (|GRAMMAR| ℓ) (|GRAMMAR|-BinProducts {ℓ})
|GRAMMAR|-AllExponentiable c d = ⇒-Exponential c d
