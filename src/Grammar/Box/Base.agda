open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Box.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List

open import Grammar.Base Alphabet
open import Grammar.Derivative.String Alphabet
open import Grammar.Sum Alphabet
open import Grammar.Product Alphabet
open import Grammar.Product.Binary.AsPrimitive Alphabet
open import Grammar.Function Alphabet
open import Grammar.External.String.Tiny Alphabet
open import Term.Base Alphabet

private
  variable
    ℓA ℓB ℓC ℓD ℓX : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD

□_ : Grammar ℓA → Grammar ℓA
□ A = &[ w ∈ String ] √l-string w A

-- counit
ε□ : □ A ⊢ A
ε□ = √l-ε ∘g π []

√l-dist :
  ∀ {w : String} {X : Type ℓX} {B : X → Grammar ℓA} →
  (&[ x ∈ X ] √l-string w (B x)) ⊢ √l-string w (&[ x ∈ X ] B x)
√l-dist {w = w} =
  ⇒-intro
    (⌈⌉-⊗&ᴰ-distL⁻Eq {w = w} ∘g
      (π₂ ,& &ᴰ-intro (λ x → ⇒-app ∘g ((π x ∘g π₁) ,& π₂))))

-- comultiplication
δ : □ A ⊢ □ (□ A)
δ = &ᴰ-intro λ w → √l-dist {w = w} ∘g &ᴰ-intro λ v → √l-cat {w = w} {v = v} ∘g π (w ++ v)
