{-# OPTIONS --lossy-unification #-}
{-
  Pullbacks in `|GRAMMAR| ℓ`, built from binary products `_&_` and
  equalizers.

  The pullback of a cospan `f : A ⊢ C`, `g : B ⊢ C` is the equalizer of
  `(f ∘g π₁)` and `(g ∘g π₂)` over `A & B`:

      P ─eq-π─▶ A & B ──f ∘g π₁──▶ C
                       ──g ∘g π₂──▶

  The two projections are `pb-π₁ = π₁ ∘g eq-π` and `pb-π₂ = π₂ ∘g eq-π`,
  the square commutes by the equalizer law `eq-π-pf`, and the universal
  property comes from the `&` UMP (pair `h ,& k`) together with the
  equalizer UMP (factor through `eq-intro`).
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

module Grammar.Limits.Pullback (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Pullback

open import Grammar Alphabet
open import Grammar.HLevels.Base Alphabet using (⟨_⟩)
open import Term Alphabet
open import Term.Category Alphabet

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- The equalizer projection `eq-π` is a monomorphism (a subobject
-- inclusion): two maps into an equalizer agree as soon as their
-- composites with `eq-π` agree (the "proof" coordinate is a prop,
-- since the codomain is a set).
------------------------------------------------------------------------
module _ {A : Grammar ℓ} {B : Grammar ℓ}
  (isSetB : isSetGrammar B) (f f' : A ⊢ B) where
  opaque
    unfolding equalizer eq-π
    isMono-eq-π : isMono (eq-π f f')
    isMono-eq-π e e' p = funExt λ w → funExt λ x →
      ΣPathP ( funExt⁻ (funExt⁻ p w) x
             , isProp→PathP (λ _ → isSetB w _ _) _ _ )

------------------------------------------------------------------------
-- The pullback of a cospan, as the equalizer over the product.
------------------------------------------------------------------------
module _ {ℓ} (cspn : Cospan (|GRAMMAR| ℓ)) where
  open Cospan cspn
  open Category (|GRAMMAR| ℓ)
  open Pullback

  private
    A : Grammar ℓ
    A = ⟨ l ⟩
    B : Grammar ℓ
    B = ⟨ r ⟩
    Cg : Grammar ℓ
    Cg = ⟨ m ⟩

    f : A ⊢ Cg
    f = s₁
    g : B ⊢ Cg
    g = s₂

    F₁ F₂ : (A & B) ⊢ Cg
    F₁ = f ∘g π₁
    F₂ = g ∘g π₂

    E : Grammar ℓ
    E = equalizer F₁ F₂

    isSetE : isSetGrammar E
    isSetE =
      isSetGrammarEqualizer F₁ F₂
        (isSetGrammar& (l .snd) (r .snd)) (m .snd)

  |GRAMMAR|-Pullback : Pullback (|GRAMMAR| ℓ) cspn
  |GRAMMAR|-Pullback .pbOb = E , isSetE
  |GRAMMAR|-Pullback .pbPr₁ = π₁ ∘g eq-π F₁ F₂
  |GRAMMAR|-Pullback .pbPr₂ = π₂ ∘g eq-π F₁ F₂
  |GRAMMAR|-Pullback .pbCommutes = eq-π-pf F₁ F₂
  |GRAMMAR|-Pullback .univProp {d} hₗ hᵣ H' =
    uniqueExists hk (H₁ , H₂)
      (λ _ → isProp× (isSetHom _ _) (isSetHom _ _))
      uniq
    where
    pair : ⟨ d ⟩ ⊢ A & B
    pair = hₗ ,& hᵣ

    cone-eq : F₁ ∘g pair ≡ F₂ ∘g pair
    cone-eq =
      cong (f ∘g_) (&-β₁ hₗ hᵣ) ∙ H' ∙ cong (g ∘g_) (sym (&-β₂ hₗ hᵣ))

    hk : ⟨ d ⟩ ⊢ E
    hk = eq-intro F₁ F₂ pair cone-eq

    eqβ : eq-π F₁ F₂ ∘g hk ≡ pair
    eqβ = eq-β F₁ F₂ pair cone-eq

    H₁ : hₗ ≡ (π₁ ∘g eq-π F₁ F₂) ∘g hk
    H₁ = sym (cong (π₁ ∘g_) eqβ ∙ &-β₁ hₗ hᵣ)

    H₂ : hᵣ ≡ (π₂ ∘g eq-π F₁ F₂) ∘g hk
    H₂ = sym (cong (π₂ ∘g_) eqβ ∙ &-β₂ hₗ hᵣ)

    uniq : (hk' : ⟨ d ⟩ ⊢ E)
         → (hₗ ≡ (π₁ ∘g eq-π F₁ F₂) ∘g hk')
         × (hᵣ ≡ (π₂ ∘g eq-π F₁ F₂) ∘g hk')
         → hk ≡ hk'
    uniq hk' (H₁' , H₂') =
      isMono-eq-π (m .snd) F₁ F₂ hk hk' (eqβ ∙ sym eq-of-hk')
      where
      eq-of-hk' : eq-π F₁ F₂ ∘g hk' ≡ pair
      eq-of-hk' =
        &-η' (eq-π F₁ F₂ ∘g hk') pair
          (sym H₁' ∙ sym (&-β₁ hₗ hᵣ))
          (sym H₂' ∙ sym (&-β₂ hₗ hᵣ))

|GRAMMAR|-Pullbacks : Pullbacks (|GRAMMAR| ℓ)
|GRAMMAR|-Pullbacks = |GRAMMAR|-Pullback
