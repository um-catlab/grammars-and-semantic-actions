{- SUBGRAMMARS: comprehension, and nothing else. -}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Subgrammar where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence using (hPropExt)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import TheoryGrammar.Base

private variable ℓS ℓX ℓA ℓB ℓ : Level

module SubG {S : Type ℓS} (X : S → Type ℓX) where

  open CarrierNotation X

  -- the subobject classifier, pointwise
  Ω : {s : S} → TheoryTy (ℓ-suc ℓ) s
  Ω _ = hProp _

  module _ {s : S} {A : TheoryTy ℓA s} (p : A ⊢ Ω {ℓ = ℓ}) where

    Compr : TheoryTy (ℓ-max ℓA ℓ) s
    Compr w = Σ[ x ∈ A w ] ⟨ p w x ⟩

    -- the inclusion, and the fact that `p` holds on its image.  The
    -- latter is `.snd` -- upstream it was `sub-π-pf`, a `Σ≡Prop` over
    -- an `hPropExt`.
    π : Compr ⊢ A
    π _ = fst

    πHolds : (w : X s) (x : Compr w) → ⟨ p w (π w x) ⟩
    πHolds w x = x .snd

    -- what it takes to factor through the subgrammar
    Holds : {B : TheoryTy ℓB s} → B ⊢ A → Type (ℓ-max ℓX (ℓ-max ℓB ℓ))
    Holds {B = B} f = (w : X s) (x : B w) → ⟨ p w (f w x) ⟩

    intro : {B : TheoryTy ℓB s} (f : B ⊢ A) → Holds f → B ⊢ Compr
    intro f h w x = f w x , h w x

    -- THEOREM.  The universal property, with both round trips `refl`.

    β : {B : TheoryTy ℓB s} (f : B ⊢ A) (h : Holds f)
      → (π ∘⊢ intro f h) ≡ f
    β f h = refl

    η : {B : TheoryTy ℓB s} (g : B ⊢ Compr)
      → intro (π ∘⊢ g) (λ w x → g w x .snd) ≡ g
    η g = refl

    Compr-UP : {B : TheoryTy ℓB s}
           → Iso (B ⊢ Compr) (Σ[ f ∈ B ⊢ A ] Holds f)
    Compr-UP .Iso.fun g       = (π ∘⊢ g) , (λ w x → g w x .snd)
    Compr-UP .Iso.inv (f , h) = intro f h
    Compr-UP .Iso.sec _       = refl
    Compr-UP .Iso.ret _       = refl

    -- ... and the bridge to the equational phrasing, needed ONCE.

    trueΩ : {B : TheoryTy ℓB s} → B ⊢ Ω {ℓ = ℓ}
    trueΩ _ _ = Unit* , isPropUnit*

    toEqn : {B : TheoryTy ℓB s} (f : B ⊢ A)
          → Holds f → (λ w x → p w (f w x)) ≡ trueΩ {B = B}
    toEqn f h = funExt λ w → funExt λ x →
      Σ≡Prop (λ _ → isPropIsProp)
             (hPropExt (p w (f w x) .snd) isPropUnit* (λ _ → tt*) (λ _ → h w x))

    ofEqn : {B : TheoryTy ℓB s} (f : B ⊢ A)
          → (λ w x → p w (f w x)) ≡ trueΩ {B = B} → Holds f
    ofEqn f e w x = transport (sym (cong fst (funExt⁻ (funExt⁻ e w) x))) tt*

-- The canonical source of subgrammars: an equalizer.  `Rules.agda`
-- already has equalizers; this says they are comprehensions, which is
-- the content of `Grammar/Subgrammar/Equalizer.agda`.
module EqualizerSub {S : Type ℓS} (X : S → Type ℓX) where

  open CarrierNotation X
  open SubG X

  module _ {s : S} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s}
           (setB : (w : X s) → isSet (B w)) (f g : A ⊢ B) where

    eqΩ : A ⊢ Ω {ℓ = ℓB}
    eqΩ w x = (f w x ≡ g w x) , setB w _ _

    Eq⊆ : TheoryTy (ℓ-max ℓA ℓB) s
    Eq⊆ = Compr eqΩ

    -- the equalizer property, immediately: the two maps agree on it
    eqHolds : (f ∘⊢ π eqΩ) ≡ (g ∘⊢ π eqΩ)
    eqHolds = funExt λ w → funExt λ x → x .snd
