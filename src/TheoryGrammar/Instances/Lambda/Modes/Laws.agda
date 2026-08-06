{-
  WHAT THE DSL GAVE, MEASURED.

  Every equation the mode development actually leans on, with its cost:

    ⊗ˢ β/η at a context promodel .............. refl
    ⊸ᶠ β/η at the canonical focus .............. refl
    ⟜ β at a representable (`⟜-app ∘ ⟜-lam`) ... refl
    ⟜ η at a representable (`⟜-lam ∘ ⟜-app`) ... funExt + Eq.J + sym-invol
    parts-split (in the three promodel files) . funExt (Bool arity)

  And the negative measurement that forced a new generic file:
  `splitNotProp` exhibits two distinct splittings of a one-name context,
  so `DecReadable.splitProp` is FALSE for every context promodel here and
  `Decidable.Tensor.dec-⊗` is unavailable.  `Decidable.Splittings` exists
  because of this line.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Modes.Laws where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.List.Properties using (¬nil≡cons)
open import Cubical.Relation.Nullary.Base using (Discrete)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Instances.Lambda.Modes.Ctx
open import TheoryGrammar.Instances.Lambda.Modes.Instances

import TheoryGrammar.Instances.Bags.Base as Bg

module Laws (Name : Type₀) (_≟_ : Discrete Name) where

  open Modes Name _≟_
  open Bg Name using (Ilv; nil; left; right)

  -- ================================================================
  -- refl.  The multiplicative and residual universal properties survive
  -- instantiation at a context promodel: neither needs a pattern match.
  -- ================================================================

  module _ where
    open Lin

    ⊗-β : (A : Bool → CtxG) (B : CtxG) (g : MultiHomˢ mul A B)
        → curryˢ mul {A = A} {B = B} (uncurryˢ mul {A = A} {B = B} g) ≡ g
    ⊗-β A B g = refl

    ⊗-η : (A : Bool → CtxG) (B : CtxG) (f : ⊗ˢ mul A ⊢ B)
        → uncurryˢ mul {A = A} {B = B} (curryˢ mul {A = A} {B = B} f) ≡ f
    ⊗-η A B f = refl

    ⊸-η : (A : Bool → CtxG) (B : CtxG) (g : A true ⊢ ⊸ᶠ A B)
        → ⊸ᶠ-lam {A = A} {B = B} (⊸ᶠ-app {A = A} {B = B} g) ≡ g
    ⊸-η A B g = refl

    -- the residual at a REPRESENTABLE, one way: `Eq.sym Eq.refl` reduces,
    -- so plugging the hole and abstracting it again is the identity
    ⟜-β : (B : CtxG) (Δ Γ : Ctx) (b : shift B Δ Γ)
        → ⟜-app B Δ Γ (⟜-lam B Δ Γ b) ≡ b
    ⟜-β B Δ Γ b = refl

  -- ================================================================
  -- funExt.  The other way round is the only equation in the whole
  -- development that costs anything: the rest-tuple has to be identified
  -- with the representable's point, pointwise, and `Eq.sym` has to be
  -- undone.  This is the price of `⌈_⌉` being `data`-valued.
  -- ================================================================

  module _ where
    open Lin

    ⟜-η : (B : CtxG) (Δ Γ : Ctx) (h : (B ⟜ᶜ Δ) Γ)
        → ⟜-lam B Δ Γ (⟜-app B Δ Γ h) ≡ h
    ⟜-η B Δ Γ h = funExt λ f → funExt λ e → step (f tt) (e tt)
      where
      base : (y : Ctx) (p : Δ Eq.≡ y)
           → Eq.transport (λ z → B (Γ · z)) p (h (λ _ → Δ) (λ _ → Eq.refl))
             ≡ h (λ _ → y) (λ _ → Eq.sym p)
      base y p =
        Eq.J (λ y' p' →
                Eq.transport (λ z → B (Γ · z)) p' (h (λ _ → Δ) (λ _ → Eq.refl))
                ≡ h (λ _ → y') (λ _ → Eq.sym p'))
             refl p

      step : (y : Ctx) (q : y Eq.≡ Δ)
           → Eq.transport (λ z → B (Γ · z)) (Eq.sym q) (h (λ _ → Δ) (λ _ → Eq.refl))
             ≡ h (λ _ → y) (λ _ → q)
      step y q =
        base y (Eq.sym q)
        ∙ cong (λ r → h (λ _ → y) (λ _ → r)) (Eq.eqToPath (Eq.sym-invol q))

  -- ================================================================
  -- THE NEGATIVE MEASUREMENT.
  --
  -- A one-name context splits two ways, so `Split` is not a proposition
  -- and unique readability -- the hypothesis `Decidable.Tensor` runs on --
  -- fails.  The same two splittings exist for `Split3` (ordered) and, with
  -- a third, for `Ilv3` (relevant).  Deciding the tensor therefore cannot
  -- go through `DecReadable`; it goes through `DecSplittings`, whose only
  -- field is `dec-⊗`'s conclusion.
  -- ================================================================

  splitNotProp : (x : Name)
               → Path (Il.CSplit mul (x ∷ []))
                      ([] , x ∷ [] , right nil) (x ∷ [] , [] , left nil)
               → ⊥
  splitNotProp x p = ¬nil≡cons (cong fst p)
