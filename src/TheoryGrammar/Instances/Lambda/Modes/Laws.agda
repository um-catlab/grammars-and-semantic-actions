{- WHAT THE DSL GAVE, MEASURED. Every equation the mode development leans
   on, with its cost: ⊗-β/⊗-η curry/uncurry at a context `Fibered` .....
   refl ⊸-η `⊸ᶠ` at the canonical focus ............. refl
   ⟜-β-{ord,lin,rel} `⟜-app ∘ ⟜-lam` ....... refl, all three
   ⟜-η-{ord,lin,rel} `⟜-lam ∘ ⟜-app` .......... -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Modes.Laws where

open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.List.Properties using (¬nil≡cons; cons-inj₁)
open import Cubical.Data.Sigma
open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary.Base using (Discrete)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Fibered
open import TheoryGrammar.Instances.Lambda.Modes.Ctx
open import TheoryGrammar.Instances.Lambda.Modes.Instances

import TheoryGrammar.Instances.Bags.Base as Bg

module Laws (Name : Type₀) (_≟_ : Discrete Name) where

  open Modes Name _≟_
  open Bg Name using (Ilv; nil; left; right)

  -- refl. The multiplicative and residual universal properties survive
  -- instantiation at a context `Fibered`: neither needs a pattern match.

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

  -- The residual at a REPRESENTABLE, forward direction, at each of the
  -- three substrates.

  ⟜-β-ord : (B : Ord.CtxG) (Δ Γ : Ord.Ctx) (b : Ord.shift B Δ Γ)
          → Ord.⟜-app B Δ Γ (Ord.⟜-lam B Δ Γ b) ≡ b
  ⟜-β-ord = Ord.⟜-β

  ⟜-β-lin : (B : Lin.CtxG) (Δ Γ : Lin.Ctx) (b : Lin.shift B Δ Γ)
          → Lin.⟜-app B Δ Γ (Lin.⟜-lam B Δ Γ b) ≡ b
  ⟜-β-lin = Lin.⟜-β

  ⟜-β-rel : (B : Rel.CtxG) (Δ Γ : Rel.Ctx) (b : Rel.shift B Δ Γ)
          → Rel.⟜-app B Δ Γ (Rel.⟜-lam B Δ Γ b) ≡ b
  ⟜-β-rel = Rel.⟜-β

  -- funExt, and the reason is not the substrate: `⟜-η` equates two
  -- FUNCTIONS of the rest-tuple, so extensionality is the statement's own
  -- cost, not the residual's.

  ⟜-η-ord : (B : Ord.CtxG) (Δ Γ : Ord.Ctx) (h : (B Ord.⟜ᶜ Δ) Γ)
          → Ord.⟜-lam B Δ Γ (Ord.⟜-app B Δ Γ h) ≡ h
  ⟜-η-ord = Ord.⟜-η

  ⟜-η-lin : (B : Lin.CtxG) (Δ Γ : Lin.Ctx) (h : (B Lin.⟜ᶜ Δ) Γ)
          → Lin.⟜-lam B Δ Γ (Lin.⟜-app B Δ Γ h) ≡ h
  ⟜-η-lin = Lin.⟜-η

  ⟜-η-rel : (B : Rel.CtxG) (Δ Γ : Rel.Ctx) (h : (B Rel.⟜ᶜ Δ) Γ)
          → Rel.⟜-lam B Δ Γ (Rel.⟜-app B Δ Γ h) ≡ h
  ⟜-η-rel = Rel.⟜-η

  -- NEGATIVE MEASUREMENT 1: `Split` IS NOT A PROPOSITION.

  -- the two splittings of a one-name context, as WITNESSES: `x` all on
  -- the right, and `x` all on the left
  splitR splitL : (x : Name) → Il.CSplit mul (x ∷ [])
  splitR x = [] , x ∷ [] , right nil
  splitL x = x ∷ [] , [] , left nil

  splitR≢splitL : (x : Name) → splitR x ≡ splitL x → ⊥
  splitR≢splitL x p = ¬nil≡cons (cong fst p)

  -- NEGATIVE MEASUREMENT 2: `unsplit` IS FALSE AT A QUOTIENT.

  swapped : (x y : Name) → Il.fib .Split mul (y ∷ x ∷ [])
  swapped x y = (x ∷ []) , (y ∷ []) , right (left nil)

  no-unsplit : (x y : Name) → (x ≡ y → ⊥)
             → Il.point .op mul (Il.fib .parts mul (y ∷ x ∷ []) (swapped x y))
                 Eq.≡ (y ∷ x ∷ [])
             → ⊥
  no-unsplit x y x≢y e = x≢y (cons-inj₁ (Eq.eqToPath e))
