{- The adjunction between a tensor and its residual, at the two extreme
   arities -- the measurement this instance exists to make. var-β (arity
   Unit) refl var-η funExt over `∀ t` only fun-β (arity Bool) refl fun-η
   funExt over `∀ t` AND over the arity `⊸ᶠ-β`/`⊸ᶠ-η` are `refl`
   generically for every... -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Adjunctions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Unit

open import TheoryGrammar.Instances.Lambda.Base
open import TheoryGrammar.Instances.Lambda.Residuals

module Adjunctions (Name : Type₀) where

  open LamBase Name
  open Residuals Name

  -- the `varOp` adjunction: `VarG ⊣ Wraps`, at arity `Unit`
  module _ {P : NmG} {C : TmG} where

    var-curry : VarG P ⊢ C → P ⊢ Wraps C
    var-curry f n p _ _ = f (var n) (mkVar n , λ _ → p)

    var-uncurry : P ⊢ Wraps C → VarG P ⊢ C
    var-uncurry g = var-elim λ n p → g n p tt (λ ())

    -- `Unit` η collapses `λ _ → p` and the `SplitAt`; the empty `Rest`
    -- is discharged by the absurd lambda.  No funExt.
    var-β : (g : P ⊢ Wraps C) → var-curry (var-uncurry g) ≡ g
    var-β g = refl

    var-η : (f : VarG P ⊢ C) → var-uncurry (var-curry f) ≡ f
    var-η f = funExt λ _ → funExt λ { (mkVar n , h) → refl }

    var-UP : Iso (VarG P ⊢ C) (P ⊢ Wraps C)
    var-UP .Iso.fun = var-curry
    var-UP .Iso.inv = var-uncurry
    var-UP .Iso.sec = var-β
    var-UP .Iso.ret = var-η

  -- the `appOp` adjunction at its function slot: `AppG - B ⊣ - ⟜ᵃ B`,
  -- at arity `Bool`
  module _ {A C : TmG} {B : TmG} where

    fun-curry : AppG A B ⊢ C → A ⊢ (C ⟜ᵃ B)
    fun-curry f u a v h = f (app u v) (mkApp u v , λ { true → a ; false → h tt })

    fun-uncurry : A ⊢ (C ⟜ᵃ B) → AppG A B ⊢ C
    fun-uncurry g = app-elim λ u v a b → g u a v (λ _ → b)

    fun-β : (g : A ⊢ (C ⟜ᵃ B)) → fun-curry (fun-uncurry g) ≡ g
    fun-β g = refl

    -- the extra funExt, over the arity: `Bool` has no η
    fun-η : (f : AppG A B ⊢ C) → fun-uncurry (fun-curry f) ≡ f
    fun-η f = funExt λ _ → funExt λ { (mkApp u v , h) →
      cong (λ k → f (app u v) (mkApp u v , k))
           (funExt λ { true → refl ; false → refl }) }

    fun-UP : Iso (AppG A B ⊢ C) (A ⊢ (C ⟜ᵃ B))
    fun-UP .Iso.fun = fun-curry
    fun-UP .Iso.inv = fun-uncurry
    fun-UP .Iso.sec = fun-β
    fun-UP .Iso.ret = fun-η
