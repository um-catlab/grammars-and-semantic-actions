{- WHAT WEAKENING COSTS. `A ⊗ B ⊢ A` is not a term of this calculus: `_⊢_`
   preserves the index and the projection does not. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Passes.Affine where

open import Cubical.Data.Bool using (false)
open import Cubical.Data.Empty as E using (⊥)
open import Cubical.Data.Sigma
open import Cubical.Foundations.Prelude
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.CarrierMap
open import TheoryGrammar.Instances.Lambda.Base
open import TheoryGrammar.Instances.Lambda.Fibered
open import TheoryGrammar.Instances.Lambda.Signature

module Affine (Name : Type₀) where

  open LamBase Name

  -- PRIMITIVE (carrier map). Carrier maps are external by definition:
  -- `ModelHom.hom` is an arbitrary function on the carrier.
  funPart argPart : Raw → Raw
  funPart (var n)   = var n
  funPart (app u _) = u
  funPart (lam n t) = lam n t
  argPart (var n)   = var n
  argPart (app _ v) = v
  argPart (lam n t) = lam n t

  funCM argCM : CarrierMap λFib
  funCM .hom nm n = n
  funCM .hom tm   = funPart
  argCM .hom nm n = n
  argCM .hom tm   = argPart

  module Fun = Along funCM
  module Arg = Along argCM

  -- The two weakenings, as terms over the projections.

  ⊗-weaken : {A B : TmG} → AppG A B ⊢ Fun.pull A
  ⊗-weaken = app-elim λ _ _ a _ → a

  ⊗-weaken₂ : {A B : TmG} → AppG A B ⊢ Arg.pull B
  ⊗-weaken₂ = app-elim λ _ _ _ b → b

  -- ... and why they are not rules: the projections lose splittings.

  private
    noApp : (x : Name) → IsApp (var x) → ⊥
    noApp x ()

  -- `funPart` maps `app (var x) (var x)` to `var x`, which is not an
  -- application: so an `appOp`-splitting of the source has no image,
  -- and `push⊗` is not available.
  ¬funSplitPres : (x : Name) → SplitPresAt funCM appOp → ⊥
  ¬funSplitPres x P =
    noApp x (P .homSplit (app (var x) (var x)) (mkApp (var x) (var x)))

  ¬argSplitPres : (x : Name) → SplitPresAt argCM appOp → ⊥
  ¬argSplitPres x P =
    noApp x (P .homSplit (app (var x) (var x)) (mkApp (var x) (var x)))

  -- Reflection fails too: the splitting of `funPart m` constrains only the
  -- function part, so the argument slot is unconstrained.
  ¬funReflects : (x : Name) → Fun.ReflectsSplitAt appOp → ⊥
  ¬funReflects x R
    with R (app (app (var x) (var x)) (lam x (var x))) (mkApp (var x) (var x))
  ... | mkApp _ _ , e = argSlotUnconstrained (e false)
    where
    -- what the argument slot is forced to be, and is not
    argSlotUnconstrained : (var x) Eq.≡ lam x (var x) → ⊥
    argSlotUnconstrained ()
