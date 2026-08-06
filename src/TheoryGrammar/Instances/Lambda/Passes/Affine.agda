{-
  WHAT WEAKENING COSTS.

  `A ⊗ B ⊢ A` is not a term of this calculus: `_⊢_` preserves the
  index and the projection does not.  What IS a term is

      AppG A B ⊢ pull A     along the carrier map `funPart`,

  the map sending an application to its function part.  So affine
  weakening is not a rule of the multiplicative fragment -- it is a
  CHANGE OF CARRIER, and the theorem below says precisely why it cannot
  be internalised: `funPart` does not preserve `appOp`-splittings, so
  `push⊗` is unavailable along it and the multiplicative fragment does
  not transport.

  `⊗-weaken` and `⊗-weaken₂` themselves are `app-elim` and nothing
  else: once the carrier map is named, the projection is definitional.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Passes.Affine where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (false)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.CarrierMap
open import TheoryGrammar.Instances.Lambda.Signature
open import TheoryGrammar.Instances.Lambda.Fibered
open import TheoryGrammar.Instances.Lambda.Base

module Affine (Name : Type₀) where

  open LamBase Name

  -- PRIMITIVE (carrier map).  Carrier maps are external by definition:
  -- `ModelHom.hom` is an arbitrary function on the carrier.  This is
  -- the boundary the calculus draws -- the map is promodel data, its
  -- action on derivations is what has to be a term.
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

  private
    module F = Along funCM
    module A = Along argCM

  -- ================================================================
  -- The two weakenings, as terms over the projections.
  -- ================================================================

  ⊗-weaken : {A B : TmG} → AppG A B ⊢ F.pull A
  ⊗-weaken = app-elim λ _ _ a _ → a

  ⊗-weaken₂ : {A B : TmG} → AppG A B ⊢ A.pull B
  ⊗-weaken₂ = app-elim λ _ _ _ b → b

  -- ================================================================
  -- ... and why they are not rules: the projections lose splittings.
  -- ================================================================

  -- `funPart` maps `app (var x) (var x)` to `var x`, which is not an
  -- application: so an `appOp`-splitting of the source has no image,
  -- and `push⊗` is not available.
  ¬funSplitPres : (x : Name) → SplitPresAt funCM appOp → ⊥
  ¬funSplitPres x P with P .homSplit (app (var x) (var x)) (mkApp (var x) (var x))
  ... | ()

  ¬argSplitPres : (x : Name) → SplitPresAt argCM appOp → ⊥
  ¬argSplitPres x P with P .homSplit (app (var x) (var x)) (mkApp (var x) (var x))
  ... | ()

  -- Reflection fails too: the splitting of `funPart m` constrains only
  -- the function part, so the argument slot is unconstrained.
  private
    noEq : (x : Name) → (var x) Eq.≡ lam x (var x) → ⊥
    noEq x ()

  ¬funReflects : (x : Name) → F.ReflectsSplitAt appOp → ⊥
  ¬funReflects x R
    with R (app (app (var x) (var x)) (lam x (var x))) (mkApp (var x) (var x))
  ... | mkApp _ _ , e = noEq x (e false)
