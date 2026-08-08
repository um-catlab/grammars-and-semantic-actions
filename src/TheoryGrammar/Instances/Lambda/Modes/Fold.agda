{- THE INDUCTION PRINCIPLE OF THE AST SUBSTRATE'S CARRIER -- DERIVED. -}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Instances.Lambda.Modes.Fold where

open import Cubical.Data.List using ([])
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Foundations.Prelude

open import TheoryGrammar.Instances.Lambda.Fibered
open import TheoryGrammar.Instances.Lambda.Initial

module Fold (Name : Type₀) where

  open Terms Name
  open Initial Name using (AllF; AllAlg; readback; fold)

  private variable ℓ : Level

  -- DERIVED: no longer a primitive.  `readback` is the primitive that
  -- replaced it, and it lives in `Lambda.Initial`.
  indRaw : (P : Raw → Type ℓ)
         → ((n : Name) → P (var n))
         → ((u v : Raw) → P u → P v → P (app u v))
         → ((n : Name) (t : Raw) → P t → P (lam n t))
         → (t : Raw) → P t
  indRaw P pv pa pl t =
    fold (λ i → P (i .snd)) (AllAlg P pv pa pl) ([] , t) (readback [] t tt)
