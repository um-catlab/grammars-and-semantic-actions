{-
  THE INDUCTION PRINCIPLE OF THE AST SUBSTRATE'S CARRIER.

  This is the ONE primitive the mode development adds on the AST side:
  `Raw` is the initial λSig-algebra and `indRaw` is its eliminator.
  Everything downstream is `indRaw` applied to an algebra assembled from
  the connectives --

      Uses  = indRaw at a CONSTANT motive (so: the fold)
      check = indRaw at the motive  ⊤ ⊢ Dec⟨ Uses t ⟩

  -- and no other definition in `Modes/` matches on a `Raw`.
-}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Instances.Lambda.Modes.Fold where

open import Cubical.Foundations.Prelude

open import TheoryGrammar.Instances.Lambda.Substrate

module Fold (Name : Type₀) where

  open Terms Name

  private variable ℓ : Level

  -- PRIMITIVE (1 of 1 on the AST side).
  indRaw : (P : Raw → Type ℓ)
         → ((n : Name) → P (var n))
         → ((u v : Raw) → P u → P v → P (app u v))
         → ((n : Name) (t : Raw) → P t → P (lam n t))
         → (t : Raw) → P t
  indRaw P pv pa pl (var n)   = pv n
  indRaw P pv pa pl (app u v) = pa u v (indRaw P pv pa pl u) (indRaw P pv pa pl v)
  indRaw P pv pa pl (lam n t) = pl n t (indRaw P pv pa pl t)
