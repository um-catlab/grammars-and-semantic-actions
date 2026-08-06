{-
  The promodel: raw lambda terms, with splittings as output-indexed
  data rather than an equation.

  Each `Is*` family has exactly ONE constructor.  That is unique
  readability of the AST, it is what makes `parts` a projection instead
  of an inversion lemma, and it is a property of the promodel rather
  than of any grammar written over it.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Fibered where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Unit

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Instances.Lambda.Signature

module Terms (Name : Type₀) where

  data Raw : Type₀ where
    var : Name → Raw
    app : Raw → Raw → Raw
    lam : Name → Raw → Raw

  Carrier : LSort → Type₀
  Carrier nm = Name
  Carrier tm = Raw

  Op : (o : LOp) → ((a : LAr o) → Carrier (LSortOf o a)) → Raw
  Op varOp f = var (f tt)
  Op appOp f = app (f true) (f false)
  Op lamOp f = lam (f true) (f false)

  data IsVar : Raw → Type₀ where
    mkVar : (n : Name) → IsVar (var n)

  data IsApp : Raw → Type₀ where
    mkApp : (u v : Raw) → IsApp (app u v)

  data IsLam : Raw → Type₀ where
    mkLam : (n : Name) (t : Raw) → IsLam (lam n t)

  LSplit : (o : LOp) → Raw → Type₀
  LSplit varOp = IsVar
  LSplit appOp = IsApp
  LSplit lamOp = IsLam

  LParts : (o : LOp) (t : Raw) → LSplit o t → (a : LAr o) → Carrier (LSortOf o a)
  LParts varOp _ (mkVar n)   _     = n
  LParts appOp _ (mkApp u v) b     = if b then u else v
  LParts lamOp _ (mkLam n t) true  = n
  LParts lamOp _ (mkLam n t) false = t

  λFib : Fibered λSig ℓ-zero ℓ-zero
  λFib .carrier       = Carrier
  λFib .Split         = LSplit
  λFib .parts         = LParts

  -- The total point, separately: raw terms DO have total constructors, so
  -- this instance loses nothing by the split.  What the split buys is that
  -- `RulesF λFib` -- the whole multiplicative layer -- never consults it.
  λPoint : LaxPoint λFib
  λPoint .op            = Op
  λPoint .split varOp f = mkVar (f tt)
  λPoint .split appOp f = mkApp (f true) (f false)
  λPoint .split lamOp f = mkLam (f true) (f false)
  -- MEASUREMENT: `varOp` is refl because `Unit` has definitional η, so
  -- `λ a → f tt` already IS `f`.  The `Bool`-arity operations need
  -- funExt, with refl at each slot -- the same cost the string instance
  -- reports for `⟜-η`, and for the same reason.
  λPoint .parts-split varOp f = refl
  λPoint .parts-split appOp f = funExt λ { true → refl ; false → refl }
  λPoint .parts-split lamOp f = funExt λ { true → refl ; false → refl }
