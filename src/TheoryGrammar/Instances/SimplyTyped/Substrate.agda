{-
  The substrate: raw annotated terms AND simple types, with splittings
  as output-indexed data.

  The carrier is now a three-element family; `Ty` is a carrier, not a
  parameter, so `⌈ A ⌉` at sort `ty` is a grammar of types in exactly
  the sense `⌈ n ⌉` is a grammar of names.

  Each `Is*` family has exactly one constructor -- unique readability,
  now at two different sorts at once.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.SimplyTyped.Substrate where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Substrate
open import TheoryGrammar.Instances.SimplyTyped.Signature

infixr 20 _⇒ᵗ_

data Ty : Type₀ where
  base : Ty
  _⇒ᵗ_ : Ty → Ty → Ty

data IsBase : Ty → Type₀ where
  mkBase : IsBase base

data IsArr : Ty → Type₀ where
  mkArr : (A B : Ty) → IsArr (A ⇒ᵗ B)

module Terms (Name : Type₀) where

  data Raw : Type₀ where
    var : Name → Raw
    app : Raw → Raw → Raw
    lam : Name → Raw → Raw
    ann : Raw → Ty → Raw

  Carrier : TSort → Type₀
  Carrier nm = Name
  Carrier tm = Raw
  Carrier ty = Ty

  Op : (o : TOp) → ((a : TAr o) → Carrier (TSortOf o a)) → Carrier (TResult o)
  Op varOp  f = var (f tt)
  Op appOp  f = app (f true) (f false)
  Op lamOp  f = lam (f true) (f false)
  Op annOp  f = ann (f true) (f false)
  Op baseOp f = base
  Op arrOp  f = f true ⇒ᵗ f false

  data IsVar : Raw → Type₀ where
    mkVar : (n : Name) → IsVar (var n)

  data IsApp : Raw → Type₀ where
    mkApp : (u v : Raw) → IsApp (app u v)

  data IsLam : Raw → Type₀ where
    mkLam : (n : Name) (t : Raw) → IsLam (lam n t)

  data IsAnn : Raw → Type₀ where
    mkAnn : (t : Raw) (A : Ty) → IsAnn (ann t A)

  TSplit : (o : TOp) → Carrier (TResult o) → Type₀
  TSplit varOp  = IsVar
  TSplit appOp  = IsApp
  TSplit lamOp  = IsLam
  TSplit annOp  = IsAnn
  TSplit baseOp = IsBase
  TSplit arrOp  = IsArr

  TParts : (o : TOp) (m : Carrier (TResult o)) → TSplit o m
         → (a : TAr o) → Carrier (TSortOf o a)
  TParts varOp  _ (mkVar n)   _     = n
  TParts appOp  _ (mkApp u v) b     = if b then u else v
  TParts lamOp  _ (mkLam n t) true  = n
  TParts lamOp  _ (mkLam n t) false = t
  TParts annOp  _ (mkAnn t A) true  = t
  TParts annOp  _ (mkAnn t A) false = A
  TParts baseOp _ mkBase      ()
  TParts arrOp  _ (mkArr A B) b     = if b then A else B

  stlcSub : Substrate stlcSig ℓ-zero ℓ-zero
  stlcSub .carrier        = Carrier
  stlcSub .op             = Op
  stlcSub .Split          = TSplit
  stlcSub .parts          = TParts
  stlcSub .split varOp  f = mkVar (f tt)
  stlcSub .split appOp  f = mkApp (f true) (f false)
  stlcSub .split lamOp  f = mkLam (f true) (f false)
  stlcSub .split annOp  f = mkAnn (f true) (f false)
  stlcSub .split baseOp f = mkBase
  stlcSub .split arrOp  f = mkArr (f true) (f false)
  -- MEASUREMENT: `varOp` is refl (Unit has definitional η); `baseOp` is
  -- funExt at the EMPTY arity, which is the degenerate case of the same
  -- failure; the four Bool arities need funExt with refl at each slot.
  stlcSub .parts-split varOp  f = refl
  stlcSub .parts-split appOp  f = funExt λ { true → refl ; false → refl }
  stlcSub .parts-split lamOp  f = funExt λ { true → refl ; false → refl }
  stlcSub .parts-split annOp  f = funExt λ { true → refl ; false → refl }
  stlcSub .parts-split baseOp f = funExt λ ()
  stlcSub .parts-split arrOp  f = funExt λ { true → refl ; false → refl }

  -- The extra substrate law the representables need: a splitting is
  -- FAITHFUL -- reassembling its parts gives the whole back.  `Substrate`
  -- has `parts-split` (tuple ↦ splitting ↦ tuple) but not this
  -- (splitting ↦ tuple ↦ whole); every clause is `Eq.refl`.
  unsplit : (o : TOp) (m : Carrier (TResult o)) (sp : TSplit o m)
          → Op o (TParts o m sp) Eq.≡ m
  unsplit varOp  _ (mkVar n)   = Eq.refl
  unsplit appOp  _ (mkApp u v) = Eq.refl
  unsplit lamOp  _ (mkLam n t) = Eq.refl
  unsplit annOp  _ (mkAnn t A) = Eq.refl
  unsplit baseOp _ mkBase      = Eq.refl
  unsplit arrOp  _ (mkArr A B) = Eq.refl
