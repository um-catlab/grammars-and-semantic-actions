{- The `Fibered`: raw de Bruijn terms AND linear types, with splittings as
   output-indexed data. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.LinTyped.Fibered where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Instances.LinTyped.Signature

infixr 20 _⊸ᵗ_

-- `Ty` denotes a linear type over one base type.  The ONLY connective
-- is the linear function space; see `Signature`'s header for why `⊗`
-- is deliberately absent.
data Ty : Type₀ where
  base : Ty
  _⊸ᵗ_ : Ty → Ty → Ty

-- `IsBase C` denotes the ways `C` is a `base` node -- one when it is,
-- none otherwise.
data IsBase : Ty → Type₀ where
  mkBase : IsBase base

-- `IsLol C` denotes the ways `C` is a lollipop node.  The constructor
-- CARRIES the domain and codomain, so a witness is already the
-- decomposition and nothing has to be re-derived from `C`.
data IsLol : Ty → Type₀ where
  mkLol : (A B : Ty) → IsLol (A ⊸ᵗ B)

-- `Raw` denotes an annotated de Bruijn lambda AST, with no scoping,
-- linearity or typing discipline imposed.
data Raw : Type₀ where
  var : ℕ → Raw
  app : Raw → Raw → Raw
  lam : Raw → Raw
  ann : Raw → Ty → Raw

-- `Carrier s` denotes the WORLDS of sort `s`: a grammar at sort `s` is
-- a family over exactly this.
Carrier : TSort → Type₀
Carrier nm = ℕ
Carrier tm = Raw
Carrier ty = Ty

-- `Op o m⃗` denotes the `o`-node assembled from the tuple `m⃗`.
Op : (o : TOp) → ((a : TAr o) → Carrier (TSortOf o a)) → Carrier (TResult o)
Op varOp  f = var (f tt)
Op appOp  f = app (f true) (f false)
Op lamOp  f = lam (f tt)
Op annOp  f = ann (f true) (f false)
Op baseOp f = base
Op lolOp  f = f true ⊸ᵗ f false

-- `Is<Op> t` denotes the ways `t` is an `<op>` node, and its
-- constructor carries the slots -- as `IsLol` does at the `ty` sort.
data IsVar : Raw → Type₀ where
  mkVar : (n : ℕ) → IsVar (var n)

data IsApp : Raw → Type₀ where
  mkApp : (u v : Raw) → IsApp (app u v)

data IsLam : Raw → Type₀ where
  mkLam : (t : Raw) → IsLam (lam t)

data IsAnn : Raw → Type₀ where
  mkAnn : (t : Raw) (A : Ty) → IsAnn (ann t A)

-- `TSplit o m` denotes the ways `m` is an `o`-node ...
TSplit : (o : TOp) → Carrier (TResult o) → Type₀
TSplit varOp  = IsVar
TSplit appOp  = IsApp
TSplit lamOp  = IsLam
TSplit annOp  = IsAnn
TSplit baseOp = IsBase
TSplit lolOp  = IsLol

-- ... and `TParts o m sp` denotes the tuple of slots that `sp` says
-- `m` is built from.  It reads the witness, never `m`.
TParts : (o : TOp) (m : Carrier (TResult o)) → TSplit o m
       → (a : TAr o) → Carrier (TSortOf o a)
TParts varOp  _ (mkVar n)   _     = n
TParts appOp  _ (mkApp u v) b     = if b then u else v
TParts lamOp  _ (mkLam t)   _     = t
TParts annOp  _ (mkAnn t A) true  = t
TParts annOp  _ (mkAnn t A) false = A
TParts baseOp _ mkBase      ()
TParts lolOp  _ (mkLol A B) b     = if b then A else B

linFib : Fibered linSig ℓ-zero ℓ-zero
linFib .carrier        = Carrier
linFib .Split          = TSplit
linFib .parts          = TParts

-- The total point, separately: term formation IS total here, so the
-- split costs this instance nothing.
linPoint : LaxPoint linFib
linPoint .op             = Op
linPoint .split varOp  f = mkVar (f tt)
linPoint .split appOp  f = mkApp (f true) (f false)
linPoint .split lamOp  f = mkLam (f tt)
linPoint .split annOp  f = mkAnn (f true) (f false)
linPoint .split baseOp f = mkBase
linPoint .split lolOp  f = mkLol (f true) (f false)
-- MEASUREMENT, as in the cartesian instance: the two UNARY arities are
-- `refl` (Unit has definitional η), the empty one is `funExt` at the
-- degenerate case, and the three `Bool` arities need `funExt` with `refl`
-- at each slot.
linPoint .parts-split varOp  f = refl
linPoint .parts-split appOp  f = funExt λ { true → refl ; false → refl }
linPoint .parts-split lamOp  f = refl
linPoint .parts-split annOp  f = funExt λ { true → refl ; false → refl }
linPoint .parts-split baseOp f = funExt λ ()
linPoint .parts-split lolOp  f = funExt λ { true → refl ; false → refl }

-- The extra `Fibered` law the representables need: a splitting is
-- FAITHFUL -- reassembling its parts gives the whole back.
unsplit : (o : TOp) (m : Carrier (TResult o)) (sp : TSplit o m)
        → Op o (TParts o m sp) Eq.≡ m
unsplit varOp  _ (mkVar n)   = Eq.refl
unsplit appOp  _ (mkApp u v) = Eq.refl
unsplit lamOp  _ (mkLam t)   = Eq.refl
unsplit annOp  _ (mkAnn t A) = Eq.refl
unsplit baseOp _ mkBase      = Eq.refl
unsplit lolOp  _ (mkLol A B) = Eq.refl
