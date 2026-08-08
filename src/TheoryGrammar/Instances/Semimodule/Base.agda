{- The `Fibered`: scalars are ℕ under multiplication, elements are strings,
   and the action is REPLICATION. carrier scl = ℕ, op mulOp (r,s) = r · s,
   op oneOp = 1 carrier elt = String, op catOp (u,v) = u ++ v op actOp
   (r,w) = rep r w = w ++ w ++ ... ++ w (r times) This is not an arbitrary
   choice of... -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Semimodule.Base (Char : Type₀) where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Nat
open import Cubical.Data.List
open import Cubical.Data.Empty using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib
open import TheoryGrammar.Instances.Semimodule.Signature public

String : Type₀
String = List Char

-- The action: replication.

rep : ℕ → String → String
rep zero    w = []
rep (suc n) w = w ++ rep n w

-- The three arithmetic facts the whole instance rests on.  They are
-- facts about the CARRIER; nothing internal appears in them.

rep-add : (a b : ℕ) (w : String) → rep (a + b) w ≡ rep a w ++ rep b w
rep-add zero    b w = refl
rep-add (suc a) b w =
  cong (w ++_) (rep-add a b w) ∙ sym (++-assoc w (rep a w) (rep b w))

rep-mul : (a b : ℕ) (w : String) → rep (a · b) w ≡ rep a (rep b w)
rep-mul zero    b w = refl
rep-mul (suc a) b w =
  rep-add b (a · b) w ∙ cong (rep b w ++_) (rep-mul a b w)

rep-one : (w : String) → rep 1 w ≡ w
rep-one w = ++-unit-r w

-- Splittings, as output-indexed data.

data Is1 : ℕ → Type₀ where
  mk1 : Is1 1

data Factor : ℕ → Type₀ where
  mkFac : (a b : ℕ) → Factor (a · b)

data Split3 : String → String → String → Type₀ where
  nil  : ∀ {v} → Split3 [] v v
  cons : ∀ {c u v w} → Split3 u v w → Split3 (c ∷ u) v (c ∷ w)

splitAll : (u v : String) → Split3 u v (u ++ v)
splitAll []      v = nil
splitAll (c ∷ u) v = cons (splitAll u v)

data IsRep : String → Type₀ where
  mkRep : (r : ℕ) (w : String) → IsRep (rep r w)

-- The `Fibered`.

MCarrier : MSort → Type₀
MCarrier scl = ℕ
MCarrier elt = String

MOpFn : (o : MOp) → ((a : MAr o) → MCarrier (MSortOf o a)) → MCarrier (MResult o)
MOpFn oneOp _ = 1
MOpFn mulOp f = f true · f false
MOpFn catOp f = f true ++ f false
MOpFn actOp f = rep (f true) (f false)

MSplit : (o : MOp) → MCarrier (MResult o) → Type₀
MSplit oneOp   = Is1
MSplit mulOp   = Factor
MSplit catOp w = Σ[ u ∈ String ] Σ[ v ∈ String ] Split3 u v w
MSplit actOp   = IsRep

MParts : (o : MOp) (m : MCarrier (MResult o))
       → MSplit o m → (a : MAr o) → MCarrier (MSortOf o a)
MParts oneOp _ _ ()
MParts mulOp _ (mkFac a b)  c     = if c then a else b
MParts catOp _ (u , v , _)  c     = if c then u else v
MParts actOp _ (mkRep r w)  true  = r
MParts actOp _ (mkRep r w)  false = w

smFib : Fibered semiSig ℓ-zero ℓ-zero
smFib .carrier = MCarrier
smFib .Split   = MSplit
smFib .parts   = MParts

-- The total point, separately: all four operations are total here, so
-- the split loses nothing.  What it buys is that `RulesF smFib` never
-- consults it; only `Graded` (which is Model-level) needs the point.
smPoint : LaxPoint smFib
smPoint .op      = MOpFn
smPoint .split oneOp f = mk1
smPoint .split mulOp f = mkFac (f true) (f false)
smPoint .split catOp f = f true , f false , splitAll (f true) (f false)
smPoint .split actOp f = mkRep (f true) (f false)
-- MEASUREMENT, same as the lambda instance: `oneOp` needs `funExt λ ()`
-- and the binary operations need `funExt` with `refl` at each slot,
-- because `Bool` has no η.
smPoint .parts-split oneOp f = funExt λ ()
smPoint .parts-split mulOp f = funExt λ { true → refl ; false → refl }
smPoint .parts-split catOp f = funExt λ { true → refl ; false → refl }
smPoint .parts-split actOp f = funExt λ { true → refl ; false → refl }

open RulesF smFib public

-- The two grammar sorts.

Scl : Type₁
Scl = TheoryTy ℓ-zero scl          -- ℕ      → Type

Elt : Type₁
Elt = TheoryTy ℓ-zero elt          -- String → Type

-- BELONGS UPSTREAM. The η-law an arity does not have.

-- A NAMED binary tuple over the arity. Naming it is not cosmetic: Agda
-- identifies extended lambdas NOMINALLY, so `λ { true → x ; false → y }`
-- written in two different files are two different terms and no `refl`
-- relates them.
pairB : ∀ {ℓ} {P : Bool → Type ℓ} → P true → P false → (a : Bool) → P a
pairB x y true  = x
pairB x y false = y

etaBool : ∀ {ℓ} {P : Bool → Type ℓ} (h : (a : Bool) → P a)
        → pairB (h true) (h false) ≡ h
etaBool h = funExt λ { true → refl ; false → refl }
