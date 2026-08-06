{-
  The substrate: scalars are ℕ under multiplication, elements are
  strings, and the action is REPLICATION.

      carrier scl = ℕ,      op mulOp (r,s) = r · s,   op oneOp = 1
      carrier elt = String, op catOp (u,v) = u ++ v
      op actOp (r,w)        = rep r w = w ++ w ++ ... ++ w   (r times)

  This is not an arbitrary choice of model.  It is the one that makes
  the GRADE MEAN SOMETHING: `⊗ˢ actOp (⌈ r ⌉ , A)` holds of exactly
  those strings that are `r` copies of a string satisfying `A`, so the
  graded modality of `Connectives.agda` is literally the multiplicity
  modality of bounded/quantitative linear logic, and the semimodule
  axioms read as facts about replication:

      (r·s)·w = r·(s·w)   rep (r · s) w ≡ rep r (rep s w)
      1·w     = w         rep 1 w       ≡ w
      (r+s)·w = r·w ++ s·w   rep (r + s) w ≡ rep r w ++ rep s w
      r·(u ++ v) = r·u ++ r·v            ***FALSE***

  The last line is not an oversight; it is the most informative thing
  in this instance.  Replication does not distribute over concatenation
  because strings do not commute: (uv)² = uvuv while u²v² = uuvv.  So
  this substrate refutes one of the graded-modality laws outright,
  which is a sharper statement than "the framework cannot derive it".

  SPLITTINGS.  Each is a one-constructor inductive family indexed by
  the OUTPUT, following the lambda instance: `parts` is then a
  projection rather than an inversion lemma, and no `Split` carries a
  proof term (CLAUDE.md's rule).  `catOp` is the exception in shape
  only -- its splitting is `Split3`, the string instance's inductive
  concatenation relation, which is also proof-free.

  Note that `IsRep []` has infinitely many inhabitants (`mkRep 0 w` for
  every `w`), i.e. the action is massively ambiguous at the unit.  That
  is normal: splittings are data, not propositions.
-}
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
open import TheoryGrammar.Substrate
open import TheoryGrammar.RulesSub
open import TheoryGrammar.Instances.Semimodule.Signature public

String : Type₀
String = List Char

-- ==================================================================
-- The action: replication.
-- ==================================================================

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

-- ==================================================================
-- Splittings, as output-indexed data.
-- ==================================================================

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

-- ==================================================================
-- The substrate.
-- ==================================================================

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

smSub : Substrate semiSig ℓ-zero ℓ-zero
smSub .carrier = MCarrier
smSub .op      = MOpFn
smSub .Split   = MSplit
smSub .parts   = MParts
smSub .split oneOp f = mk1
smSub .split mulOp f = mkFac (f true) (f false)
smSub .split catOp f = f true , f false , splitAll (f true) (f false)
smSub .split actOp f = mkRep (f true) (f false)
-- MEASUREMENT, same as the lambda instance: `oneOp` needs `funExt λ ()`
-- and the binary operations need `funExt` with `refl` at each slot,
-- because `Bool` has no η.
smSub .parts-split oneOp f = funExt λ ()
smSub .parts-split mulOp f = funExt λ { true → refl ; false → refl }
smSub .parts-split catOp f = funExt λ { true → refl ; false → refl }
smSub .parts-split actOp f = funExt λ { true → refl ; false → refl }

open RulesS smSub public

-- ==================================================================
-- The two grammar sorts.
-- ==================================================================

Scl : Type₁
Scl = TheoryTy ℓ-zero scl          -- ℕ      → Type

Elt : Type₁
Elt = TheoryTy ℓ-zero elt          -- String → Type

-- ==================================================================
-- BELONGS UPSTREAM.  The η-law an arity does not have.  Every
-- round-trip in this instance ends here, because `⊗ˢ`'s payload is a
-- function out of `arities o = Bool` and `λ { true → h true ; false →
-- h false }` is not definitionally `h`.  Stated once, used everywhere.
-- ==================================================================

-- A NAMED binary tuple over the arity.  Naming it is not cosmetic:
-- Agda identifies extended lambdas NOMINALLY, so `λ { true → x ;
-- false → y }` written in two different files are two different terms
-- and no `refl` relates them.  Every arity-family below therefore goes
-- through `pairB`.
pairB : ∀ {ℓ} {P : Bool → Type ℓ} → P true → P false → (a : Bool) → P a
pairB x y true  = x
pairB x y false = y

etaBool : ∀ {ℓ} {P : Bool → Type ℓ} (h : (a : Bool) → P a)
        → pairB (h true) (h false) ≡ h
etaBool h = funExt λ { true → refl ; false → refl }
