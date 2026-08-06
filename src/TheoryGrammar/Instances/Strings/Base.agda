{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The monoid signature, splittings as an inductive family, and the substrate. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Strings.Base (Char : Type₀) where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.List
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Substrate
open import TheoryGrammar.RulesSub
open import TheoryGrammar.SemanticAction
open import TheoryGrammar.Decidable.Tensor

String : Type₀
String = List Char

-- Signature of monoids; splittings inductively.

data MonOp : Type₀ where
  nilop appop : MonOp

MonAr : MonOp → Type₀
MonAr nilop = ⊥
MonAr appop = Bool

monSig : SortedSig Unit ℓ-zero ℓ-zero
monSig .ops          = MonOp
monSig .arities      = MonAr
monSig .sortOf _ _   = tt
monSig .resultSort _ = tt

data Split3 : String → String → String → Type₀ where
  nil  : ∀ {v} → Split3 [] v v
  cons : ∀ {c u v w} → Split3 u v w → Split3 (c ∷ u) v (c ∷ w)

-- IsNil as a RECURSIVE predicate, not an indexed family: then every
-- case split below happens on the string itself, and no clause needs
-- higher-dimensional unification.
IsNil : String → Type₀
IsNil []      = Unit
IsNil (_ ∷ _) = ⊥

splitAll : (u v : String) → Split3 u v (u ++ v)
splitAll []      v = nil
splitAll (c ∷ u) v = cons (splitAll u v)

MonSplit : (o : MonOp) → String → Type₀
MonSplit nilop w = IsNil w
MonSplit appop w = Σ[ u ∈ String ] Σ[ v ∈ String ] Split3 u v w

MonParts : (o : MonOp) (w : String) → MonSplit o w → MonAr o → String
MonParts nilop w sp ()
MonParts appop w (u , v , _) b = if b then u else v

strSub : Substrate monSig ℓ-zero ℓ-zero
strSub .carrier _   = String
strSub .op nilop _  = []
strSub .op appop f  = f true ++ f false
strSub .Split       = MonSplit
strSub .parts       = MonParts
strSub .split nilop f = tt
strSub .split appop f = f true , f false , splitAll (f true) (f false)
strSub .parts-split nilop f = funExt λ ()
strSub .parts-split appop f = funExt λ { false → refl ; true → refl }

-- The connectives, the decision layer and the semantic actions in one
-- open: `DecSub` is the aggregation point (`RulesS` + `ActSub` +
-- `DecAdd`), so this instance gets `Dec⟨_⟩` and `run` without
-- redefining either.
open DecSub strSub public

Gr : Type₁
Gr = TheoryTy ℓ-zero tt
