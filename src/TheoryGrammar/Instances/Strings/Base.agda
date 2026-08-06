{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The monoid signature, splittings as an inductive family, and the promodel. -}
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
open import TheoryGrammar.Theories.Monoid public
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib
open import TheoryGrammar.SemanticAction
open import TheoryGrammar.Decidable.Tensor

String : Type₀
String = List Char

-- Signature of monoids; splittings inductively.


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

strFib : Fibered monoidSig ℓ-zero ℓ-zero
strFib .carrier _   = String
strFib .Split       = MonSplit
strFib .parts       = MonParts

-- The total point, separately: strings DO have a total concatenation, so
-- this instance loses nothing by the split.  What the split buys is that
-- `RulesF strFib` never consults it.
strPoint : LaxPoint strFib
strPoint .op nilop _  = []
strPoint .op appop f  = f true ++ f false
strPoint .split nilop f = tt
strPoint .split appop f = f true , f false , splitAll (f true) (f false)
strPoint .parts-split nilop f = funExt λ ()
strPoint .parts-split appop f = funExt λ { false → refl ; true → refl }

-- The connectives, the decision layer and the semantic actions in one
-- open: `DecFib` is the aggregation point (`RulesF` + `ActFib` +
-- `DecAdd`), so this instance gets `Dec⟨_⟩` and `run` without
-- redefining either.
open DecFib strFib public

Gr : Type₁
Gr = TheoryTy ℓ-zero tt
