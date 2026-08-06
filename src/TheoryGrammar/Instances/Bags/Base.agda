{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The commutative-monoid signature, interleaving, and the substrate. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Bags.Base (A : Type₀) where

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
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded

Bag : Type₀
Bag = List A

-- Signature.  Same as monoids -- commutativity is an EQUATION, and
-- equations live in the model, not the signature.

data MonOp : Type₀ where
  nilop appop : MonOp

MonAr : MonOp → Type₀
MonAr nilop = ⊥
MonAr appop = Bool

cmSig : SortedSig Unit ℓ-zero ℓ-zero
cmSig .ops          = MonOp
cmSig .arities      = MonAr
cmSig .sortOf _ _   = tt
cmSig .resultSort _ = tt

-- Interleaving: the commutative splitting.

data Ilv : Bag → Bag → Bag → Type₀ where
  nil   : Ilv [] [] []
  left  : ∀ {x u v w} → Ilv u v w → Ilv (x ∷ u) v (x ∷ w)
  right : ∀ {x u v w} → Ilv u v w → Ilv u (x ∷ v) (x ∷ w)

IsNil : Bag → Type₀
IsNil []      = Unit
IsNil (_ ∷ _) = ⊥

ilvApp : (u v : Bag) → Ilv u v (u ++ v)
ilvApp []      []      = nil
ilvApp []      (x ∷ v) = right (ilvApp [] v)
ilvApp (x ∷ u) v       = left (ilvApp u v)


MonSplit : (o : MonOp) → Bag → Type₀
MonSplit nilop w = IsNil w
MonSplit appop w = Σ[ u ∈ Bag ] Σ[ v ∈ Bag ] Ilv u v w

MonParts : (o : MonOp) (w : Bag) → MonSplit o w → MonAr o → Bag
MonParts nilop w sp ()
MonParts appop w (u , v , _) b = if b then u else v

bagSub : Substrate cmSig ℓ-zero ℓ-zero
bagSub .carrier _   = Bag
bagSub .op nilop _  = []
bagSub .op appop f  = f true ++ f false
bagSub .Split       = MonSplit
bagSub .parts       = MonParts
bagSub .split nilop f = tt
bagSub .split appop f = f true , f false , ilvApp (f true) (f false)
bagSub .parts-split nilop f = funExt λ ()
bagSub .parts-split appop f = funExt λ { false → refl ; true → refl }

open SubNotation bagSub public

Gr : Type₁
Gr = TheoryTy ℓ-zero tt
