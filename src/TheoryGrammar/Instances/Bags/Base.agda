{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The commutative-monoid signature, interleaving, and the promodel. -}
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
open import TheoryGrammar.Theories.Monoid public
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib
open import TheoryGrammar.SemanticAction
open import TheoryGrammar.Decidable.Tensor
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded

Bag : Type₀
Bag = List A

-- Signature.  Same as monoids -- commutativity is an EQUATION, and
-- equations live in the model, not the signature.


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

bagFib : Fibered monoidSig ℓ-zero ℓ-zero
bagFib .carrier _   = Bag
bagFib .Split       = MonSplit
bagFib .parts       = MonParts

-- The total point, separately.  Bags have a total union, so the split
-- costs this instance nothing; what it buys is that the connectives
-- never consult it.  Note `Ilv` is NOT the fibre of `++` -- a splitting
-- need not be a concatenation -- so the point really is only lax.
bagPoint : LaxPoint bagFib
bagPoint .op nilop _  = []
bagPoint .op appop f  = f true ++ f false
bagPoint .split nilop f = tt
bagPoint .split appop f = f true , f false , ilvApp (f true) (f false)
bagPoint .parts-split nilop f = funExt λ ()
bagPoint .parts-split appop f = funExt λ { false → refl ; true → refl }

open DecFib bagFib public

Gr : Type₁
Gr = TheoryTy ℓ-zero tt
