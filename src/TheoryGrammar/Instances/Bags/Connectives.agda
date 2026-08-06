{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- ⊗ and ε at bags, their intro/elim, and the combinators programs are built from. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Bags.Connectives (A : Type₀) where

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
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded

open import TheoryGrammar.Instances.Bags.Base A public

_⊗'_ : Gr → Gr → Gr
P ⊗' Q = ⊗ˢ appop (λ b → if b then P else Q)

ε' : Gr
ε' = ⊗ˢ nilop (λ ())

⊗-mk : {P Q : Gr} {u v w : Bag} → Ilv u v w → P u → Q v → (P ⊗' Q) w
⊗-mk {u = u} {v} s p q = (u , v , s) , λ { true → p ; false → q }

-- THE COMMUTATIVITY EQUATION, lifted to an isomorphism.  This is the
-- `eqn→Iso` shape at the one equation that distinguishes commutative
-- monoids from monoids, discharged by `ilvSwap`.

-- ⊗ intro and elim AT THE CONNECTIVE LEVEL.  These two are the only
-- places below that mention a splitting; everything after is built
-- from them.

⊗I : {P : Bool → Bag → Type₀} {u v w : Bag}
   → Ilv u v w → P true u → P false v
   → Σ[ sp ∈ MonSplit appop w ] ((a : Bool) → P a (MonParts appop w sp a))
⊗I {u = u} {v} s p q = (u , v , s) , λ { true → p ; false → q }

⊗E : {P : Bool → Bag → Type₀} {R : Type₀} {w : Bag}
   → ((u v : Bag) → Ilv u v w → P true u → P false v → R)
   → Σ[ sp ∈ MonSplit appop w ] ((a : Bool) → P a (MonParts appop w sp a)) → R
⊗E f ((u , v , s) , h) = f u v s (h true) (h false)

-- PERMUTATION, for the intrinsic specification.  `Perm a w` says the
-- list `a` is a rearrangement of `w`; insertion is `Ilv (x ∷ []) v w`,
-- so permutation is built from the SUBSTRATE'S OWN relation rather
-- than from a quotient.

-- The combinators come from `RulesF` (opened in Base); only `liftg`
-- and the binary ⊗ intro/elim are local.

liftg : {P : Gr} → P ⊢ (λ m → Lift ℓ-zero (P m))
liftg _ p = lift p

-- ASSOCIATIVITY OF INTERLEAVING.  w = p ⊎ (q ⊎ r) regrouped as
-- w = q ⊎ (p ⊎ r).  Used once, by the partition primitive.
