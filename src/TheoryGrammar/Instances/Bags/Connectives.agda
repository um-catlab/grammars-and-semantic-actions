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
open import TheoryGrammar.Substrate
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

-- COMBINATORS.  These are the rules of the calculus; they are the
-- only pointful things in this file apart from the two primitives
-- below.  Everything after composes them.

⊤' : Gr
⊤' _ = Unit

idg : {P : Gr} → P ⊢ P
idg _ p = p

_∘g_ : {P Q R : Gr} → Q ⊢ R → P ⊢ Q → P ⊢ R
(g ∘g f) w p = g w (f w p)

infixr 9 _∘g_

⊕-elim : {P Q R : Gr} → P ⊢ R → Q ⊢ R → (P ⊕ Q) ⊢ R
⊕-elim f g w (inl p) = f w p
⊕-elim f g w (inr q) = g w q

⊕ᴰ-in : {Y : Type₀} {P : Y → Gr} (y : Y) → P y ⊢ ⊕ᴰ Y P
⊕ᴰ-in y w p = y , p

⊕ᴰ-elim : {Y : Type₀} {P : Y → Gr} {R : Gr}
        → ((y : Y) → P y ⊢ R) → ⊕ᴰ Y P ⊢ R
⊕ᴰ-elim f w (y , p) = f y w p

liftg : {P : Gr} → P ⊢ (λ m → Lift ℓ-zero (P m))
liftg _ p = lift p

⊗-map : {P P' Q Q' : Gr} → P ⊢ P' → Q ⊢ Q' → (P ⊗' Q) ⊢ (P' ⊗' Q')
⊗-map f g w ((u , v , s) , h) = ⊗-mk s (f u (h true)) (g v (h false))

-- ASSOCIATIVITY OF INTERLEAVING.  w = p ⊎ (q ⊎ r) regrouped as
-- w = q ⊎ (p ⊎ r).  Used once, by the partition primitive.
