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

-- The functorial action of the binary tensor: `⊗ˢ-map` at arity
-- `Bool`.  It is what lets a program act on both factors without
-- opening the splitting.
⊗-map : {P P' Q Q' : Gr} → P ⊢ P' → Q ⊢ Q' → (P ⊗' Q) ⊢ (P' ⊗' Q')
⊗-map {P} {P'} {Q} {Q'} f g =
  ⊗ˢ-map appop {A = λ b → if b then P  else Q}
                {B = λ b → if b then P' else Q'}
         λ { true → f ; false → g }

-- ⊗ intro and elim at the connective level: the only two places here
-- that mention a splitting.

⊗I : {P : Bool → Bag → Type₀} {u v w : Bag}
   → Ilv u v w → P true u → P false v
   → Σ[ sp ∈ MonSplit appop w ] ((a : Bool) → P a (MonParts appop w sp a))
⊗I {u = u} {v} s p q = (u , v , s) , λ { true → p ; false → q }

⊗E : {P : Bool → Bag → Type₀} {R : Type₀} {w : Bag}
   → ((u v : Bag) → Ilv u v w → P true u → P false v → R)
   → Σ[ sp ∈ MonSplit appop w ] ((a : Bool) → P a (MonParts appop w sp a)) → R
⊗E f ((u , v , s) , h) = f u v s (h true) (h false)

-- The combinators come from `RulesF` (opened in Base); only the binary
-- ⊗ intro/elim/map are local.
