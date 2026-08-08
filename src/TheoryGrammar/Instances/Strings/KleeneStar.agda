{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- A * as the generic μ, guarded exactly when A is non-nullable. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Strings.KleeneStar (Char : Type₀) where

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
open import TheoryGrammar.Theories.MonoidStar

open import TheoryGrammar.Instances.Strings.Decomposition Char public

-- The description and its guardedness are NOT string-specific: they are
-- the generic monoid star (TheoryGrammar.Theories.MonoidStar) at this
-- `Fibered`.
open MonStar strGraded
  using (starSlot; starAlt; starF; ProperBody;
         KL*; nil*; cons*; unroll*; roll*; starOut; starIn) public

-- non-nullability, internally: a non-nullable grammar entails the resource
-- predicate.
NonNullable : Gr → Type₀
NonNullable A = A ⊢ NonTrivial

nn→proper : {A : Gr} → NonNullable A → ProperBody A
nn→proper nn m sp a = nn _ a

-- THE UNIT versus GUARDEDNESS. `A *` is guarded exactly when `A` is NON-
-- NULLABLE.
starGuarded : (A : Gr) → NonNullable A → (x : Unit) → Guarded (starF A x)
starGuarded A nn = MonStar.starGuarded strGraded A (nn→proper nn)

-- literals are non-nullable, so `literal c *` is guarded
literalNN : (c : Char) → NonNullable (literal c)
literalNN c = ⌈⌉-E (c , ⊗-mk (cons nil) Eq.refl tt)

