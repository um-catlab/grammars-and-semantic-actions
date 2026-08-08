{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- THE ADDITIVE NATURALS (ℕ, +, 0) AS A SUBSTRATE. Every file in this
   directory is the `Instances/Strings/` development with `ℕ` in place of
   `List Char`, and it is worth saying exactly what changes and what does
   not, because the answer is: nothing changes. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Nat.Base where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Theories.Monoid public
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib

-- The signature of monoids. (Commutativity of + is an EQUATION and lives
-- in the model, not the signature -- see Bags/Base for the same remark.

-- Splittings, inductively. `Add3 i j k` is `i + j = k` presented as DATA
-- indexed by the output, in the shape `Split3` has for strings.

data Add3 : ℕ → ℕ → ℕ → Type₀ where
  z : ∀ {j} → Add3 zero j j
  s : ∀ {i j k} → Add3 i j k → Add3 (suc i) j (suc k)

-- `IsZero` as a RECURSIVE predicate, not an indexed family.
IsZero : ℕ → Type₀
IsZero zero    = Unit
IsZero (suc _) = ⊥

addAll : (i j : ℕ) → Add3 i j (i + j)
addAll zero    j = z
addAll (suc i) j = s (addAll i j)

MonSplit : (o : MonOp) → ℕ → Type₀
MonSplit nilop n = IsZero n
MonSplit appop n = Σ[ i ∈ ℕ ] Σ[ j ∈ ℕ ] Add3 i j n

MonParts : (o : MonOp) (n : ℕ) → MonSplit o n → MonAr o → ℕ
MonParts nilop n sp ()
MonParts appop n (i , j , _) b = if b then i else j

natFib : Fibered monoidSig ℓ-zero ℓ-zero
natFib .carrier _   = ℕ
natFib .Split       = MonSplit
natFib .parts       = MonParts

-- The total point, separately.  `(ℕ,+)` has a total addition, so nothing
-- is lost here; what the split buys is that the whole multiplicative and
-- additive layer -- `RulesF natFib` -- never consults it.
natPoint : LaxPoint natFib
natPoint .op nilop _  = 0
natPoint .op appop f  = f true + f false
natPoint .split nilop f = tt
natPoint .split appop f = f true , f false , addAll (f true) (f false)
natPoint .parts-split nilop f = funExt λ ()
natPoint .parts-split appop f = funExt λ { false → refl ; true → refl }

open RulesF natFib public

-- A "grammar" here is a graded set: the coefficient sequence of a formal
-- power series, with the coefficients given as TYPES rather than numbers.
Gr : Type₁
Gr = TheoryTy ℓ-zero tt
