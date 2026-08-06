{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE ADDITIVE NATURALS  (ℕ, +, 0)  AS A SUBSTRATE.

  Every file in this directory is the `Instances/Strings/` development
  with `ℕ` in place of `List Char`, and it is worth saying exactly what
  changes and what does not, because the answer is: nothing changes.

      Strings/Base                   Nat/Base
      ------------                   --------
      String  = List Char            ℕ
      Split3 u v w                   Add3 i j k
      IsNil                          IsZero
      splitAll u v : Split3 …        addAll i j : Add3 i j (i + j)

  `Split3` is already `Add3` with a character remembered at each `cons`
  step; erase the character and you have the unary numerals.  That is not
  a coincidence -- ℕ IS the free monoid on one generator -- and it is the
  whole reason this instance is worth having: it is the image of the
  string instance under `length`, and `Instances/Nat/Length.agda` makes
  that precise.

  WHAT A TYPE OVER (ℕ, +) IS.

  `TheoryTy ℓ tt = ℕ → Type ℓ` -- a GRADED SET, i.e. a species-like
  object, i.e. the categorification of a formal power series.  Write

      A(x)  =  Σₙ |A n| xⁿ .

  Then the connectives are the operations on power series:

      ⊕      is  A(x) + B(x)          (coefficientwise sum)
      ⊗      is  A(x) · B(x)          (the CAUCHY PRODUCT: a point of
                                       (A ⊗ B) n is a way of writing
                                       n = i + j together with payloads,
                                       which is exactly Σᵢ₊ⱼ₌ₙ aᵢ bⱼ)
      ε      is  1
      ⌈ 1 ⌉  is  x
      A *    is  1/(1 - A(x))         (the geometric series -- `KL*` is
                                       μ of `ε ⊕ (A ⊗ Var)`, whose
                                       coefficient recurrence is exactly
                                       the expansion of 1/(1-A))

  Consequently A GRAMMAR ISOMORPHISM IS A GENERATING-FUNCTION IDENTITY,
  with the bijection supplied rather than asserted.  `Instances/Nat/
  Species.agda` carries out one such: the Catalan recurrence
  C(x) = 1 + x²C(x)² is a two-line term of the calculus.

  The residual `⟜` is division of power series -- which is total here
  only in the "formal quotient" sense that ⟜ is a right adjoint, not
  because coefficients can be subtracted.  This is the usual reason ⊸ is
  well-behaved in a Lambek calculus and subtraction is not: right
  adjoints always exist, inverses need not.

  NOTE ON SIGNATURE DUPLICATION.  This file defines its own `MonOp` /
  `monoidSig`, exactly as `Strings/Base.agda` and `Bags/Base.agda` each do.
  The three are definitionally distinct datatypes with identical
  definitions, so a `ModelHom` between (say) the string model and the ℕ
  model cannot even be STATED without first choosing one of them.  That
  is a real defect; see the header of `Length.agda`.
-}
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

-- ==================================================================
-- The signature of monoids.  (Commutativity of + is an EQUATION and
-- lives in the model, not the signature -- see Bags/Base for the same
-- remark.  We do NOT use it here: everything below is the ORDERED
-- reading of ℕ, i.e. the free monoid on one letter, which is what makes
-- `length` a Conduché functor in Length.agda.)
-- ==================================================================


-- ==================================================================
-- Splittings, inductively.  `Add3 i j k` is `i + j = k` presented as
-- DATA indexed by the output, in the shape `Split3` has for strings.
-- Note the asymmetry: recursion is on the LEFT summand, so `Add3` is the
-- graph of `+` *as a program*, and its constructors are exactly the
-- clauses of `_+_`.
-- ==================================================================

data Add3 : ℕ → ℕ → ℕ → Type₀ where
  z : ∀ {j} → Add3 zero j j
  s : ∀ {i j k} → Add3 i j k → Add3 (suc i) j (suc k)

-- `IsZero` as a RECURSIVE predicate, not an indexed family.  Same reason
-- as `IsNil` in Strings/Base: then every case split below happens on the
-- NUMBER, and no clause needs higher-dimensional unification.  An
-- indexed `data IsZero : ℕ → Type` would force `--no-unsupported-indexed
-- -match` warnings at each of `parts-split`, `deg≤`, `deg<`.
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
