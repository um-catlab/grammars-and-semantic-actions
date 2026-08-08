{- IS `Proper` THE NON-IDENTITY MAPS? In a direct category the dichotomy is
   forced: a map either is the identity or is not, and
   `Direct/StrictDownset.agda`'s sieve `↡c` contains exactly the maps that
   strictly raise degree. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Direct.Proper where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Bool
  using (Bool ; true ; false ; not ; notnot ; true≢false ; false≢true)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as E using (⊥ ; ⊥*)
open import Cubical.Relation.Nullary using (¬_)

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Grading
open import TheoryGrammar.Direct.Divisibility

private variable ℓS ℓ ℓ' ℓX ℓP : Level

-- PART A. SATURATION -- "Proper IS non-identity".

module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (Fib : Fibered σ ℓX ℓP) where

  open Div Fib

  Saturated : Grading Fib → Type (ℓ-max ℓS (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓX ℓP))))
  Saturated G =
    (o : σ .ops) (m : Fib .carrier (σ .resultSort o))
    (sp : Fib .Split o m) (a : σ .arities o)
    → ¬ (Path Elt (σ .sortOf o a , Fib .parts o m sp a) (σ .resultSort o , m))
    → G .Proper o m sp a

-- PART B. THE `Fibered` THAT SEPARATES THEM.

predSig : SortedSig Unit ℓ-zero ℓ-zero
predSig .ops          = Unit
predSig .arities _    = Unit
predSig .sortOf _ _   = tt
predSig .resultSort _ = tt

predFib : Fibered predSig ℓ-zero ℓ-zero
predFib .carrier _     = ℕ
predFib .Split _ m     = Σ[ k ∈ ℕ ] (m ≡ suc k)
predFib .parts _ m sp _ = sp .fst

-- the honest grading: degree = the number itself, every slot proper
full : Grading predFib
full .deg _ n           = n
full .Proper _ _ _ _    = Unit
full .deg≤ _ m (k , p) _   = subst (k ≤_) (sym p) (≤-suc ≤-refl)
full .deg< _ m (k , p) _ _ = subst (k <_) (sym p) ≤-refl

-- the degenerate grading: it always exists (`Group/NoGrading`'s header
-- makes this point), and it is what makes `Proper` structure rather than
-- property
triv : Grading predFib
triv .deg _ _        = 0
triv .Proper _ _ _ _ = ⊥*
triv .deg≤ _ _ _ _   = ≤-refl
triv .deg< _ _ _ _ ()

module D    = Div predFib
module Full = D.Graded full
module Triv = D.Graded triv

-- 0 is the predecessor of 1 ...
step01 : (tt , 0) D.◃₁ (tt , 1)
step01 = D.slot tt 1 (0 , refl) tt

-- ... and this is a NON-IDENTITY map of the divisibility preorder
step01-≢ : ¬ (Path D.Elt (tt , 0) (tt , 1))
step01-≢ e = znots (cong snd e)

-- under `full` it is proper ...
step01-proper : (tt , 0) Full.◃ᵖ (tt , 1)
step01-proper = Full.pslot tt 1 (0 , refl) tt tt

-- ... and under `triv` NOTHING is proper.
triv-no-proper : {n m : D.Elt} → ¬ (n Triv.◃ᵖ m)
triv-no-proper (Triv.pslot o m sp a ())

-- THEOREM 2. `Proper` is not determined by the `Fibered`: two gradings of
-- `predFib` disagree on the very same slot.

Proper-undetermined :
  ((tt , 0) Full.◃ᵖ (tt , 1)) × (¬ ((tt , 0) Triv.◃ᵖ (tt , 1)))
Proper-undetermined = step01-proper , triv-no-proper

-- correspondingly: `full` is saturated, `triv` is not
full-saturated : Saturated predFib full
full-saturated o m sp a ne = tt

triv-not-saturated : ¬ (Saturated predFib triv)
triv-not-saturated sat = E.rec* (sat tt 1 (0 , refl) tt step01-≢)

-- PART C. SATURATION IS NOT ALWAYS ACHIEVABLE.

notFib : Fibered predSig ℓ-zero ℓ-zero
notFib .carrier _      = Bool
notFib .Split _ _      = Unit
notFib .parts _ m _ _  = not m

module N = Div notFib

-- deg≤ instantiated at both elements, then antisymmetry: verbatim
-- `GroupObstruction.deg-const`, with `not` in place of `h ↦ h⁻¹ · m`.
not-deg-const : (G : Grading notFib) (b : Bool) → G .deg tt (not b) ≡ G .deg tt b
not-deg-const G b =
  ≤-antisym (G .deg≤ tt b tt tt)
            (subst (λ z → G .deg tt z ≤ G .deg tt (not b))
                   (notnot b)
                   (G .deg≤ tt (not b) tt tt))

not-≢ : (b : Bool) → ¬ (Path N.Elt (tt , not b) (tt , b))
not-≢ b e = ¬not≡ b (cong snd e)
  where
    ¬not≡ : (c : Bool) → ¬ (not c ≡ c)
    ¬not≡ false p = true≢false p
    ¬not≡ true  p = false≢true p

-- THEOREM 3.  No grading of `notFib` is saturated.
no-saturated : (G : Grading notFib) → ¬ (Saturated notFib G)
no-saturated G sat =
  ¬m<m (subst (λ n → n < G .deg tt true)
              (not-deg-const G true)
              (G .deg< tt true tt tt (sat tt true tt tt (not-≢ true))))
