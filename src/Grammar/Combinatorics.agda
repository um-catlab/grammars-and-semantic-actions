{-
  The (ℕ,+) substrate: grammars graded by size.

  This is the same construction as Grammar.SplitExperiment with the
  free monoid replaced by (ℕ,+).  Day convolution becomes the Cauchy
  product, μ becomes a recursive combinatorial specification, and an
  ISOMORPHISM OF GRAMMARS IS A BIJECTIVE PROOF.

  Two classical results, proved as equivalences:
    * compositions of n into 1s and 2s are counted by Fibonacci
    * binary trees satisfy the Catalan convolution recurrence
-}
module Grammar.Combinatorics where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.SumFin

-- ==================================================================
-- 1.  The substrate.  Splitting is an inductive family, not `i + j ≡ n`.
-- ==================================================================

Gr : Type₁
Gr = ℕ → Type₀

data Add : ℕ → ℕ → ℕ → Type₀ where
  z : ∀ {n} → Add 0 n n
  s : ∀ {i j n} → Add i j n → Add (suc i) j (suc n)

_⊗_ : Gr → Gr → Gr
(A ⊗ B) n = Σ[ i ∈ ℕ ] Σ[ j ∈ ℕ ] (Add i j n × A i × B j)

data Ε : ℕ → Type₀ where
  mk : Ε 0

data At (k : ℕ) : ℕ → Type₀ where
  mk : At k k

-- ==================================================================
-- 2.  Compositions of n into parts 1 and 2.
--     Grammar:  C = ε ⊕ At 1 ⊗ C ⊕ At 2 ⊗ C
-- ==================================================================

data Comp12 : ℕ → Type₀ where
  nil : Comp12 0
  one : ∀ {n} → Comp12 n → Comp12 (suc n)
  two : ∀ {n} → Comp12 n → Comp12 (suc (suc n))

-- The recurrence, as a bijection.  This IS the bijective proof.
comp12-rec : ∀ n → Iso (Comp12 (suc (suc n))) (Comp12 (suc n) ⊎ Comp12 n)
Iso.fun (comp12-rec n) (one c) = inl c
Iso.fun (comp12-rec n) (two c) = inr c
Iso.inv (comp12-rec n) (inl c) = one c
Iso.inv (comp12-rec n) (inr c) = two c
Iso.sec (comp12-rec n) (inl c) = refl
Iso.sec (comp12-rec n) (inr c) = refl
Iso.ret (comp12-rec n) (one c) = refl
Iso.ret (comp12-rec n) (two c) = refl

fib : ℕ → ℕ
fib 0 = 1
fib 1 = 1
fib (suc (suc n)) = fib (suc n) + fib n

comp12-0 : Iso (Comp12 0) (Fin 1)
Iso.fun comp12-0 nil = inl tt
Iso.inv comp12-0 (inl tt) = nil
Iso.sec comp12-0 (inl tt) = refl
Iso.ret comp12-0 nil = refl

comp12-1 : Iso (Comp12 1) (Fin 1)
Iso.fun comp12-1 (one nil) = inl tt
Iso.inv comp12-1 (inl tt) = one nil
Iso.sec comp12-1 (inl tt) = refl
Iso.ret comp12-1 (one nil) = refl

-- THEOREM: the compositions of n into 1s and 2s are Fibonacci-many.
comp12-count : ∀ n → Comp12 n ≃ Fin (fib n)
comp12-count 0 = isoToEquiv comp12-0
comp12-count 1 = isoToEquiv comp12-1
comp12-count (suc (suc n)) =
  isoToEquiv (comp12-rec n)
  ∙ₑ ⊎-equiv (comp12-count (suc n)) (comp12-count n)
  ∙ₑ SumFin⊎≃ (fib (suc n)) (fib n)

-- ==================================================================
-- 3.  Binary trees, graded by number of internal nodes.
--     Grammar:  T = ε ⊕ At 1 ⊗ T ⊗ T   (here: node carries the split)
-- ==================================================================

data Bin : ℕ → Type₀ where
  leaf : Bin 0
  node : ∀ {i j n} → Add i j n → Bin i → Bin j → Bin (suc n)

-- THEOREM (Catalan recurrence, as a bijection):
--    T_{n+1} ≅ Σ_{i+j=n} T_i × T_j
catalan-rec : ∀ n → Iso (Bin (suc n)) ((Bin ⊗ Bin) n)
Iso.fun (catalan-rec n) (node sp l r) = _ , _ , sp , l , r
Iso.inv (catalan-rec n) (i , j , sp , l , r) = node sp l r
Iso.sec (catalan-rec n) (i , j , sp , l , r) = refl
Iso.ret (catalan-rec n) (node sp l r) = refl
