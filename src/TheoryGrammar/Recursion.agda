{- THE FUEL-INDEXED RECURSOR, generic in the carrier and the motive. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Recursion where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Nat.Order
  using (_<_; ≤-refl; ≤-trans; pred-≤-pred; ¬-<-zero)
open import Cubical.Data.Empty as E using (⊥)

private variable ℓ ℓM : Level

-- Structural recursion on the grade, with the carrier never matched.
recSize : {C : Type ℓ} (size : C → ℕ) {M : C → Type ℓM}
        → ((t : C) → ((s : C) → size s < size t → M s) → M t)
        → (t : C) → M t
recSize {C = C} size {M} f t = go (suc (size t)) t ≤-refl
  where
  -- `go` matches ONLY `k`.  Were it to match `s` the carrier would have
  -- to reduce before the recursion could, and closed terms would stall.
  go : (k : ℕ) (s : C) → size s < k → M s
  go zero    s p = E.rec (¬-<-zero p)
  go (suc k) s p = f s λ r q → go k r (≤-trans q (pred-≤-pred p))
