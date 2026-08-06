{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Sorting at ℕ: quicksort, its intrinsically-verified form, and mergesort. -}
module TheoryGrammar.Instances.Bags.Examples where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.List

open import TheoryGrammar.Instances.Bags.Mergesort ℕ

leℕ : ℕ → ℕ → Bool
leℕ zero    _       = true
leℕ (suc m) zero    = false
leℕ (suc m) (suc n) = leℕ m n

open Sort  leℕ
open MSort leℕ

_ : quicksort [] ≡ []
_ = refl

_ : quicksort (1 ∷ []) ≡ (1 ∷ [])
_ = refl

_ : quicksort (2 ∷ 1 ∷ []) ≡ (1 ∷ 2 ∷ [])
_ = refl

_ : quicksort (5 ∷ 3 ∷ 4 ∷ 1 ∷ 2 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
_ = refl

-- _ : quicksort (5 ∷ 3 ∷ 4 ∷ 1 ∷ 2 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
-- _ = refl


-- the verified version computes to the same answer, and its second
-- component is the permutation proof, produced by construction
_ : quicksortV (5 ∷ 3 ∷ 4 ∷ 1 ∷ 2 ∷ []) .fst ≡ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
_ = refl

_ : quicksortV (2 ∷ 2 ∷ 1 ∷ []) .fst ≡ (1 ∷ 2 ∷ 2 ∷ [])
_ = refl

_ : mergesort (5 ∷ 3 ∷ 4 ∷ 1 ∷ 2 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
_ = refl

_ : mergesort (2 ∷ 2 ∷ 1 ∷ []) ≡ (1 ∷ 2 ∷ 2 ∷ [])
_ = refl
