{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- WHAT THE EVALUATOR SHARES, AND WHAT IT DOES NOT. -}
module TheoryGrammar.ShareProbe where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Unit
open import Cubical.Induction.WellFounded

open import TheoryGrammar.Enumerable
import TheoryGrammar.DP as D
open import TheoryGrammar.DPTests
  using (_≺_; ≺-here; ≺-there; ≺-wf; down; ∈down; fibTab)

-- ================================================================ ℕ
-- the baseline: a cell that is a number.  Linear.
_ : fibTab 60 ≡ 1548008755920
_ = refl

-- ============================================================ X → B The
-- SAME recurrence, with the cell a function out of `Bool`.
module Fun where
  open D.DP _≺_ ≺-wf (λ _ → Bool → ℕ) public

  st : Step
  st zero          _   _     = 0
  st (suc zero)    _   _     = 1
  st (suc (suc n)) rec true  = rec (suc n) ≺-here false + rec n (≺-there ≺-here) true
  st (suc (suc n)) rec false = rec (suc n) ≺-here true  + rec n (≺-there ≺-here) false

  chD : (n : ℕ) → Chain (down n)
  chD zero    = nil
  chD (suc n) = cons n (∈down n) (chD n)

  tab : ℕ → ℕ
  tab n = solveAt st (chD (suc n)) n (∈down (suc n) n ≺-here) true

-- ============================================================== A × B
-- The same information again, as DATA.
module Pair where
  open D.DP _≺_ ≺-wf (λ _ → ℕ × ℕ) public

  st : Step
  st zero          _   = 0 , 0
  st (suc zero)    _   = 1 , 1
  st (suc (suc n)) rec =
      rec (suc n) ≺-here .snd + rec n (≺-there ≺-here) .fst
    , rec (suc n) ≺-here .fst + rec n (≺-there ≺-here) .snd

  chD : (n : ℕ) → Chain (down n)
  chD zero    = nil
  chD (suc n) = cons n (∈down n) (chD n)

  tab : ℕ → ℕ
  tab n = solveAt st (chD (suc n)) n (∈down (suc n) n ≺-here) .fst

-- THE MEASUREMENT.  Both lines below are `fib`, tabulated by the same
-- `build` over the same `Chain`.  Only the cell's type differs, and
-- only one of them can be asked for `60`.

_ : Pair.tab 60 ≡ 1548008755920
_ = refl

_ : Fun.tab 30 ≡ 832040        -- `Fun.tab 60` does not terminate
_ = refl
