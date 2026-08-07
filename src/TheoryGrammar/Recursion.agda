{-
  THE FUEL-INDEXED RECURSOR, generic in the carrier and the motive.

  Given any grade `size : C → ℕ`, `recSize` turns "the recursive calls
  sit at strictly smaller grades" into a total function.  It is the
  recursor the checkers of this development actually run on --
  `Lambda/ScopeCheck` and `SimplyTyped/Check` both cite it at their
  `size`.

  It recurses on FUEL -- a natural bound, discharged by `≤-refl` at the
  top -- and NOT on an accessibility proof.  That is load bearing, not
  stylistic: an `Acc`-based recursor is blocked on a proof that does not
  reduce, while `go` matches only the fuel and never the carrier, so a
  closed argument computes.  Every test downstream is a `refl`.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Recursion where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Nat.Order
  using (_<_; ≤-refl; ≤-trans; pred-≤-pred; ¬-<-zero)
open import Cubical.Data.Empty as E using (⊥)

private variable ℓ ℓM : Level

-- Structural recursion on the grade, with the carrier never matched.
--
-- The grade is a bare `C → ℕ` rather than a `GradedFib`, for three
-- reasons.  (i) Nothing but the grade is used: no fibration, no
-- splitting, and none of `Proper`/`deg≤`/`deg<` -- the descent proofs
-- are supplied by the CALLER, at its own recursive calls.  (ii) A
-- `GradedFib` grades every sort of a signature at once, whereas this
-- recursion runs at ONE sort; `SimplyTyped` has no `GradedFib` at all
-- and would be excluded.  (iii) `deg` is a record field, so routing the
-- fuel through one puts a projection between the caller's `size t` and
-- the numeral it must reduce to.  Instances that do have a `GradedFib`
-- cite this at `deg s`, losing nothing.
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
