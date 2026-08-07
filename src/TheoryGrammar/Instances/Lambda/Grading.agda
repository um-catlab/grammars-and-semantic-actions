{-
  Every splitting of this promodel is proper.

  Grade a name 0 and a term by its node count; then every slot of every
  splitting is strictly smaller than the whole -- for `nm` slots
  trivially, since a term has at least one node.  So the guardedness
  side condition that a general promodel must discharge per description
  is discharged here ONCE, for the promodel.

  `λGraded` packages that as the framework's `GradedFib`, which is what
  `Guard`/`Hylo`/`Decidable.Guarded` take as input.  `recSize` is the
  recursor `ScopeCheck` actually runs on; it is `TheoryGrammar.Recursion`'s
  fuel-indexed recursor at `size`, named here so that module has a local
  spelling.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Grading where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Nat using (ℕ; suc; _+_)
open import Cubical.Data.Nat.Order
  using (_<_; ≤-refl; <-weaken; suc-≤-suc; zero-≤; ≤SumLeft; ≤SumRight)
open import Cubical.Data.Unit using (Unit)

open import TheoryGrammar.Grading using (GradedFib; fib; deg; Proper; deg≤; deg<)
import TheoryGrammar.Recursion as Rec
open import TheoryGrammar.Instances.Lambda.Signature
open import TheoryGrammar.Instances.Lambda.Fibered

module Grading (Name : Type₀) where

  open Terms Name

  -- `size t` DENOTES: the number of nodes in `t`.  It is a RECURSION
  -- MEASURE, not an observation -- the observable node count is the
  -- term `Initial.size! : ⊤G ⊢ Δ ℕ`.
  size : Raw → ℕ
  size (var _)   = 1
  size (app u v) = suc (size u + size v)
  size (lam _ t) = suc (size t)

  grade : (s : LSort) → Carrier s → ℕ
  grade nm _ = 0
  grade tm t = size t

  -- `proper` DENOTES: "every slot of every splitting is strictly
  -- smaller than the whole" -- the descent proof `ScopeCheck` runs on.
  proper : (o : LOp) (t : Raw) (sp : LSplit o t) (a : LAr o)
         → grade (LSortOf o a) (LParts o t sp a) < size t
  proper varOp _ (mkVar n)   _     = ≤-refl
  proper appOp _ (mkApp u v) true  = suc-≤-suc ≤SumLeft
  proper appOp _ (mkApp u v) false = suc-≤-suc ≤SumRight
  proper lamOp _ (mkLam n t) true  = suc-≤-suc zero-≤
  proper lamOp _ (mkLam n t) false = suc-≤-suc ≤-refl

  -- ... which is exactly the framework's grading structure, so it is
  -- packaged as one.  `Proper = Unit`: over a SYNTAX every slot is a
  -- proper part, and that is the finding -- a resource substrate has to
  -- say which slots are proper, because a usage can split off an empty
  -- part while a subterm is always strictly smaller.  This is what
  -- `Guard`/`Hylo`/`Decidable.Guarded` take as their input.
  λGraded : GradedFib λSig ℓ-zero ℓ-zero
  λGraded .fib             = λFib
  λGraded .deg             = grade
  λGraded .Proper _ _ _ _  = Unit
  λGraded .deg≤ o t sp a   = <-weaken (proper o t sp a)
  λGraded .deg< o t sp a _ = proper o t sp a

  -- Structural recursion on the grade, with the term never matched:
  -- `TheoryGrammar.Recursion.recSize` at `size`.  It is stated there
  -- over a bare grade function rather than over `λGraded`, because the
  -- recursion runs at ONE sort and uses nothing else the record carries;
  -- see the note there.  Fuel, not `Acc`, so closed terms reduce.
  recSize : {M : Raw → Type₀}
          → ((t : Raw) → ((s : Raw) → size s < size t → M s) → M t)
          → (t : Raw) → M t
  recSize {M} = Rec.recSize size {M}
