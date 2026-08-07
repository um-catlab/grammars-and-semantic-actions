{-
  Every splitting of this promodel is proper -- now at BOTH result
  sorts at once.

  The grading is genuinely three-sorted: names weigh 0, terms weigh
  their node count, and TYPES weigh their node count too.  That last is
  what makes `annOp` (whose slots are a term and a type) proper, and
  what makes `arrOp` proper inside the `ty` sort, so one statement
  covers all six operations.

  `recSize` is `TheoryGrammar.Recursion`'s fuel-indexed recursor at
  `size`; fuel, not `Acc`, is what makes closed terms reduce.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.SimplyTyped.Grading where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Nat using (ℕ; suc; _+_)
open import Cubical.Data.Nat.Order
  using (_<_; ≤-refl; suc-≤-suc; zero-≤; ≤SumLeft; ≤SumRight; <-weaken)
open import Cubical.Data.Unit using (Unit)

open import TheoryGrammar.Grading using (GradedFib; fib; deg; Proper; deg≤; deg<)
open import TheoryGrammar.Instances.SimplyTyped.Signature
open import TheoryGrammar.Instances.SimplyTyped.Fibered
import TheoryGrammar.Recursion as Rec

-- `tysize A` denotes the node count of the type `A`.
tysize : Ty → ℕ
tysize base      = 1
tysize (A ⇒ᵗ B) = suc (tysize A + tysize B)

module Grading (Name : Type₀) where

  open Terms Name

  -- `size t` denotes the node count of the term `t`, counting the nodes
  -- of an annotation's TYPE as well -- which is what makes `annOp`
  -- proper.
  size : Raw → ℕ
  size (var _)   = 1
  size (app u v) = suc (size u + size v)
  size (lam _ t) = suc (size t)
  size (ann t A) = suc (size t + tysize A)

  -- `grade s m` denotes the weight of a world at sort `s`: names weigh
  -- 0, terms and types weigh their node count.  One grading for all
  -- three sorts, so one statement covers all six operations.
  grade : (s : TSort) → Carrier s → ℕ
  grade nm _ = 0
  grade tm t = size t
  grade ty A = tysize A

  -- every slot of every splitting weighs strictly less than the whole
  proper : (o : TOp) (m : Carrier (TResult o)) (sp : TSplit o m) (a : TAr o)
         → grade (TSortOf o a) (TParts o m sp a) < grade (TResult o) m
  proper varOp  _ (mkVar n)   _     = ≤-refl
  proper appOp  _ (mkApp u v) true  = suc-≤-suc ≤SumLeft
  proper appOp  _ (mkApp u v) false = suc-≤-suc ≤SumRight
  proper lamOp  _ (mkLam n t) true  = suc-≤-suc zero-≤
  proper lamOp  _ (mkLam n t) false = suc-≤-suc ≤-refl
  proper annOp  _ (mkAnn t A) true  = suc-≤-suc ≤SumLeft
  proper annOp  _ (mkAnn t A) false = suc-≤-suc ≤SumRight
  proper baseOp _ mkBase      ()
  proper arrOp  _ (mkArr A B) true  = suc-≤-suc ≤SumLeft
  proper arrOp  _ (mkArr A B) false = suc-≤-suc ≤SumRight

  -- `grade` and `proper`, packaged as the framework's `GradedFib` --
  -- what `Guard`/`Hylo`/`Decidable.Guarded` take as input.  Without it
  -- the instance is silently excluded from all three; that was the gap
  -- the lambda instance had until `λGraded` was added.  `Proper` is
  -- `Unit` because every slot here is strictly smaller, with no side
  -- condition.
  stGraded : GradedFib stlcSig ℓ-zero ℓ-zero
  stGraded .fib             = stlcFib
  stGraded .deg             = grade
  stGraded .Proper _ _ _ _  = Unit
  stGraded .deg≤ o t sp a   = <-weaken (proper o t sp a)
  stGraded .deg< o t sp a _ = proper o t sp a

  -- Structural recursion on the grade, with the term never matched:
  -- `TheoryGrammar.Recursion.recSize` at `size`.  The grade taken there
  -- is a bare `Raw → ℕ`, not the `GradedFib` above, because the
  -- recursion `typecheck` needs runs at the `tm` sort alone.  Fuel, not
  -- `Acc`, is what makes closed terms reduce.
  recSize : {M : Raw → Type₀}
          → ((t : Raw) → ((s : Raw) → size s < size t → M s) → M t)
          → (t : Raw) → M t
  recSize {M} = Rec.recSize size {M}
