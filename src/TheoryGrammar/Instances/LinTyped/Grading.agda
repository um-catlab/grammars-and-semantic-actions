{- Every splitting of this `Fibered` is proper -- at BOTH result sorts at
   once. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.LinTyped.Grading where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Nat using (ℕ; suc; _+_)
open import Cubical.Data.Nat.Order
  using (_<_; ≤-refl; suc-≤-suc; zero-≤; ≤SumLeft; ≤SumRight; <-weaken)
open import Cubical.Data.Unit using (Unit)

open import TheoryGrammar.Grading using (GradedFib; fib; deg; Proper; deg≤; deg<)
open import TheoryGrammar.Instances.LinTyped.Signature
open import TheoryGrammar.Instances.LinTyped.Fibered
import TheoryGrammar.Recursion as Rec

-- `tysize A` denotes the node count of the type `A`.
tysize : Ty → ℕ
tysize base       = 1
tysize (A ⊸ᵗ B)  = suc (tysize A + tysize B)

-- `size t` denotes the node count of the term `t`, counting the nodes
-- of an annotation's TYPE as well -- which is what makes `annOp`
-- proper.
size : Raw → ℕ
size (var _)   = 1
size (app u v) = suc (size u + size v)
size (lam t)   = suc (size t)
size (ann t A) = suc (size t + tysize A)

-- `grade s m` denotes the weight of a world at sort `s`: indices weigh
-- 0, terms and types weigh their node count.
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
proper lamOp  _ (mkLam t)   _     = suc-≤-suc ≤-refl
proper annOp  _ (mkAnn t A) true  = suc-≤-suc ≤SumLeft
proper annOp  _ (mkAnn t A) false = suc-≤-suc ≤SumRight
proper baseOp _ mkBase      ()
proper lolOp  _ (mkLol A B) true  = suc-≤-suc ≤SumLeft
proper lolOp  _ (mkLol A B) false = suc-≤-suc ≤SumRight

-- `grade` and `proper`, packaged as the framework's `GradedFib` --
-- what `Guard`/`Hylo`/`Decidable.Guarded` take as input.
linGraded : GradedFib linSig ℓ-zero ℓ-zero
linGraded .fib             = linFib
linGraded .deg             = grade
linGraded .Proper _ _ _ _  = Unit
linGraded .deg≤ o t sp a   = <-weaken (proper o t sp a)
linGraded .deg< o t sp a _ = proper o t sp a

-- Structural recursion on the grade, with the term never matched.
recSize : {M : Raw → Type₀}
        → ((t : Raw) → ((s : Raw) → size s < size t → M s) → M t)
        → (t : Raw) → M t
recSize {M} = Rec.recSize size {M}
