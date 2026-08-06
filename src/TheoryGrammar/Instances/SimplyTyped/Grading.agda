{-
  Every splitting of this promodel is proper -- now at BOTH result
  sorts at once.

  The grading is genuinely three-sorted: names weigh 0, terms weigh
  their node count, and TYPES weigh their node count too.  That last is
  what makes `annOp` (whose slots are a term and a type) proper, and
  what makes `arrOp` proper inside the `ty` sort, so one statement
  covers all six operations.

  `recSize` recurses on FUEL, so closed terms reduce.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.SimplyTyped.Grading where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Nat.Order
  using (_<_; ≤-refl; ≤-trans; suc-≤-suc; pred-≤-pred; zero-≤; ¬-<-zero;
         ≤SumLeft; ≤SumRight)
open import Cubical.Data.Empty as E using (⊥)

open import TheoryGrammar.Instances.SimplyTyped.Signature
open import TheoryGrammar.Instances.SimplyTyped.Fibered

tysize : Ty → ℕ
tysize base      = 1
tysize (A ⇒ᵗ B) = suc (tysize A + tysize B)

module Grading (Name : Type₀) where

  open Terms Name

  size : Raw → ℕ
  size (var _)   = 1
  size (app u v) = suc (size u + size v)
  size (lam _ t) = suc (size t)
  size (ann t A) = suc (size t + tysize A)

  grade : (s : TSort) → Carrier s → ℕ
  grade nm _ = 0
  grade tm t = size t
  grade ty A = tysize A

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

  -- structural recursion on the grade, with the term never matched
  recSize : {M : Raw → Type₀}
          → ((t : Raw) → ((s : Raw) → size s < size t → M s) → M t)
          → (t : Raw) → M t
  recSize {M} f t = go (suc (size t)) t ≤-refl
    where
    go : (k : ℕ) (s : Raw) → size s < k → M s
    go zero    s p = E.rec (¬-<-zero p)
    go (suc k) s p = f s λ r q → go k r (≤-trans q (pred-≤-pred p))
