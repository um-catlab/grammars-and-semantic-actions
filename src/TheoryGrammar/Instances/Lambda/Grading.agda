{-
  Every splitting of this substrate is proper.

  Grade a name 0 and a term by its node count; then every slot of every
  splitting is strictly smaller than the whole -- for `nm` slots
  trivially, since a term has at least one node.  So the guardedness
  side condition that a general substrate must discharge per description
  is discharged here ONCE, for the substrate.

  `recSize` is the recursor that buys: it recurses on FUEL, not on an
  accessibility proof, which is what makes closed terms reduce.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Grading where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Nat.Order
  using (_<_; ≤-refl; ≤-trans; suc-≤-suc; pred-≤-pred; zero-≤; ¬-<-zero;
         ≤SumLeft; ≤SumRight)
open import Cubical.Data.Empty as E using (⊥)

open import TheoryGrammar.Instances.Lambda.Signature
open import TheoryGrammar.Instances.Lambda.Substrate

module Grading (Name : Type₀) where

  open Terms Name

  size : Raw → ℕ
  size (var _)   = 1
  size (app u v) = suc (size u + size v)
  size (lam _ t) = suc (size t)

  grade : (s : LSort) → Carrier s → ℕ
  grade nm _ = 0
  grade tm t = size t

  proper : (o : LOp) (t : Raw) (sp : LSplit o t) (a : LAr o)
         → grade (LSortOf o a) (LParts o t sp a) < size t
  proper varOp _ (mkVar n)   _     = ≤-refl
  proper appOp _ (mkApp u v) true  = suc-≤-suc ≤SumLeft
  proper appOp _ (mkApp u v) false = suc-≤-suc ≤SumRight
  proper lamOp _ (mkLam n t) true  = suc-≤-suc zero-≤
  proper lamOp _ (mkLam n t) false = suc-≤-suc ≤-refl

  -- structural recursion on the grade, with the term never matched
  recSize : {M : Raw → Type₀}
          → ((t : Raw) → ((s : Raw) → size s < size t → M s) → M t)
          → (t : Raw) → M t
  recSize {M} f t = go (suc (size t)) t ≤-refl
    where
    go : (k : ℕ) (s : Raw) → size s < k → M s
    go zero    s p = E.rec (¬-<-zero p)
    go (suc k) s p = f s λ r q → go k r (≤-trans q (pred-≤-pred p))
