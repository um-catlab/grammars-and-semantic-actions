{-
  The signature of lambda ASTs: two sorts, three operations.

  `lamOp` is the point of the exercise -- its two slots have DIFFERENT
  sorts, so `sortOf` is non-constant and the sort machinery is actually
  exercised.  A single-sorted presentation has to index the OPERATIONS
  by names (`varOp n`, `lamOp n`, so `ops` is as big as `Name`); here
  names are a sort instead, so there are exactly three operations and
  `⌈ n ⌉ : Name → Type` is what pins a binder.
-}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Instances.Lambda.Signature where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Unit

open import TheoryGrammar.Base

data LSort : Type₀ where
  nm tm : LSort

data LOp : Type₀ where
  varOp appOp lamOp : LOp

LAr : LOp → Type₀
LAr varOp = Unit
LAr appOp = Bool
LAr lamOp = Bool

-- `lamOp` binds a NAME and a TERM: this is the non-constant `sortOf`
LSortOf : (o : LOp) → LAr o → LSort
LSortOf varOp _     = nm
LSortOf appOp _     = tm
LSortOf lamOp true  = nm
LSortOf lamOp false = tm

λSig : SortedSig LSort ℓ-zero ℓ-zero
λSig .ops          = LOp
λSig .arities      = LAr
λSig .sortOf       = LSortOf
λSig .resultSort _ = tm
