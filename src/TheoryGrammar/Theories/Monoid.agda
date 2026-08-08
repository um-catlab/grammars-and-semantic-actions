{-# OPTIONS --lossy-unification #-}
{- The signature of monoids: a nullary unit and a binary product. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Theories.Monoid where

open import Cubical.Data.Bool using (Bool)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty using (⊥)

open import TheoryGrammar.Base

data MonOp : Type₀ where
  nilop appop : MonOp

MonAr : MonOp → Type₀
MonAr nilop = ⊥
MonAr appop = Bool

monoidSig : SortedSig Unit ℓ-zero ℓ-zero
monoidSig .ops          = MonOp
monoidSig .arities      = MonAr
monoidSig .sortOf _ _   = tt
monoidSig .resultSort _ = tt

-- `boolΠ`, the binary arity's eliminator, is in `TheoryGrammar.Base`: it
-- is a fact about `Bool`, so a signature that is binary WITHOUT being the
-- monoid signature (`λSig`, `spanSig`, ...) must not have to import this
-- file to get it.
