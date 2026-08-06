{-# OPTIONS --lossy-unification #-}
{- The signature of monoids: a nullary unit and a binary product.

   Note this is ALSO the signature of commutative monoids, of groups
   before inverses are added, and of `(ℕ , +)`.  Commutativity is an
   EQUATION, so it changes the model and the isomorphisms
   (`TheoryGrammar.Equations`), never the signature.  Instances over
   this signature differ only in their `Split` -- which is the design
   claim, and is why it is worth having exactly one copy of this. -}
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
