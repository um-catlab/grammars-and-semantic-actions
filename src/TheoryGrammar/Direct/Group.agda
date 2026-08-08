{- `NoGrading` RE-READ: THE DIVISIBILITY CATEGORY OF A GROUP IS INDISCRETE,
   HENCE NOT DIRECT, HENCE THERE IS NO INDUCTION. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Direct.Group where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as E using (⊥)
open import Cubical.Relation.Nullary using (¬_)

open import Cubical.Categories.Functor
open Functor
open import Cubical.Categories.Direct.StrictDownset using (↡Psh)

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Grading
open import TheoryGrammar.Direct.Divisibility
open import TheoryGrammar.Instances.Group.NoGrading
  using (GroupLike ; module GroupObstruction)

private variable ℓ ℓ' ℓX ℓP ℓM : Level

module _ {σ : SortedSig Unit ℓ ℓ'} (Fib : Fibered σ ℓX ℓP)
         (o : σ .ops) (a : σ .arities o) (gl : GroupLike Fib o a) where

  open Div Fib

  -- THEOREM. `Div Fib` is INDISCRETE.

  chaotic₁ : (n m : Elt) → n ◃₁ m
  chaotic₁ n m =
    subst (λ z → (tt , z) ◃₁ m)
          (gl (m .snd) (n .snd) .snd)
          (slot o (m .snd) (gl (m .snd) (n .snd) .fst) a)

  chaotic : (n m : Elt) → n ≼ m
  chaotic n m = one (chaotic₁ n m)

  -- so `Flat` holds trivially here (everything is a one-step factor):
  -- the group is the degenerate case in BOTH directions, maximal
  -- divisibility and no associativity obligation.
  chaotic-flat : {n k m : Elt} → n ◃₁ k → k ◃₁ m → n ◃₁ m
  chaotic-flat {n} {k} {m} _ _ = chaotic₁ n m

  module _ (G : Grading Fib) where

    open Div.Graded Fib G

    private
      module GO = GroupObstruction (graded Fib G) o a gl

    -- CITED, not reproved: `GroupObstruction.deg-const`.
    deg-const : (n m : Elt) → degE n ≡ degE m
    deg-const n m = GO.deg-const (n .snd) (m .snd)

    -- Every consequence, read off the category.

    -- the degree functor is constant, so NO map is ≺-strict
    no-strict : (n m : Elt) → ¬ (n ≺ m)
    no-strict n m p = ¬m<m (subst (λ z → z < degE m) (deg-const n m) p)

    -- ... in particular no divisibility is proper (`Degenerate.no-proper`)
    no-proper : (n m : Elt) → ¬ (n ◃ᵖ m)
    no-proper n m s = no-strict n m (strict₁ s)

    -- ... so the strict-downset sieve of `Direct/StrictDownset.agda` is
    -- EMPTY at every object.  `↡-proper` there says ↡ omits the
    -- identity; here it omits everything.
    ↡-empty : (x y : Elt) → ¬ ⟨ ↡Psh DivDirect↑ x .F-ob y ⟩
    ↡-empty x y (f , q) = no-strict y x (lower q)

    -- ... hence the sieve modality is terminal ...
    ▷ᵈ-terminal : {A : Elt → Type ℓM} (x : Elt)
                → (y : Elt) → ⟨ ↡Psh DivDirect↑ x .F-ob y ⟩ → A y
    ▷ᵈ-terminal x y h = E.rec (↡-empty x y h)

    -- ... and so, here, is the graded one.  (Compare `Direct/Later.agda`,
    -- where they are separated: the group obstruction kills both.)
    ▷ᵍ-terminal : {A : Elt → Type ℓM} (x : Elt) → (y : Elt) → y ≺ x → A y
    ▷ᵍ-terminal x y p = E.rec (no-strict y x p)
