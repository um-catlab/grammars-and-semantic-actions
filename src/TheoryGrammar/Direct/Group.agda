{-
  `NoGrading` RE-READ: THE DIVISIBILITY CATEGORY OF A GROUP IS
  INDISCRETE, HENCE NOT DIRECT, HENCE THERE IS NO INDUCTION.

  `Instances/Group/NoGrading.agda` proves the rigidity theorem -- every
  grading of a group-like promodel has constant degree, so no splitting
  is proper and no description is guarded.  It closes by NAMING the
  general criterion:

      inductive grammars exist exactly when the DIVISIBILITY PREORDER
      of the theory is well-founded.

  `Direct/Divisibility.agda` builds that preorder.  This file completes
  the circuit: it shows that the preorder of a group-like promodel is
  INDISCRETE (`chaotic₁` -- every element is an immediate factor of every
  element, in ONE step, no closure needed), and reads every conclusion of
  `NoGrading` off the categorical structure.

  NOTHING HERE IS RE-PROVED.  `GroupLike`, `GroupObstruction.deg-const`
  and `Degenerate.no-proper` / `no-guarded` are imported from
  `TheoryGrammar.Instances.Group.NoGrading` and cited.  The content added
  is only the translation:

      NoGrading                     here
      ---------                     ----
      GroupLike o a                 `_◃₁_` is the total relation
      deg-const                     the degree functor is constant
      no-proper                     no map of Div is ≺-strict
      (new)                         ↡x is EMPTY at every object x
      no-guarded                    ▷ is terminal, löb is the identity

  The last line is the sharp form.  `Direct/StrictDownset.agda`'s `▷Psh`
  is "sections over ↡"; when ↡ is empty, every family has exactly one
  section over it, so `▷ A` is terminal and a step `▷ A x → A x` is just
  an element of `A x`.  löb then reads: from `∀ x. A x` conclude
  `∀ x. A x`.  That is not a defect of the construction, it is the
  construction reporting honestly that there is nothing to recurse on.

  ------------------------------------------------------------------
  A REMARK THE TWO FILES TOGETHER MAKE POSSIBLE.

  `Direct/Later.agda` separates two modalities -- the graded `▷ᵍ`
  (indexed by lower DEGREE) and the sieve `▷ᵈ` (indexed by lower
  degree AND divisibility).  They differ in general, and `▷ᵍ` is
  strictly stronger.  At a group they COINCIDE, because both are
  terminal: `▷ᵈ` because ↡ is empty, `▷ᵍ` because the degree is constant.
  So the group obstruction is invisible to the distinction -- it kills
  both modalities at once, which is why `NoGrading` never had to choose
  between them.
-}
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

  -- ================================================================
  -- THEOREM.  `Div Fib` is INDISCRETE.
  --
  -- `GroupLike` says slot `a` of the splittings of `m` ranges over the
  -- whole carrier -- in a group, `m = h · (h⁻¹ m)`.  So the one-step
  -- relation is total, no reflexive-transitive closure is needed, and
  -- the preorder has a single equivalence class: it "collapses to a
  -- point" in the precise sense that its poset reflection is Unit.
  -- ================================================================

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

    -- ==============================================================
    -- Every consequence, read off the category.
    -- ==============================================================

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
