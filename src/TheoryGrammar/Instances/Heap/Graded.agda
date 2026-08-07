{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  HEAPS ARE GRADED -- so separation logic supports Löb induction.

  Worth reading beside `Instances/Group/NoGrading`.  There, `GroupLike`
  (every element occurs in a splitting of every other) forces `deg` to be
  constant, hence `Proper` to be empty, hence `μ` to degenerate to its own
  shape functor: over a group there are no well-founded inductive grammars
  at all.  Heaps are the opposite case, and the reason fits on one line --

      Disj u v w   ⟹   alloc u + alloc v ≡ alloc w

  -- so a part never owns more than the whole, and owns strictly less as
  soon as its sibling owns anything.  That is exactly `deg≤` and `deg<`.

  NOTE WHAT THE DEGREE IS NOT.  `length` does not work: `Disj` preserves
  length (the bitmaps are the same width), so length is CONSTANT on every
  splitting and would give precisely the degenerate grading the group
  result describes.  The right degree counts OWNERSHIP -- the resource the
  operation actually divides.  That is the general lesson: grade by what
  the operation consumes, and a grading exists exactly when doing so makes
  the divisibility order well-founded.

  Consequence: `Ind`, `Guard`, `hyloC` and `löb` are all available over
  heaps.  A recursive separation-logic predicate -- a list segment, say --
  is a `μ` of a description, guarded because each recursive occurrence
  sits at a strictly smaller heap.  Partiality costs nothing here.
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Heap.Graded where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.List
open import Cubical.Data.Empty as E using (⊥)

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded

open import TheoryGrammar.Instances.Heap.Connectives public

-- ==================================================================
-- The degree: how many locations the heap owns.
-- ==================================================================

alloc : Heap → ℕ
alloc []          = 0
alloc (true  ∷ w) = suc (alloc w)
alloc (false ∷ w) = alloc w

-- PRIMITIVE (phase 1): ownership is additive across a disjoint union.
-- The (true,true) case that would have broken this is exactly the
-- constructor `Disj` does not have.
allocDisj : ∀ {u v w} → Disj u v w → alloc u + alloc v ≡ alloc w
allocDisj dnil      = refl
allocDisj (dl d)    = cong suc (allocDisj d)
allocDisj (dr d)    = +-suc _ _ ∙ cong suc (allocDisj d)
allocDisj (dnone d) = allocDisj d

private
  -- a ≤ a + b, always
  weak : (a b : ℕ) → a ≤ a + b
  weak a b = b , +-comm b a

  -- ... and strictly, as soon as b owns something
  strict : (a b : ℕ) → 0 < b → a < a + b
  strict a zero    p = E.rec (¬-<-zero p)
  strict a (suc b) _ =
    subst (suc a ≤_) (sym (+-suc a b)) (suc-≤-suc (weak a b))

-- ==================================================================
-- THE GRADING.  `Proper` says the SIBLING owns something -- the same
-- phrasing every other instance uses, and the one that dodges needing
-- `Discrete (arities o)`.
-- ==================================================================

heapGrading : Grading heapFib
heapGrading .deg _ = alloc

heapGrading .Proper empOp  w sp ()
heapGrading .Proper joinOp w (u , v , _) b = 0 < alloc (if b then v else u)

heapGrading .deg≤ empOp  w sp ()
heapGrading .deg≤ joinOp w (u , v , d) true  =
  subst (alloc u ≤_) (allocDisj d) (weak (alloc u) (alloc v))
heapGrading .deg≤ joinOp w (u , v , d) false =
  subst (alloc v ≤_) (+-comm (alloc v) (alloc u) ∙ allocDisj d)
        (weak (alloc v) (alloc u))

heapGrading .deg< empOp  w sp ()
heapGrading .deg< joinOp w (u , v , d) true  pr =
  subst (alloc u <_) (allocDisj d) (strict (alloc u) (alloc v) pr)
heapGrading .deg< joinOp w (u , v , d) false pr =
  subst (alloc v <_) (+-comm (alloc v) (alloc u) ∙ allocDisj d)
        (strict (alloc v) (alloc u) pr)

-- ... and bundled, so `Ind` / `Guard` / `hyloC` apply.
heapGraded : GradedFib pcmSig ℓ-zero ℓ-zero
heapGraded = graded heapFib heapGrading
