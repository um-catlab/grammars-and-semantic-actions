{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  HEAPS ARE GRADED -- so separation logic supports Löb induction.

  Read beside `Instances/Group/NoGrading`.  There, `GroupLike` (every
  element occurs in a splitting of every other) forces `deg` to be
  constant, hence `Proper` empty, hence `μ` degenerate to its own shape
  functor: over a group there are no well-founded inductive grammars at
  all.  Heaps are the opposite case, and for a reason worth naming --

      partiality RESTRICTS the splittings, and restricting splittings
      can only help a grading.

  `HeapSplit` is `CellSplit` with the `u # v` conjunct added, so every
  heap splitting is a cell splitting; `deg≤` and `deg<` are inherited
  from `Ilv` alone and never mention `_#_`.  Partiality costs nothing
  here, which is the complement of the `NoPoint` result: it obstructs the
  TOTAL POINT and not the RECURSION.

  Consequence: `Ind`, `Guard`, `hyloC` and `löb` are available over
  heaps, so a recursive separation-logic predicate -- a list segment, say
  -- is a `μ` of a description, guarded because each recursive occurrence
  sits at a strictly smaller heap.
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Heap.Graded where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.List using (List; []; _∷_; length)
open import Cubical.Data.Empty as E using (⊥)

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded

open import TheoryGrammar.Instances.Heap.Connectives public

-- ==================================================================
-- The degree is the number of cells, and every clause is about `Ilv`
-- alone -- `_#_` never appears.  These are `Bags/Graded`'s length
-- lemmas at `Cell`; the duplication is because `Heap` declares its own
-- `Ilv` rather than instantiating the bag one.
-- ==================================================================

-- PRIMITIVE (phase 1): recursion on the interleaving.
ilvLenL : ∀ {u v w} → Ilv u v w → length u ≤ length w
ilvLenL nil       = ≤-refl
ilvLenL (left s)  = suc-≤-suc (ilvLenL s)
ilvLenL (right s) = ≤-suc (ilvLenL s)

ilvLenR : ∀ {u v w} → Ilv u v w → length v ≤ length w
ilvLenR nil       = ≤-refl
ilvLenR (left s)  = ≤-suc (ilvLenR s)
ilvLenR (right s) = suc-≤-suc (ilvLenR s)

-- ... and a NONEMPTY complement makes the slot strictly smaller.
ilvLenL< : ∀ {u v w} → Ilv u v w → 0 < length v → length u < length w
ilvLenL< nil       pr = E.rec (¬-<-zero pr)
ilvLenL< (left s)  pr = suc-≤-suc (ilvLenL< s pr)
ilvLenL< (right s) pr = suc-≤-suc (ilvLenL s)

ilvLenR< : ∀ {u v w} → Ilv u v w → 0 < length u → length v < length w
ilvLenR< nil       pr = E.rec (¬-<-zero pr)
ilvLenR< (left s)  pr = suc-≤-suc (ilvLenR s)
ilvLenR< (right s) pr = suc-≤-suc (ilvLenR< s pr)

-- ==================================================================
-- THE GRADING.  `Proper` says the SIBLING is nonempty -- the phrasing
-- every instance uses, and the one that dodges needing
-- `Discrete (arities o)`.  `boolΠ` supplies each slot's case.
-- ==================================================================

heapGrading : Grading heapFib
heapGrading .deg _ = length

heapGrading .Proper nilop h sp ()
heapGrading .Proper appop h (u , v , _) b = 0 < length (boolΠ {M = λ _ → Heap} v u b)

heapGrading .deg≤ nilop h sp ()
heapGrading .deg≤ appop h (u , v , i , _) =
  boolΠ {M = λ a → length (boolΠ {M = λ _ → Heap} u v a) ≤ length h}
        (ilvLenL i) (ilvLenR i)

heapGrading .deg< nilop h sp ()
heapGrading .deg< appop h (u , v , i , _) =
  boolΠ {M = λ a → 0 < length (boolΠ {M = λ _ → Heap} v u a) → length (boolΠ {M = λ _ → Heap} u v a) < length h}
        (ilvLenL< i) (ilvLenR< i)

-- ... bundled, so `Ind` / `Guard` / `hyloC` apply over a PARTIAL promodel.
heapGraded : GradedFib monoidSig ℓ-zero ℓ-zero
heapGraded = graded heapFib heapGrading
