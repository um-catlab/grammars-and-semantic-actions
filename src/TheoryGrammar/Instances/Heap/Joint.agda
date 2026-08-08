{- HEAPS, THROUGH THE SAME JOINT LEMMA. `Connectives.noHeapPoint` goes
   through a copy of the lemma kept local to this directory; here it is re-
   derived from the upstream `TheoryGrammar.Domain.no-point-joint`, the one
   `Field/Joint` also uses. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Heap.Joint where

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Domain
open import TheoryGrammar.Instances.Heap.Located

-- only the NEW names: the connectives are already in scope from
-- `Connectives`, and a second copy of them would be ambiguous.
open JointDomain heapFib
  using (Tuple; Composableᴳ; Composable; Domˢ; Imageˢ; ¬G_;
         point→composable; no-point-joint; no-point-internal;
         joint→dom; SlotwiseSuffices)

-- 1.  THE BAD TUPLE: one cell, twice.

cell : Heap
cell = single 0 v0

selfTuple : Tuple appop
selfTuple = boolΠ cell cell

-- INTERNAL: no heap is the disjoint join of that tuple.  `⊗ˢ-map`
-- respells the slot family, then `apart-self` -- "a location cannot be
-- owned twice" -- is the whole content.
not-composable-self : Composableᴳ appop selfTuple ⊢ ⊥G
not-composable-self =
  apart-self 0 v0
  ∘g ⊗ˢ-map appop {A = λ a → ⌈ selfTuple a ⌉}
                  {B = boolΠ ⌈ cell ⌉ ⌈ cell ⌉} respell

-- 2.  THEOREM.  `heapFib` has no total point -- through the JOINT
--     lemma, the same one the field goes through.

noHeapPoint-joint : LaxPoint heapFib → ⊥
noHeapPoint-joint = no-point-internal appop selfTuple not-composable-self

not-composable : Composable appop selfTuple → ⊥
not-composable c = E.rec* (not-composable-self (c .fst) (c .snd))

-- 3. AND THE CONVERSE IMPLICATION IS REFUTED.

slotwise-self : (i : MonAr appop) → Domˢ appop i (selfTuple i)
slotwise-self = boolΠ {M = λ i → Domˢ appop i (selfTuple i)}
                      (dom-total-L cell tt) (dom-total-R cell tt)

no-slotwise-joint : SlotwiseSuffices → ⊥
no-slotwise-joint sw = not-composable (sw appop selfTuple slotwise-self)

-- Surjectivity is no help either: `Imageˢ appop` IS the unit here
-- (`Located.img-total`, h = h ∗ emp), at the same `Fibered` that has no
-- point.  Both old grammars are ⊤ at every slot; the joint one fails.
slotwise-total : (i : MonAr appop) → ⊤G ⊢ Domˢ appop i
slotwise-total = boolΠ {M = λ i → ⊤G ⊢ Domˢ appop i} dom-total-L dom-total-R

-- THE BLINDNESS, as three separate theorems rather than one conjunctive
-- one -- a statement with an `×` in its conclusion is two statements
-- wearing a coat, and none of the three below needs the other two:
-- `Located.img-total` ⊤G ⊢ Imageˢ appop -- surjective `slotwise-total` ⊤G
-- ⊢ Domˢ appop i --...

-- 4.  THE TOTAL FRAGMENT COMPOSES EVERYTHING.  Same carrier, same
--     `parts`, one conjunct of one splitting deleted (`Base.cellFib`).

open JointDomain cellFib using ()
  renaming (Tuple to TupleC; Composable to ComposableC;
            point→composable to pointC→composable)

cell-composable : (o : MonOp) (m⃗ : TupleC o) → ComposableC o m⃗
cell-composable = pointC→composable cellPoint
