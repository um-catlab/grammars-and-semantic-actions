{-
  WHERE THE OBSTRUCTION IS -- and where it is NOT.

  `Connectives.noHeapPoint` refutes every total point.  Two
  localisations, each sharper than `Field/NoPoint`'s ring fragment:

    empPoint           restrict to `nilop`: the UNIT of the separation
                       algebra is perfectly total.
    cellFragmentPoint  same carrier, same `parts`, same `Ilv` -- delete
                       only the `u # v` CONJUNCT of `HeapSplit`
                       (`Base.cellFib`) -- and the point reappears.  One
                       conjunct of one splitting.

  AND WHERE IT IS NOT.  The SLOTWISE grammars of `Field/Domain` are
  blind to it: `Domˢ appop` is `⊤G` at both slots (h = h ∗ emp and
  h = emp ∗ h) and `Imgˢ appop` is `⊤G` too, so `Covering` holds.  Every
  slot totally defined, the operation surjective, and still no point;
  `no-slotwise-L/R` prove no refutation of `Domain.no-point`'s shape
  exists here at any heap.  For a partial COMMUTATIVE monoid the
  partiality is JOINT, and `Heap/Joint` carries the form that works --
  a tensor of REPRESENTABLES rather than of `⊤`.

  DEFINES `cellFragmentPoint`; the restricted fragment `EmpOp`/`ιE`/
  `empSig`/`empFib`/`empPoint`; the three positive facts `img-total`,
  `dom-total-L`, `dom-total-R`; and the three refutations of the
  slotwise shape `no-slotwise-L`, `no-slotwise-R`, `no-img-obstruction`.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Heap.Located where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Restrict using (restrictSig; restrictFib)
open import TheoryGrammar.Domain using (module DomainOf)

open import TheoryGrammar.Instances.Heap.Connectives public

-- ==================================================================
-- 1.  DELETE THE DISJOINTNESS CONJUNCT AND THE POINT APPEARS.
--
-- `cellFib` is `heapFib` with `u # v` dropped from `Split appop`; the
-- carrier, `parts` and `Ilv` are literally the same.  `cellPoint` is
-- its lax point (list concatenation), so the whole of `noHeapPoint`
-- lives in that one conjunct.
-- ==================================================================

cellFragmentPoint : LaxPoint cellFib
cellFragmentPoint = cellPoint

-- ==================================================================
-- 2.  RESTRICT TO `nilop` AND THE POINT APPEARS.  So the unit is
--     total; only the join fails.
-- ==================================================================

data EmpOp : Type₀ where
  emponly : EmpOp

ιE : EmpOp → MonOp
ιE emponly = nilop

empSig : SortedSig Unit ℓ-zero ℓ-zero
empSig = restrictSig monoidSig ιE

empFib : Fibered empSig ℓ-zero ℓ-zero
empFib = restrictFib monoidSig ιE heapFib

empPoint : LaxPoint empFib
empPoint .op emponly _          = []
empPoint .split emponly _       = tt
empPoint .parts-split emponly _ = funExt λ ()

-- ==================================================================
-- 3.  THE SLOTWISE GRAMMARS ARE BLIND.
-- ==================================================================

-- `Imgˢ o`   DENOTES "this heap IS an o-composite"          (`⊗ˢ o ⊤`)
-- `Domˢ o i` DENOTES "this heap OCCURS in slot i of one"
-- Both are indexed by ONE slot, which is precisely why they are blind
-- to a failure that lives in the PAIR.
open DomainOf heapFib using (Imgˢ; Domˢ; ¬G_)

-- every heap IS a composite: h = h ∗ emp.  So `Covering` holds and
-- `⊗ˢ appop ⊤` is the unit -- the condition `Field/Domain` shows is the
-- right reading of `⊗ˢ o ⊤`.
img-total : ⊤G ⊢ Imgˢ appop
img-total h _ = (h , [] , ilv-nilR h , #-nil h) , λ _ → tt

-- every heap occurs in the left slot of a splitting ...
dom-total-L : ⊤G ⊢ Domˢ appop true
dom-total-L u _ = u , (u , [] , ilv-nilR u , #-nil u) , Eq.refl

-- ... and in the right slot of one
dom-total-R : ⊤G ⊢ Domˢ appop false
dom-total-R v _ = v , ([] , v , ilv-nilL v , tt) , Eq.refl

-- THEOREM.  No refutation of `Domain.no-point`'s shape exists at either
-- slot, at any heap.  This is why the joint form was needed.
no-slotwise-L : (x : Heap) → (Domˢ appop true ⊢ ¬G ⌈ x ⌉) → ⊥
no-slotwise-L x k = E.rec* (k x (dom-total-L x tt) Eq.refl)

no-slotwise-R : (x : Heap) → (Domˢ appop false ⊢ ¬G ⌈ x ⌉) → ⊥
no-slotwise-R x k = E.rec* (k x (dom-total-R x tt) Eq.refl)

-- ... and none of the image's shape either
no-img-obstruction : ((⊤G ⊢ Imgˢ appop) → ⊥) → ⊥
no-img-obstruction k = k img-total
