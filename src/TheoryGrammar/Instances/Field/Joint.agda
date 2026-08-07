{-
  THE FIELD, THROUGH THE JOINT LEMMA.

  `NoPoint.noFieldPoint` refutes every total point via the SLOTWISE
  `Domain.no-point`.  Here the same theorem is re-derived from
  `TheoryGrammar.Domain.no-point-joint`, which is also what the heap uses
  (`Heap/Joint`): the bad datum is the TUPLE `(0)` at the unary `invOp`,
  and the internal refutation is the existing calculus theorem
  `dom-inv⊢nonzero` with `joint→dom` as the only glue.

  A unary operation is the degenerate case -- tuple and slot coincide --
  which is exactly why the slotwise reading survived here and had to be
  refuted elsewhere.

  DEFINES `zeroTuple`, `not-composable-zero`, `noFieldPoint-joint`,
  `noFieldPoint-slotwise`, and the positive side `one-composable`/
  `two-composable`/`rng-composable`.

  PRIMITIVE: none.
-}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Instances.Field.Joint where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Domain
open import TheoryGrammar.Instances.Field.Base
open import TheoryGrammar.Instances.Field.Partial using (Nonzero; dom-inv⊢nonzero)
open import TheoryGrammar.Instances.Field.NoPoint using (fillsInv)

-- Brings in the JOINT reading, at `fldFib`:
--   `Tuple o`          DENOTES an argument tuple for o
--   `Composableᴳ o m⃗`  DENOTES "this result is the o-composite of m⃗"
--   `Composable o m⃗`   DENOTES "m⃗ composes SOMEWHERE" -- the domain of
--                      definition proper, a predicate on TUPLES
open JointDomain fldFib

-- ==================================================================
-- 1.  THE BAD TUPLE, and the internal refutation at it.
-- ==================================================================

zeroTuple : Tuple invOp
zeroTuple _ = f0

-- `Composableᴳ invOp zeroTuple` is `⊗ˢ invOp ⌈ 0 ⌉`: "this element is
-- the inverse of zero".  It is empty, and the content of that is
-- `dom-inv⊢nonzero`, already a theorem of the calculus.
not-composable-zero : Composableᴳ invOp zeroTuple ⊢ ⊥G
not-composable-zero m c =
  dom-inv⊢nonzero f0 (joint→dom invOp zeroTuple tt (m , c)) Eq.refl

-- ==================================================================
-- 2.  THEOREM.  `fldFib` has no total point -- through the JOINT lemma.
-- ==================================================================

noFieldPoint-joint : LaxPoint fldFib → ⊥
noFieldPoint-joint = no-point-internal invOp zeroTuple not-composable-zero

-- ... and the slotwise statement `NoPoint.noFieldPoint` used is now a
-- corollary of the same lemma, `Fills` supplying the tuple.
noFieldPoint-slotwise : LaxPoint fldFib → ⊥
noFieldPoint-slotwise = no-point-from-joint invOp tt fillsInv f0 dom-inv⊢nonzero

-- ==================================================================
-- 3.  THE PARTIALITY IS AT THAT TUPLE AND NOWHERE ELSE.
-- ==================================================================

-- every other unary tuple composes: `inv` is defined off zero
one-composable : Composable invOp (λ _ → f1)
one-composable = f1 , tt , λ _ → Eq.refl

two-composable : Composable invOp (λ _ → f2)
two-composable = f2 , tt , λ _ → Eq.refl

-- ... and every RING tuple composes, at every ring operation, because
-- the fragment has a point.  One line, generically.
open JointDomain rngFib using ()
  renaming (Tuple to TupleR; Composable to ComposableR;
            point→composable to pointR→composable)

rng-composable : (o : RngOp) (m⃗ : TupleR o) → ComposableR o m⃗
rng-composable = pointR→composable rngPoint
