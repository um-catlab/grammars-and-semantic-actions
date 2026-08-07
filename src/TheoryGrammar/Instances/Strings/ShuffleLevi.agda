{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{-
  THE THIRD REFINEMENT LAW, and why it is in a different file.

  Over one carrier with both operations there are three interchange
  laws to ask about, and this is the table:

      ordered  x ordered      Strings/Refinement   NEEDS decChar
      ordered  x commutative  Shuffle.mixed        no decidability
      commutative x commutative  Bags/Refinement   no decidability

  Two of the three live in `Shuffle`, which takes no `decChar`.  The
  ordered-with-ordered case cannot, and that is not an artefact of the
  proof: Levi within ONE theory has to decide which off-diagonal cell
  vanishes, and deciding it is deciding letter equality.  The module
  boundary is the measurement.

  Both transports are field-by-field with no coercion.
  PRIMITIVE: none.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sum using (_⊎_)
import Cubical.Data.Equality as Eq
open import TheoryGrammar.Enumerable using (No)

module TheoryGrammar.Instances.Strings.ShuffleLevi
  (A : Type₀)
  (decA : (a b : A) → (a Eq.≡ b) ⊎ No (a Eq.≡ b))
  where

open import TheoryGrammar.Refinement

import TheoryGrammar.Instances.Strings.Shuffle as Sh
open Sh A public

import TheoryGrammar.Instances.Strings.Refinement as SRf
module SR = SRf A decA

module RS = Refine S.strFib

-- The ORDERED homogeneous law, transported from `Strings/Refinement`.
-- Same shape as `Shuffle.comRefinable`: `bothFib .Split (inl appop)`
-- reduces to `strFib .Split appop`, so only the record changes.
ordRefinable : R.Refinable ordOp ordOp
ordRefinable w p q = res
  where
  Z = SR.strRefinable w p q

  res : R.Refinement ordOp ordOp w p q
  res .R.cell     = Z .RS.cell
  res .R.rowSplit = Z .RS.rowSplit
  res .R.rowCell  = Z .RS.rowCell
  res .R.colSplit = Z .RS.colSplit
  res .R.colCell  = Z .RS.colCell
