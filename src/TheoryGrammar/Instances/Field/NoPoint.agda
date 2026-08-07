{-
  NO TOTAL POINT FOR A FIELD -- and one for its ring fragment.

  The money result.  `Fibered` was split from `LaxPoint` in order to
  admit partial algebras; this is the proof that the admission is real,
  i.e. that some `Fibered` in the library has NO `LaxPoint` at all,
  while the same promodel restricted to a sub-signature has one.

  The refutation is entirely internal down to the last step: it is the
  SLOTWISE `Domain.no-point` applied to `dom-inv⊢nonzero`, the calculus
  theorem "being in the domain of inv refutes being zero".  Slotwise
  suffices only because `invOp` is unary, so tuple and slot coincide;
  `Field/Joint` redoes it through the joint lemma that survives at a
  heap, and gets the same statement back.

  Also here: `⊗ˢ o ⊤` is the IMAGE, not the domain.  `zeroOp` is TOTAL
  and its image is still a proper subgrammar (`no-img-zero`), so
  "`⊗ˢ o ⊤ = ⊤`" is strictly stronger than totality; the exact
  condition is `Covering`.

  DEFINES `fillsInv`, `noFieldPoint` (+ `noFieldPoint-explicit`),
  `ringFragmentPoint`, the ring-side totality `dom-add-total`/
  `dom-mul-total` and surjectivity `img-add`/`img-mul`/`coverAdd`/
  `coverMul`/`cover-add-again`, and the five refutations `no-dom-inv`,
  `no-img-inv`, `no-img-zero`, `no-img-one`, `no-cover-zero`.

  READING THE `no-` NAMES.  Throughout this directory `no-X-o` is
  `(⊤G ⊢ X o) → ⊥` -- "the grammar `X o` is NOT the unit" -- and NOT
  "`X o` is empty".  `no-img-zero` is the sharp case: `ImgR zeroR` is
  inhabited (at f0), just not everywhere.  The prefix is the tree-wide
  spelling for a refutation (`no-point`, `no-slotwise-L/R`,
  `noHeapPoint`), which is why it is kept rather than respelled here.
-}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Instances.Field.NoPoint where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Domain
open import TheoryGrammar.Instances.Field.Base
open import TheoryGrammar.Instances.Field.Partial

-- ==================================================================
-- 1.  THE INVERSE SLOT IS FILLABLE (it is the only slot), so a total
--     point would have to make its domain grammar ⊤.
-- ==================================================================

-- `Fills o i` DENOTES a way to complete a tuple around slot i.  At the
-- unary `invOp` "the other slots" is empty, so padding is the identity.
fillsInv : Fills invOp tt
fillsInv .pad x _ = x
fillsInv .pad-i x = refl

-- ==================================================================
-- 2.  THEOREM.  `fldFib` HAS NO TOTAL POINT.
--
-- One line, and every ingredient is a theorem of the calculus:
-- `no-point` is generic, `dom-inv⊢nonzero` is `Domˢ invOp ⊢ ¬G ⌈ f0 ⌉`.
-- ==================================================================

noFieldPoint : LaxPoint fldFib → ⊥
noFieldPoint = no-point invOp tt fillsInv f0 dom-inv⊢nonzero

-- Unpacked, for the record: the contradiction is that a point would
-- have to invert zero, and the result would have to be zero's inverse
-- AND nonzero.
noFieldPoint-explicit : LaxPoint fldFib → ⊥
noFieldPoint-explicit P =
  nz-not-f0 (inv y sp) (inv-nz y sp)
            (Eq.pathToEq (funExt⁻ (P .parts-split invOp (λ _ → f0)) tt))
  where y  = P .op invOp (λ _ → f0)
        sp = P .split invOp (λ _ → f0)

-- ==================================================================
-- 3.  THE FRAGMENT DOES HAVE ONE.  Same carrier, same splittings, same
--     `parts` -- only `invOp` removed.  So the obstruction is located
--     exactly at the partial operation and nowhere else.
-- ==================================================================

ringFragmentPoint : LaxPoint rngFib
ringFragmentPoint = rngPoint

-- ==================================================================
-- 4.  DOMAIN OF DEFINITION vs. `⊗ˢ o ⊤`.
-- ==================================================================

open DomainOf rngFib
  using () renaming (Imgˢ to ImgR; Domˢ to DomR; Fills to FillsR;
                     pad to padR; pad-i to padR-i;
                     Covering to CoveringR;
                     point→dom to pointR→dom;
                     covering→img to coveringR→img;
                     img→covering to imgR→coveringR)

-- THE DOMAIN, first.  Every slot of every RING operation is total: its
-- domain grammar is ⊤, and that is `point→dom` at the fragment's point.
fillsAddL : FillsR addR lhs
fillsAddL .padR x lhs = x
fillsAddL .padR x rhs = f0
fillsAddL .padR-i x = refl

fillsMulR : FillsR mulR rhs
fillsMulR .padR x lhs = f1
fillsMulR .padR x rhs = x
fillsMulR .padR-i x = refl

dom-add-total : ⊤G ⊢ DomR addR lhs
dom-add-total = pointR→dom rngPoint addR lhs fillsAddL

dom-mul-total : ⊤G ⊢ DomR mulR rhs
dom-mul-total = pointR→dom rngPoint mulR rhs fillsMulR

-- ... and `invOp`'s is not, at f0.  Same shape, opposite verdict: this
-- is `noFieldPoint` with the point erased, i.e. the statement that
-- FAILS is exactly the one `point→dom` would supply.
no-dom-inv : (⊤G ⊢ Domˢ invOp tt) → ⊥
no-dom-inv f = E.rec* (dom-inv⊢nonzero f0 (f f0 tt) Eq.refl)

-- `⊗ˢ invOp ⊤` is NOT the unit: it is empty at zero, which is the same
-- fact as `img-inv⊢nonzero`, read at a point.
no-img-inv : (⊤G ⊢ Imgˢ invOp) → ⊥
no-img-inv f = f f0 tt .fst

-- The two operations that ARE covering, via the generic theorem:
-- m = 0 + m and m = 1 · m.
coverAdd : CoveringR rngPoint addR
coverAdd m = (λ { lhs → f0 ; rhs → m }) , Eq.refl

coverMul : CoveringR rngPoint mulR
coverMul m = (λ { lhs → f1 ; rhs → m }) , Eq.refl

img-add : ⊤G ⊢ ImgR addR
img-add = coveringR→img rngPoint addR coverAdd

img-mul : ⊤G ⊢ ImgR mulR
img-mul = coveringR→img rngPoint mulR coverMul

-- ... and the two that are NOT, ALTHOUGH THEY ARE TOTAL.  This is the
-- caveat: `⊗ˢ o ⊤ = ⊤` says the operation is SURJECTIVE, not that it is
-- defined everywhere.  A constant is total and never surjective.
no-img-zero : (⊤G ⊢ ImgR zeroR) → ⊥
no-img-zero f = f f1 tt .fst

no-img-one : (⊤G ⊢ ImgR oneR) → ⊥
no-img-one f = f f0 tt .fst

-- and, through the generic equivalence, the corresponding failure of
-- `Covering` -- so the two sides really are the same condition here
no-cover-zero : CoveringR rngPoint zeroR → ⊥
no-cover-zero cov = no-img-zero (coveringR→img rngPoint zeroR cov)

cover-add-again : CoveringR rngPoint addR
cover-add-again = imgR→coveringR rngPoint rngHonest addR img-add
