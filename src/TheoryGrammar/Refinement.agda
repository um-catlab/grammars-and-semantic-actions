{-
  REFINEMENT: Levi = Riesz = cross-split, at theory generality.

  Two splittings of one whole are refined by a MATRIX of pieces -- rows
  recompose to the parts of the first, columns to those of the second.
  Stated on `Split`/`parts` only, never on `op`, so it is available to a
  PARTIAL algebra, where cross-split normally carries a definedness side
  condition.

  SORTS CONSTRAIN IT.  `cell i j` arrives at `sortOf o' j` from its row
  and at `sortOf o i` from its column, so the operations have to be
  HOMOGENEOUS -- an explicit hypothesis (`HomOp`), not a convention.
  True of monoid, bag and heap composition; false of `lamOp`.

  MAIN: `HomOp`, `Refinement`, `Refinable`, `Diagonal`, `NonOverlap`,
  `Rigid`; `diag→sameParts` and `AtResult.rigid→partsPropAt`, the bridge
  to `Precision`.

  PRIMITIVE: `coeEqInj` (this file's one `Eq.refl` match).  `coeEq` is
  imported from `Precision`.
-}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Refinement where

open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Precision using (coeEq; module Prec)

private variable ℓS ℓ ℓ' ℓX ℓP ℓA : Level

-- PRIMITIVE.  Coercion along a strict equality of sorts is injective;
-- it is what turns a homogeneous statement back into a `σ`-indexed one.
coeEqInj : {X : Type ℓ} (P : X → Type ℓ') {x y : X} (e : x Eq.≡ y) {p q : P x}
         → coeEq P e p Eq.≡ coeEq P e q → p Eq.≡ q
coeEqInj P Eq.refl h = h

module Refine {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (Fib : Fibered σ ℓX ℓP) where

  open FibNotation Fib
  open Prec Fib using (PartsPropAt; PreciseP; PreciseI; MergeAt;
                       partsPropAt→preciseP; partsPropAt→preciseI;
                       partsProp→merge)

  -- 1.  HOMOGENEITY, as data.

  -- A `HomOp s` denotes an operation all of whose slots AND whose result
  -- live at the single sort `s` -- an operation on `Fib .carrier s` alone.
  record HomOp (s : S) : Type (ℓ-max ℓS (ℓ-max ℓ ℓ')) where
    field
      -- the operation itself
      op⋆  : σ .ops
      -- ... whose result sort is forced to be `s` ...
      resH : σ .resultSort op⋆ Eq.≡ s
      -- ... as is the sort of every one of its slots.  In `Eq` rather
      -- than `Path`, so `coeEq` along it still reduces.
      argH : (a : σ .arities op⋆) → σ .sortOf op⋆ a Eq.≡ s

  open HomOp public

  module _ {s : S} where

    Slots : HomOp s → Type ℓ'
    Slots o = σ .arities (o .op⋆)

    -- the whole, and the parts, read at the one sort `s`
    SplitH : (o : HomOp s) → Fib .carrier s → Type ℓP
    SplitH o m = Fib .Split (o .op⋆) (coeEq (Fib .carrier) (Eq.sym (o .resH)) m)

    partsH : (o : HomOp s) (m : Fib .carrier s) → SplitH o m
           → Slots o → Fib .carrier s
    partsH o m sp a =
      coeEq (Fib .carrier) (o .argH a)
            (Fib .parts (o .op⋆) (coeEq (Fib .carrier) (Eq.sym (o .resH)) m) sp a)

    -- a splitting is TRIVIAL at slot `i` when that slot already holds
    -- the whole.  No unit, and no nullary operation, is mentioned.
    Whole : (o : HomOp s) (m : Fib .carrier s) → SplitH o m → Slots o → Type ℓX
    Whole o m sp i = partsH o m sp i Eq.≡ m

    -- 2. THE MATRIX.

    -- A `Refinement o o' m p q` denotes a common refinement of the two
    -- splittings `p`, `q` of `m`: a matrix of pieces of `m` that
    -- recomposes to `p` when read by rows and to `q` when read by columns.
    record Refinement (o o' : HomOp s) (m : Fib .carrier s)
                      (p : SplitH o m) (q : SplitH o' m)
      : Type (ℓ-max ℓ' (ℓ-max ℓX ℓP)) where
      field
        -- the (i,j) piece: the part of `m` that slot `i` of `p` and slot
        -- `j` of `q` have in common
        cell     : Slots o → Slots o' → Fib .carrier s
        -- row `i` splits the i-th part of `p` under `o'` ...
        rowSplit : (i : Slots o) → SplitH o' (partsH o m p i)
        -- ... into exactly the cells of that row
        rowCell  : (i : Slots o) (j : Slots o')
                 → partsH o' (partsH o m p i) (rowSplit i) j Eq.≡ cell i j
        -- column `j` splits the j-th part of `q` under `o` ...
        colSplit : (j : Slots o') → SplitH o (partsH o' m q j)
        -- ... into exactly the cells of that column
        colCell  : (j : Slots o') (i : Slots o)
                 → partsH o (partsH o' m q j) (colSplit j) i Eq.≡ cell i j

    open Refinement public

    Refinable : (o o' : HomOp s) → Type (ℓ-max ℓ' (ℓ-max ℓX ℓP))
    Refinable o o' = (m : Fib .carrier s) (p : SplitH o m) (q : SplitH o' m)
                   → Refinement o o' m p q

    -- Transposition: the axiom is symmetric, and the proof is the
    -- matrix read the other way round.  Nothing is recomputed.
    transpose : {o o' : HomOp s} {m : Fib .carrier s}
                {p : SplitH o m} {q : SplitH o' m}
              → Refinement o o' m p q → Refinement o' o m q p
    transpose R .cell j i    = R .cell i j
    transpose R .rowSplit j  = R .colSplit j
    transpose R .rowCell j i = R .colCell j i
    transpose R .colSplit i  = R .rowSplit i
    transpose R .colCell i j = R .rowCell i j

    refinableSym : {o o' : HomOp s} → Refinable o o' → Refinable o' o
    refinableSym r m q p = transpose (r m p q)

    -- 3. DIAGONALITY, and `sameParts` GENERICALLY.

    -- every row is concentrated on its own diagonal cell ...
    DiagonalRows : {o : HomOp s} {m : Fib .carrier s} {p q : SplitH o m}
                 → Refinement o o m p q → Type (ℓ-max ℓ' ℓX)
    DiagonalRows {o = o} {m} {p} R =
      (i : Slots o) → Whole o (partsH o m p i) (R .rowSplit i) i

    -- ... and so is every column
    DiagonalCols : {o : HomOp s} {m : Fib .carrier s} {p q : SplitH o m}
                 → Refinement o o m p q → Type (ℓ-max ℓ' ℓX)
    DiagonalCols {o = o} {m} {q = q} R =
      (i : Slots o) → Whole o (partsH o m q i) (R .colSplit i) i

    -- Both at once.  Kept as one name because `NonOverlap` and `Rigid`
    -- both produce the pair and `diag→sameParts` consumes it; the two
    -- halves are named above so that a caller can say which it means.
    Diagonal : {o : HomOp s} {m : Fib .carrier s} {p q : SplitH o m}
             → Refinement o o m p q → Type (ℓ-max ℓ' ℓX)
    Diagonal R = DiagonalRows R × DiagonalCols R

    -- diagonality transposes with the matrix: rows become columns
    diagTranspose : {o : HomOp s} {m : Fib .carrier s} {p q : SplitH o m}
                    (R : Refinement o o m p q) → Diagonal R → Diagonal (transpose R)
    diagTranspose R (rw , cw) = cw , rw

    diag→sameParts : {o : HomOp s} {m : Fib .carrier s} {p q : SplitH o m}
                     (R : Refinement o o m p q) → Diagonal R
                   → (i : Slots o) → partsH o m p i Eq.≡ partsH o m q i
    diag→sameParts R (rw , cw) i =
      Eq.sym (rw i) Eq.∙ R .rowCell i i Eq.∙ Eq.sym (R .colCell i i) Eq.∙ cw i

    -- GRAMMAR-RELATIVE.  `NonOverlap` is `SeqUnambig`'s `_⊛_` at theory
    -- generality: not "the substrate has one splitting" but "the
    -- splittings compatible with A do not genuinely overlap".
    module _ (o : HomOp s) (ref : Refinable o o)
             (A : Slots o → TheoryTy ℓA s) where

      NonOverlap : Type (ℓ-max ℓ' (ℓ-max ℓX (ℓ-max ℓP ℓA)))
      NonOverlap = (m : Fib .carrier s) (p q : SplitH o m)
                 → ((i : Slots o) → A i (partsH o m p i))
                 → ((i : Slots o) → A i (partsH o m q i))
                 → Diagonal (ref m p q)

      nonOverlap→sameParts
        : NonOverlap
        → (m : Fib .carrier s) (p q : SplitH o m)
        → ((i : Slots o) → A i (partsH o m p i))
        → ((i : Slots o) → A i (partsH o m q i))
        → (i : Slots o) → partsH o m p i Eq.≡ partsH o m q i
      nonOverlap→sameParts no m p q x y =
        diag→sameParts (ref m p q) (no m p q x y)

    -- The grammar-free extreme: EVERY refinement is diagonal.
    Rigid : {o : HomOp s} → Refinable o o → Type (ℓ-max ℓ' (ℓ-max ℓX ℓP))
    Rigid {o = o} ref = (m : Fib .carrier s) (p q : SplitH o m)
                      → Diagonal (ref m p q)

    rigid→sameParts : {o : HomOp s} (ref : Refinable o o) → Rigid ref
                    → (m : Fib .carrier s) (p q : SplitH o m) (i : Slots o)
                    → partsH o m p i Eq.≡ partsH o m q i
    rigid→sameParts ref rg m p q i = diag→sameParts (ref m p q) (rg m p q) i

  -- 4. ... AND PRECISION.

  module AtResult (ho : σ .ops)
                  (argH⋆ : (a : σ .arities ho) → σ .sortOf ho a Eq.≡ σ .resultSort ho)
                  where

    homOp : HomOp (σ .resultSort ho)
    homOp .op⋆  = ho
    homOp .resH = Eq.refl
    homOp .argH = argH⋆

    rigid→partsPropAt : (ref : Refinable homOp homOp) → Rigid ref → PartsPropAt ho
    rigid→partsPropAt ref rg m p q a =
      coeEqInj (Fib .carrier) (argH⋆ a) (rigid→sameParts ref rg m p q a)

    rigid→preciseP : (ref : Refinable homOp homOp) → Rigid ref
                   → (i : σ .arities ho) (A : TheoryTy ℓA (σ .sortOf ho i))
                   → PreciseP ho i A
    rigid→preciseP ref rg i A =
      partsPropAt→preciseP ho i A (rigid→partsPropAt ref rg)

    rigid→preciseI : (ref : Refinable homOp homOp) → Rigid ref
                   → (ℓB : Level) (i : σ .arities ho)
                     (A : TheoryTy ℓA (σ .sortOf ho i))
                   → PreciseI ℓB ho i A
    rigid→preciseI ref rg ℓB i A =
      partsPropAt→preciseI ℓB ho i A (rigid→partsPropAt ref rg)

    rigid→merge : (ref : Refinable homOp homOp) → Rigid ref
                → (ℓB : Level) → MergeAt ℓB ho
    rigid→merge ref rg ℓB = partsProp→merge ℓB ho (rigid→partsPropAt ref rg)
