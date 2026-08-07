{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE TABLE'S SPINE, AS A TREE.

  `Enumerable.AllYes'` tabulates over a `List`, so an entry at offset `d`
  is addressed by `there^d here` and read by walking that address: `O(d)`
  to BUILD the address and `O(d)` to CONSUME it, both real (measured, see
  `DPTests`).  Neither half can be repaired alone, and both are forced by
  the SPINE: a list has one shape, and the only path to its `d`th cell
  has length `d`.

  So change the spine.  A `Seq` is a list with its associativity left
  UNQUOTIENTED -- a binary tree of concatenations --

      εQ            the empty schedule
      oneQ i        one subproblem
      s ⋈ t         `s` then `t`

  and a `Tab` over it is the same nested `×` reassociated to match.  An
  address is a PATH (`lQ`/`rQ`), so a balanced `Seq` addresses `n` cells
  with paths of length `O(log n)`, and again both halves move together:
  the path is `O(log n)` to build and `O(log n)` to walk.

  WHY NOT A LIST WITH A COMPUTED INDEX (skew-binary, Braun, ...).  Those
  address by a NUMBER, and a number has to be compared against subtree
  sizes on the way down.  At a unary `ℕ` each comparison is itself `O(n)`,
  so the log is lost at the first step; at a binary numeral it is
  recovered but the entry's TYPE `A i` then has to be recovered from the
  numeral, which is a `subst` -- and `CLAUDE.md`'s third trap says a
  derivation that introduces `subst` is the wrong derivation.  A path is
  a dependent address: `lookupQ (p : i ∈Q s)` returns `A i` on the nose,
  with no coercion anywhere.  That is the whole reason this file is a
  tree of concatenations rather than a random-access list.

  NOTHING HERE IS ABOUT DP.  This is `Enumerable`'s `AllYes'` /
  `lookupYes'` / `_∈L_` with the spine reassociated, and it is kept in
  its own file for that reason.
-}
module TheoryGrammar.DP.Seq where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.List

private variable ℓI ℓA ℓB : Level

-- ==================================================================
-- THE SPINE.  `List` with `++` as a constructor rather than a
-- function -- so the SHAPE of the concatenation survives, and it is
-- the shape that an address is a path through.
-- ==================================================================

infixr 5 _⋈_

data Seq (I : Type ℓI) : Type ℓI where
  εQ   : Seq I
  oneQ : I → Seq I
  _⋈_  : Seq I → Seq I → Seq I

-- ==================================================================
-- THE ADDRESS.  A path, not an offset.  `_∈L_`'s `there` advances one
-- CELL; `lQ`/`rQ` advance one LEVEL, so a balanced spine gives
-- addresses of length `O(log n)`.
-- ==================================================================

data _∈Q_ {I : Type ℓI} (i : I) : Seq I → Type ℓI where
  hereQ : i ∈Q oneQ i
  lQ    : {s t : Seq I} → i ∈Q s → i ∈Q (s ⋈ t)
  rQ    : {s t : Seq I} → i ∈Q t → i ∈Q (s ⋈ t)

-- ==================================================================
-- THE TABLE.  Still a nested `×` -- DATA, forced once and projected
-- many times -- only reassociated to follow the spine.  Note the
-- definitional equation that makes the whole of `DP`'s `build` work:
--
--     Tab A (s ⋈ t) = Tab A s × Tab A t
--
-- so EXTENDING a table by a batch is PAIRING, at cost `O(1)` and with
-- no re-indexing of anything already in it.  With a list spine the
-- corresponding move is `++`, whose addresses need `∈++ʳ` -- a walk.
-- ==================================================================

Tab : {I : Type ℓI} (A : I → Type ℓA) → Seq I → Type ℓA
Tab A εQ       = Unit*
Tab A (oneQ i) = A i
Tab A (s ⋈ t)  = Tab A s × Tab A t

-- Reading the table.  Recursion is on the PATH, so the cost is the
-- path's length and nothing else; and because the path is dependent
-- the result is `A i` with no coercion.
lookupQ : {I : Type ℓI} {A : I → Type ℓA} {s : Seq I} {i : I}
        → i ∈Q s → Tab A s → A i
lookupQ hereQ  a       = a
lookupQ (lQ p) (x , _) = lookupQ p x
lookupQ (rQ p) (_ , y) = lookupQ p y

-- ... and the pointwise map, for what little needs it
mapQ : {I : Type ℓI} {A : I → Type ℓA} {B : I → Type ℓB}
     → ((i : I) → A i → B i) → (s : Seq I) → Tab A s → Tab B s
mapQ f εQ       tt*     = tt*
mapQ f (oneQ i) a       = f i a
mapQ f (s ⋈ t)  (x , y) = mapQ f s x , mapQ f t y

-- ==================================================================
-- BALANCE IS NOT ENFORCED, AND SHOULD NOT BE.
--
-- `Seq` says nothing about the shape of `_⋈_`; a right-nested comb is
-- a list again, with a list's costs.  That is deliberate.  A schedule's
-- LAYOUT is the instance's business -- an instance that knows its chart
-- is a triangle of levels can lay it out better than any generic
-- splitter, and it also knows how to ADDRESS what it laid out, which a
-- generic splitter cannot hand back for free.  `DPTests`' `blk`/`chain`
-- is the worked example: a perfect block, and covering proofs threaded
-- down the split rather than searched for.
--
-- What is generic is only the flattening, for saying in a spec that a
-- `Seq` holds what a list held.
-- ==================================================================

flatten : {I : Type ℓI} → Seq I → List I
flatten εQ       = []
flatten (oneQ i) = i ∷ []
flatten (s ⋈ t)  = flatten s ++ flatten t
