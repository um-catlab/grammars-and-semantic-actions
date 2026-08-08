{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- THE TABLE'S SPINE, AS A TREE. `Enumerable.AllYes'` tabulates over a
   `List`, so an entry at offset `d` is addressed by `there^d here` and
   read by walking that address: `O(d)` to BUILD the address and `O(d)` to
   CONSUME it, both real (measured, see `DPTests`). -}
module TheoryGrammar.DP.Seq where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.List

private variable ℓI ℓA ℓB : Level

-- THE SPINE.  `List` with `++` as a constructor rather than a
-- function -- so the SHAPE of the concatenation survives, and it is
-- the shape that an address is a path through.

infixr 5 _⋈_

data Seq (I : Type ℓI) : Type ℓI where
  εQ   : Seq I
  oneQ : I → Seq I
  _⋈_  : Seq I → Seq I → Seq I

-- THE ADDRESS.  A path, not an offset.  `_∈L_`'s `there` advances one
-- CELL; `lQ`/`rQ` advance one LEVEL, so a balanced spine gives
-- addresses of length `O(log n)`.

data _∈Q_ {I : Type ℓI} (i : I) : Seq I → Type ℓI where
  hereQ : i ∈Q oneQ i
  lQ    : {s t : Seq I} → i ∈Q s → i ∈Q (s ⋈ t)
  rQ    : {s t : Seq I} → i ∈Q t → i ∈Q (s ⋈ t)

-- THE TABLE. Still a nested `×` -- DATA, forced once and projected many
-- times -- only reassociated to follow the spine.

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

-- BALANCE IS NOT ENFORCED, AND SHOULD NOT BE. `Seq` says nothing about the
-- shape of `_⋈_`; a right-nested comb is a list again, with a list's
-- costs.

flatten : {I : Type ℓI} → Seq I → List I
flatten εQ       = []
flatten (oneQ i) = i ∷ []
flatten (s ⋈ t)  = flatten s ++ flatten t
