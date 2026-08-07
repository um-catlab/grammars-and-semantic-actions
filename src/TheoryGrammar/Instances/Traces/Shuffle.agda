{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  PRIMITIVE: the I-indexed shuffle, the splitting relation of a trace
  monoid.  One data type, parameterised by MAZURKIEWICZ INDEPENDENCE --
  a relation `Ind` on the alphabet, intended symmetric and irreflexive,
  though nothing here needs either.

  `left` takes the next letter from the left factor.  `right` may take a
  letter from the right factor ahead of the left factor only when that
  letter commutes past everything the left factor still owes -- and that
  side condition, `IndepAll`, is the entire content of the partial
  commutation.  Nothing is quotiented: the carrier stays `List Letter`.

  DEFINES `Word`, `Indep`, `IndepAll`, `ITr`, `IsNil`, and the two
  concatenation shuffles `itrNil`/`itrApp`.
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Traces.Shuffle (Letter : Type₀) where

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.List
open import Cubical.Data.Empty using (⊥)

-- `Word` DENOTES an element of the trace monoid, presented by one of
-- its representatives.  NOT quotiented: the equation lives in `ITr`.
Word : Type₀
Word = List Letter

-- `Indep` DENOTES a Mazurkiewicz independence alphabet: `Ind x y` says
-- `xy = yx` is imposed.  Intended symmetric and irreflexive, though
-- nothing in this file needs either.
Indep : Type₁
Indep = Letter → Letter → Type₀

-- "x commutes past every letter still owed by u".  A RECURSIVE
-- predicate, not an indexed family, so every case split below happens on
-- the word itself and no clause needs higher-dimensional unification.
IndepAll : Indep → Word → Letter → Type₀
IndepAll Ind []      x = Unit
IndepAll Ind (y ∷ u) x = Ind y x × IndepAll Ind u x

-- `ITr Ind u v w` DENOTES "w is a product of u and v in the trace
-- monoid" -- concretely, a two-colouring of w's positions reading off u
-- and v in order, every out-of-order pair of which is independent.  A
-- VALUE of it is the interleaving itself, so the witness is the datum
-- and no side condition is ever re-checked.
data ITr (Ind : Indep) : Word → Word → Word → Type₀ where
  nil   : ITr Ind [] [] []
  left  : ∀ {x u v w} → ITr Ind u v w → ITr Ind (x ∷ u) v (x ∷ w)
  right : ∀ {x u v w} → IndepAll Ind u x → ITr Ind u v w
        → ITr Ind u (x ∷ v) (x ∷ w)

-- `IsNil w` DENOTES "w is the empty trace", and it is what
-- `Split nilop` reads.  Recursive, so it computes at a closed word.
IsNil : Word → Type₀
IsNil []      = Unit
IsNil (_ ∷ _) = ⊥

-- Concatenation is always a shuffle: once the left factor is exhausted
-- the side condition is vacuous, so no independence is ever consulted.
itrNil : (Ind : Indep) (v : Word) → ITr Ind [] v v
itrNil Ind []      = nil
itrNil Ind (x ∷ v) = right tt (itrNil Ind v)

itrApp : (Ind : Indep) (u v : Word) → ITr Ind u v (u ++ v)
itrApp Ind []      v = itrNil Ind v
itrApp Ind (x ∷ u) v = left (itrApp Ind u v)
