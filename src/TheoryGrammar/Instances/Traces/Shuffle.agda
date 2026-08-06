{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  PRIMITIVE: the I-indexed shuffle, the splitting relation of a trace
  monoid.  One data type, parameterised by an INDEPENDENCE RELATION.

  `left` takes the next letter from the left factor.  `right` may take a
  letter from the right factor ahead of the left factor only when that
  letter commutes past everything the left factor still owes -- and that
  side condition, `IndepAll`, is the entire content of the partial
  commutation.  Nothing is quotiented: the carrier stays `List Letter`.
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Traces.Shuffle (Letter : Type₀) where

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.List
open import Cubical.Data.Empty using (⊥)

Word : Type₀
Word = List Letter

Indep : Type₁
Indep = Letter → Letter → Type₀

-- "x commutes past every letter still owed by u".  A RECURSIVE
-- predicate, not an indexed family, so every case split below happens on
-- the word itself and no clause needs higher-dimensional unification.
IndepAll : Indep → Word → Letter → Type₀
IndepAll I []      x = Unit
IndepAll I (y ∷ u) x = I y x × IndepAll I u x

data ITr (I : Indep) : Word → Word → Word → Type₀ where
  nil   : ITr I [] [] []
  left  : ∀ {x u v w} → ITr I u v w → ITr I (x ∷ u) v (x ∷ w)
  right : ∀ {x u v w} → IndepAll I u x → ITr I u v w → ITr I u (x ∷ v) (x ∷ w)

IsNil : Word → Type₀
IsNil []      = Unit
IsNil (_ ∷ _) = ⊥

-- Concatenation is always a shuffle: once the left factor is exhausted
-- the side condition is vacuous, so no independence is ever consulted.
itrNil : (I : Indep) (v : Word) → ITr I [] v v
itrNil I []      = nil
itrNil I (x ∷ v) = right tt (itrNil I v)

itrApp : (I : Indep) (u v : Word) → ITr I u v (u ++ v)
itrApp I []      v = itrNil I v
itrApp I (x ∷ u) v = left (itrApp I u v)
