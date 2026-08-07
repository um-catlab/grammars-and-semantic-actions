{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{-
  RECOMPOSITION, freed from `SeqUnambig`.

  `SeqUnambig.split3App` proves exactly this, but that module takes a
  `decChar` parameter, so every client that merely wants "a splitting
  recomposes" has had to prove it again -- `FINDINGS` counts the copies.
  Nothing here needs decidable equality on the alphabet.
  PRIMITIVE: `recompose`, `isNilEq`, `appCancel` -- one recursion each.
  `ordDetermines` is derived from the first and the third.
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Strings.Recompose (Char : Type₀) where

open import Cubical.Data.List
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

import TheoryGrammar.Instances.Strings.Base as StB
module S = StB Char

-- PRIMITIVE.  A splitting recomposes.
recompose : {u v w : S.String} → S.Split3 u v w → w Eq.≡ (u ++ v)
recompose S.nil      = Eq.refl
recompose (S.cons p) = Eq.ap (λ z → _ ∷ z) (recompose p)

-- PRIMITIVE.  The nullary splitting is the empty string.
isNilEq : (w : S.String) → S.IsNil w → w Eq.≡ []
isNilEq [] _ = Eq.refl

private
  tl : S.String → S.String
  tl []       = []
  tl (_ ∷ xs) = xs

-- PRIMITIVE.  Left cancellation for append, via `ap tl` -- so no two
-- heads are ever unified and no decidable equality is needed.
appCancel : (u : S.String) {v v' : S.String}
          → (u ++ v) Eq.≡ (u ++ v') → v Eq.≡ v'
appCancel []      e = e
appCancel (c ∷ u) e = appCancel u (Eq.ap tl e)

-- an ordered splitting is determined by its LEFT block.  Not a
-- primitive: `recompose` twice and cancel.
ordDetermines : {u v v' w : S.String}
              → S.Split3 u v w → S.Split3 u v' w → v Eq.≡ v'
ordDetermines {u = u} p q =
  appCancel u (Eq.sym (recompose p) Eq.∙ recompose q)
