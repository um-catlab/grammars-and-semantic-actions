{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- ENDPOINT 1. At `I = ⊥` -- nothing commutes -- the shuffle IS
   concatenation: `ITr ⊥I u v w ≅ Split3 u v w`, with `Split3` imported
   from `Instances.Strings.Base` unchanged. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Traces.Ordered (Letter : Type₀) where

open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.List
open import Cubical.Data.Empty using (⊥)

open import TheoryGrammar.Instances.Traces.Shuffle Letter public

import TheoryGrammar.Instances.Strings.Base
module Str = TheoryGrammar.Instances.Strings.Base Letter

⊥I : Indep
⊥I _ _ = ⊥

-- `Split3 [] v w` forces `w ≡ v`, so it absorbs a shared head; matching
-- `nil` is what makes the two indices one, with no transport.
bump : ∀ {x v w} → Str.Split3 [] v w → Str.Split3 [] (x ∷ v) (x ∷ w)
bump Str.nil = Str.nil

toSplit3 : ∀ {u v w} → ITr ⊥I u v w → Str.Split3 u v w
toSplit3 nil                       = Str.nil
toSplit3 (left s)                  = Str.cons (toSplit3 s)
toSplit3 (right {u = []}    tt s)  = bump (toSplit3 s)
toSplit3 (right {u = y ∷ u} (() , _) s)

fromSplit3 : ∀ {u v w} → Str.Split3 u v w → ITr ⊥I u v w
fromSplit3 Str.nil      = itrNil ⊥I _
fromSplit3 (Str.cons s) = left (fromSplit3 s)

-- the two round trips
nilSec : (v : Word) → toSplit3 (itrNil ⊥I v) ≡ Str.nil
nilSec []      = refl
nilSec (x ∷ v) = cong (bump {x = x}) (nilSec v)

ordSec : ∀ {u v w} (s : Str.Split3 u v w) → toSplit3 (fromSplit3 s) ≡ s
ordSec (Str.nil {v}) = nilSec v
ordSec (Str.cons s)  = cong Str.cons (ordSec s)

bumpFrom : ∀ {x v w} (p : Str.Split3 [] v w)
         → fromSplit3 (bump {x = x} p) ≡ right tt (fromSplit3 p)
bumpFrom Str.nil = refl

ordRet : ∀ {u v w} (t : ITr ⊥I u v w) → fromSplit3 (toSplit3 t) ≡ t
ordRet nil                      = refl
ordRet (left s)                 = cong left (ordRet s)
ordRet (right {u = []} tt s)    = bumpFrom (toSplit3 s) ∙ cong (right tt) (ordRet s)
ordRet (right {u = y ∷ u} (() , _) s)

-- THEOREM.  The ⊥ endpoint of the family is the free monoid's splitting.
ordered≅ : ∀ {u v w} → Iso (ITr ⊥I u v w) (Str.Split3 u v w)
ordered≅ .Iso.fun = toSplit3
ordered≅ .Iso.inv = fromSplit3
ordered≅ .Iso.sec = ordSec
ordered≅ .Iso.ret = ordRet

-- ... and hence at the level the `Fibered` actually uses: the `appop`
-- splittings of a word agree with `Strings`' on the nose.
orderedSplit≅ : (w : Word)
              → Iso (Σ[ u ∈ Word ] Σ[ v ∈ Word ] ITr ⊥I u v w)
                    (Str.MonSplit Str.appop w)
orderedSplit≅ w .Iso.fun (u , v , s) = u , v , toSplit3 s
orderedSplit≅ w .Iso.inv (u , v , s) = u , v , fromSplit3 s
orderedSplit≅ w .Iso.sec (u , v , s) = cong (λ z → u , v , z) (ordSec s)
orderedSplit≅ w .Iso.ret (u , v , s) = cong (λ z → u , v , z) (ordRet s)
