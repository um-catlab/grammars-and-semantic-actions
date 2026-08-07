{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  ENDPOINT 2.  At `I = ⊤` -- everything commutes -- the shuffle IS
  interleaving: `ITr ⊤I u v w ≅ Ilv u v w`, with `Ilv` imported from
  `Instances.Bags.Base` unchanged.

  Here the two presentations are constructor-for-constructor; the only
  difference is that `right` carries a side condition, which at `I = ⊤`
  is a nested `Unit` and so contractible.  `allTtUnique` is that fact,
  and it is all the round trips need.
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Traces.Commutative (Letter : Type₀) where

open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.List

open import TheoryGrammar.Instances.Traces.Shuffle Letter public

import TheoryGrammar.Instances.Bags.Base
module Bg = TheoryGrammar.Instances.Bags.Base Letter

⊤I : Indep
⊤I _ _ = Unit

allTt : (u : Word) (x : Letter) → IndepAll ⊤I u x
allTt []      x = tt
allTt (y ∷ u) x = tt , allTt u x

-- the side condition is contractible at this endpoint
allTtUnique : (u : Word) (x : Letter) (pf : IndepAll ⊤I u x) → allTt u x ≡ pf
allTtUnique []      x pf = refl
allTtUnique (y ∷ u) x pf = ΣPathP (refl , allTtUnique u x (pf .snd))

toIlv : ∀ {u v w} → ITr ⊤I u v w → Bg.Ilv u v w
toIlv nil         = Bg.nil
toIlv (left s)    = Bg.left  (toIlv s)
toIlv (right _ s) = Bg.right (toIlv s)

fromIlv : ∀ {u v w} → Bg.Ilv u v w → ITr ⊤I u v w
fromIlv Bg.nil                        = nil
fromIlv (Bg.left s)                   = left (fromIlv s)
fromIlv (Bg.right {x = x} {u = u} s)  = right (allTt u x) (fromIlv s)

comSec : ∀ {u v w} (s : Bg.Ilv u v w) → toIlv (fromIlv s) ≡ s
comSec Bg.nil       = refl
comSec (Bg.left s)  = cong Bg.left  (comSec s)
comSec (Bg.right s) = cong Bg.right (comSec s)

comRet : ∀ {u v w} (t : ITr ⊤I u v w) → fromIlv (toIlv t) ≡ t
comRet nil                          = refl
comRet (left s)                     = cong left (comRet s)
comRet (right {x = x} {u = u} pf s) =
  cong₂ right (allTtUnique u x pf) (comRet s)

-- THEOREM.  The ⊤ endpoint of the family is the commutative monoid's
-- splitting.
commutative≅ : ∀ {u v w} → Iso (ITr ⊤I u v w) (Bg.Ilv u v w)
commutative≅ .Iso.fun = toIlv
commutative≅ .Iso.inv = fromIlv
commutative≅ .Iso.sec = comSec
commutative≅ .Iso.ret = comRet

commutativeSplit≅ : (w : Word)
                  → Iso (Σ[ u ∈ Word ] Σ[ v ∈ Word ] ITr ⊤I u v w)
                        (Bg.MonSplit Bg.appop w)
commutativeSplit≅ w .Iso.fun (u , v , s) = u , v , toIlv s
commutativeSplit≅ w .Iso.inv (u , v , s) = u , v , fromIlv s
commutativeSplit≅ w .Iso.sec (u , v , s) = cong (λ z → u , v , z) (comSec s)
commutativeSplit≅ w .Iso.ret (u , v , s) = cong (λ z → u , v , z) (comRet s)
