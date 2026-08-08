{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- DEDUPLICATION, AND WHY A SCHEDULE NEEDS IT. `DP` says a recurrence is
   tabulated by a `Chain`: an enumeration of subproblems in which every
   element's dependencies appear later. -}
module TheoryGrammar.DP.Nub where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List
open import Cubical.Relation.Nullary using (Dec; yes; no; ¬_; Discrete)

open import TheoryGrammar.Enumerable

private variable ℓ : Level

-- membership is decidable when equality is
mem? : {X : Type ℓ} → Discrete X → (x : X) (xs : List X) → Dec (x ∈L xs)
mem? dx x []       = no λ ()
mem? dx x (y ∷ ys) = here? (dx x y)
  where
    tail? : Dec (x ∈L ys) → ¬ (x ≡ y) → Dec (x ∈L (y ∷ ys))
    tail? (yes p) k = yes (there p)
    tail? (no  r) k = no λ { here      → k refl
                           ; (there p) → r p }

    here? : Dec (x ≡ y) → Dec (x ∈L (y ∷ ys))
    here? (yes e) = yes (subst (_∈L (y ∷ ys)) (sym e) here)
    here? (no  k) = tail? (mem? dx x ys) k

-- `nub`, KEEPING THE LAST OCCURRENCE. Dropping the EARLIER copy matters: a
-- `Chain` needs dependencies to appear later in the list, and a world's
-- dependencies are enumerated after it, so the surviving copy must be the
-- deepest one.

-- the two branches of the `cons` case, named so lemmas can case on
-- them.  Taking the tail as a PLAIN list (rather than `nub dx ys`)
-- keeps this out of a mutual block with `nub`.
nubCons : {X : Type ℓ} (y : X) (r : List X) → Dec (y ∈L r) → List X
nubCons y r (yes _) = r                 -- already present later: drop this one
nubCons y r (no  _) = y ∷ r

nub : {X : Type ℓ} → Discrete X → List X → List X
nub dx []       = []
nub dx (x ∷ xs) = nubCons x (nub dx xs) (mem? dx x (nub dx xs))

-- ... AND IT LOSES NOTHING.  The one fact a covering proof cites, and
-- it is two lemmas about `nubCons` plus one line of recursion.
∈nubCons-here : {X : Type ℓ} (y : X) (r : List X) (d : Dec (y ∈L r))
              → y ∈L nubCons y r d
∈nubCons-here y r (yes p) = p
∈nubCons-here y r (no  _) = here

∈nubCons-there : {X : Type ℓ} {x y : X} {r : List X} (d : Dec (y ∈L r))
               → x ∈L r → x ∈L nubCons y r d
∈nubCons-there (yes _) q = q
∈nubCons-there (no  _) q = there q

∈nub : {X : Type ℓ} (dx : Discrete X) {x : X} {xs : List X}
     → x ∈L xs → x ∈L nub dx xs
∈nub dx {xs = y ∷ ys} here      =
  ∈nubCons-here y (nub dx ys) (mem? dx y (nub dx ys))
∈nub dx {xs = y ∷ ys} (there q) =
  ∈nubCons-there (mem? dx y (nub dx ys)) (∈nub dx q)
