{- `refl` TESTS ON SMALL CONCRETE HEAPS. Every expected value is a `Heap`,
   a `Val` or a `Loc`, so a wrong answer is a type error rather than a
   silently-true equation. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Heap.Tests where

open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit
open import Cubical.Data.List using (List; []; _∷_)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered

-- `Suite` gives `passes` / `_at_`; its `_↦_` is renamed because `↦` is
-- already the POINTS-TO of this instance (`Heap/Emp`), and that notation
-- wins.  `_≔_` reads "expected to be".
open import TheoryGrammar.SemanticAction
  using (Case; passes; _at_) renaming (_↦_ to _≔_)

open import TheoryGrammar.Instances.Heap.Adjunction
open import TheoryGrammar.Instances.Heap.Precision

-- 0.  A two-cell heap.

h2 : Heap
h2 = (0 , v0) ∷ (1 , v1) ∷ []

c0 c1 : Heap
c0 = single 0 v0
c1 = single 1 v1

-- 1. IT SPLITS FOUR WAYS, and every one is a term of `Split appop`.

sp∅ spL spR spAll : heapFib .Split appop h2
sp∅   = []  , h2  , ilv-nilL h2      , tt
spL   = c0  , c1  , left (right nil) , ((tt , tt) , tt)
spR   = c1  , c0  , right (left nil) , ((tt , tt) , tt)
spAll = h2  , []  , ilv-nilR h2      , #-nil h2

private
  -- one observation, five cases: the term under test is written once.
  _ : passes ((λ p → heapFib .parts appop h2 (p .fst) (p .snd)) at
               ( (sp∅   , true)  ≔ []
               ∷ (spL   , true)  ≔ c0
               ∷ (spL   , false) ≔ c1
               ∷ (spR   , true)  ≔ c1
               ∷ (spAll , true)  ≔ h2
               ∷ [] ))
  _ = refl

-- 2.  `∗` AT THOSE SPLITTINGS, and `∗-comm` computing on them --
-- which exercises `ilv-sym` and `#-sym`.

w01 : ((0 ↦ v0) ∗ (1 ↦ v1)) h2
w01 = spL , boolΠ Eq.refl Eq.refl

w10 : ((1 ↦ v1) ∗ (0 ↦ v0)) h2
w10 = ∗-comm (0 ↦ v0) (1 ↦ v1) h2 w01

private
  -- the commuted witness really is the OTHER splitting
  _ : passes ((λ p → heapFib .parts appop h2 (p .fst) (p .snd)) at
               ( (w01 .fst , true)  ≔ c0
               ∷ (w10 .fst , true)  ≔ c1
               ∷ (w10 .fst , false) ≔ c0
               ∷ [] ))
  _ = refl

-- 3.  `emp` IS A UNIT, and the round trip carries a value through.
-- A grammar constant in the heap makes the test read a `Val` back,
-- so a broken unit law cannot pass by accident.

private
  V : Gr
  V _ = Val

  _ : passes ( emp-∗ V h2 (emp-∗-I V h2 v2) ≔ v2
             ∷ ∗-emp V h2 (∗-emp-I V h2 v2) ≔ v2
             ∷ [] )
  _ = refl

  -- ... and the two spellings of `emp` agree at the empty heap.  Its own
  -- suite: the observed type is an `Eq.≡`, not a `Val`, and `passes`
  -- needs a homogeneous list.
  _ : passes ( emp⊢empR [] (empR⊢emp [] Eq.refl) ≔ Eq.refl ∷ [] )
  _ = refl

-- 4. THE WAND APPLIES.

H : Gr
H _ = Heap

-- "give me a heap disjoint from mine and I hand back the join"
joinW : ((0 ↦ v0) ─∗ H) c1
joinW = wandIso (0 ↦ v0) H c1 .Iso.inv (λ u h ilv apt a → h)

starW : ((0 ↦ v0) ∗ ((0 ↦ v0) ─∗ H)) h2
starW = spL , boolΠ Eq.refl joinW

private
  -- both spellings of applying the wand, and the textbook form
  _ : passes ( wand-app (0 ↦ v0) H h2 starW ≔ h2
             ∷ wandIso (0 ↦ v0) H c1 .Iso.fun joinW c0 h2 (left (right nil))
                       ((tt , tt) , tt) Eq.refl ≔ h2
             ∷ [] )
  _ = refl

-- 5.  PRECISION COMPUTES.  `preciseI-↦` merges two decompositions of
-- `h2` whose `0 ↦ v0` part coincides; `ilv-det` is what identifies
-- their complements, and both payloads must survive.

private
  L : Gr
  L _ = Loc

  dV : ((0 ↦ v0) ∗ V) h2
  dV = spL , boolΠ Eq.refl v2

  dL : ((0 ↦ v0) ∗ L) h2
  dL = spL , boolΠ Eq.refl 7

  merged : ((0 ↦ v0) ∗ (V & L)) h2
  merged = preciseI-↦ 0 v0 V L h2 (dV , dL)

  -- both payloads survive the merge -- observed as one pair, so the two
  -- checks share a suite despite having different component types
  _ : passes {X = Val × Loc}
             ( (merged .snd false .fst , merged .snd false .snd) ≔ (v2 , 7)
             ∷ [] )
  _ = refl

  _ : passes ( heapFib .parts appop h2 (merged .fst) false ≔ c1 ∷ [] )
  _ = refl
