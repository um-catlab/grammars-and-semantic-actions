{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  SPANS AS A DYNAMIC PROGRAMMING PROBLEM.

  `DP.DPGraded` derives the dependency order `_≺ᵖ_` -- "v is a proper
  slot of some splitting of w" -- and its well-foundedness from
  `spanGraded` alone, so nothing about subspans is stated anywhere.  All
  that is left for the instance is `Finitary`: the dependencies of a span
  must be finitely LISTED.

  And that is `DecEnumerable` restated.  The dependencies of `(i , n)`
  are the two slots of each of its `n+1` cuts, so `deps` is
  `Spans.Base.allCuts` mapped over the arity and `depsOk` is
  `allCutsComplete` -- the same two facts the DECISION already needed in
  order to refute a tensor.  A theory that can enumerate its splittings
  can tabulate its recursion; nothing further is assumed.
-}
module TheoryGrammar.Instances.Spans.DP where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.List

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Graded
open import TheoryGrammar.Enumerable
open import TheoryGrammar.DP

open import TheoryGrammar.Instances.Spans.Graded

open DPGraded spanGraded public

-- the two slots of one cut, as worlds
slotsOf : (s : Span) → SpanSplit cat s → List World
slotsOf s c = (tt , SpanParts cat s c true)
            ∷ (tt , SpanParts cat s c false)
            ∷ []

-- ... over every cut: the dependencies of a span
spanDeps : World → List World
spanDeps w = cmap (slotsOf (w .snd)) (allCuts (w .snd .snd))

-- ... and the listing misses none.  `allCutsComplete` is the whole
-- proof; the arity contributes the two-case split.
spanDepsOk : (w v : World) → v ≺ᵖ w → v ∈L spanDeps w
spanDepsOk _ _ (slot cat m c true  _) =
  ∈cmap (slotsOf m) (allCutsComplete (m .snd) c) here
spanDepsOk _ _ (slot cat m c false _) =
  ∈cmap (slotsOf m) (allCutsComplete (m .snd) c) (there here)

-- THE INSTANCE.  Everything a tabulated fixpoint needs at spans.
module _ {ℓM : Level} (A : World → Type ℓM) where
  open Problem A

  spanFinitary : Finitary
  spanFinitary .Finitary.deps   = spanDeps
  spanFinitary .Finitary.depsOk = spanDepsOk
