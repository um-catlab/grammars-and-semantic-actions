{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE CHECKER COMPUTES, and its negative answers are REFUTATIONS.

  Two things are being demonstrated, and the second is the one that
  matters.

  (1) `linear?` reduces.  It is `runAut`, i.e. `hyloC`, i.e. `löb` over
  the suffix-style order given by `dbGrading`; nothing in the chain is
  postulated or opaque, so the whole decision procedure evaluates and a
  test is one `refl`.  `sizeA` is the same coalgebra at a different
  algebra, and evaluates too.

  (2) A NEGATIVE test is not an observation, it is a theorem.  Per the
  repository's rule, `run f m ≡ false` on its own says only that the
  algorithm answered no.  `refute` (TheoryGrammar.SemanticAction) turns
  that `refl` into the content of the ERROR branch, and the error branch
  of `Dec⟨ Lin ⟩` is `¬G Lin`.  So `noLin` below yields a genuine
  internal refutation `Lin m → ⊥*`: there is NO linear term whose
  skeleton is `λx. x x`.  Nothing was re-proved to get it -- the
  exclusion came with `Dec⟨_⟩`.

  THE THREE CASES are chosen to separate the two halves of linearity:

      λx. x        linear
      λx. x x      rejected -- DUPLICATION, refuted by the absent
                   `(true,true)` constructor of `Use⊎`
      λx. λy. x    rejected -- WEAKENING, refuted by `tlam` demanding
                   `Tm (true ∷ u)`

  An affine checker would accept the third; that it is rejected is the
  evidence that `LinLam/Syntax`'s `Tm` really is linear and not merely
  affine.
-}
module TheoryGrammar.Instances.LinLam.Tests where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.List using ([]; _∷_)
open import Cubical.Data.Nat
open import Cubical.Data.FinData.Base using (Fin)
  renaming (zero to fzero; suc to fsuc)

open import TheoryGrammar.SemanticAction using (passes; _at_; _↦_)
open import TheoryGrammar.Instances.LinLam.DB
open import TheoryGrammar.Instances.LinLam.Check

-- λx. x
idT : DBTm 0
idT = dlam (dvar fzero)

-- λx. x x
dupT : DBTm 0
dupT = dlam (dapp (dvar fzero) (dvar fzero))

-- λx. λy. x
dropT : DBTm 0
dropT = dlam (dlam (dvar (fsuc fzero)))

-- an OPEN term: the free variable 0 of a scope of size 1
openT : DBTm 1
openT = dapp (dvar fzero) (dvar fzero)

-- ==================================================================
-- The suite.  One `refl`, with the term under test written once.
-- ==================================================================

decisions : passes (run linearB at ( (0 , idT)   ↦ true
                                   ∷ (0 , dupT)  ↦ false
                                   ∷ (0 , dropT) ↦ false
                                   ∷ (1 , openT) ↦ false
                                   ∷ []))
decisions = refl

sizes : passes (run sizeA at ( (0 , idT)   ↦ 2
                             ∷ (0 , dupT)  ↦ 4
                             ∷ (0 , dropT) ↦ 3
                             ∷ []))
sizes = refl

-- ==================================================================
-- ... and the negative answers, as refutations.
-- ==================================================================

noLin : (m : Term•) → run linearB m ≡ false → (¬G Lin) m
noLin = refute Lin (¬G Lin) linear?

-- THEOREM: no linear term erases to `λx. x x`.
no-dup : (¬G Lin) (0 , dupT)
no-dup = noLin (0 , dupT) refl

-- THEOREM: no linear term erases to `λx. λy. x` -- linearity, not
-- affineness.
no-drop : (¬G Lin) (0 , dropT)
no-drop = noLin (0 , dropT) refl

-- ... and the positive answer carries the linear term itself.
yesLin : (m : Term•) → run linearB m ≡ true → Lin m
yesLin = witness Lin (¬G Lin) linear?

is-id : Lin (0 , idT)
is-id = yesLin (0 , idT) refl
