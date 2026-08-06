{-
  THE FOUR MODES SEPARATE, and they compute.

  Each `refl` holds only if `Uses`, the substrate's `dec-⊗ˢ`, the
  residual's transport and `dec-map` all reduce.  Acceptance is OBSERVED
  with `⊕-E` into a constant grammar (`accepts`), never by matching a
  decision.

                 ordered  linear  affine  relevant
      λx.x          T        T       T        T
      λx.λy.x       F        F       T        F     -- weakening only
      λx.x x        F        F       F        T     -- contraction only
      λx.λy.y x     F        T       T        T     -- exchange only
      λx.λy.x y     T        T       T        T
      S             F        F       F        T     -- contraction only
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Modes.Tests where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool
open import Cubical.Data.Unit
open import Cubical.Data.List using ([])
open import Cubical.Data.Nat using (ℕ; discreteℕ)

open import TheoryGrammar.Instances.Lambda.Substrate
open import TheoryGrammar.Instances.Lambda.Modes.Instances

open Terms ℕ using (Raw; var; app; lam)
open Modes ℕ discreteℕ

tI tK tW tC tB tS : Raw
tI = lam 0 (var 0)                                   -- λx. x
tK = lam 0 (lam 1 (var 0))                           -- λx. λy. x
tW = lam 0 (app (var 0) (var 0))                     -- λx. x x
tC = lam 0 (lam 1 (app (var 1) (var 0)))             -- λx. λy. y x
tB = lam 0 (lam 1 (app (var 0) (var 1)))             -- λx. λy. x y
tS = lam 0 (lam 1 (lam 2 (app (app (var 0) (var 2))  -- λx. λy. λz. (x z)(y z)
                              (app (var 1) (var 2)))))

-- ==================================================================
-- ORDERED
-- ==================================================================
_ : Ord.accepts tI [] tt ≡ true
_ = refl
_ : Ord.accepts tK [] tt ≡ false
_ = refl
_ : Ord.accepts tW [] tt ≡ false
_ = refl
_ : Ord.accepts tC [] tt ≡ false
_ = refl
_ : Ord.accepts tB [] tt ≡ true
_ = refl
_ : Ord.accepts tS [] tt ≡ false
_ = refl

-- ==================================================================
-- LINEAR
-- ==================================================================
_ : Lin.accepts tI [] tt ≡ true
_ = refl
_ : Lin.accepts tK [] tt ≡ false
_ = refl
_ : Lin.accepts tW [] tt ≡ false
_ = refl
_ : Lin.accepts tC [] tt ≡ true
_ = refl
_ : Lin.accepts tB [] tt ≡ true
_ = refl
_ : Lin.accepts tS [] tt ≡ false
_ = refl

-- ==================================================================
-- AFFINE
-- ==================================================================
_ : Aff.accepts tI [] tt ≡ true
_ = refl
_ : Aff.accepts tK [] tt ≡ true
_ = refl
_ : Aff.accepts tW [] tt ≡ false
_ = refl
_ : Aff.accepts tC [] tt ≡ true
_ = refl
_ : Aff.accepts tB [] tt ≡ true
_ = refl
_ : Aff.accepts tS [] tt ≡ false
_ = refl

-- ==================================================================
-- RELEVANT
-- ==================================================================
_ : Rel.accepts tI [] tt ≡ true
_ = refl
_ : Rel.accepts tK [] tt ≡ false
_ = refl
_ : Rel.accepts tW [] tt ≡ true
_ = refl
_ : Rel.accepts tC [] tt ≡ true
_ = refl
_ : Rel.accepts tB [] tt ≡ true
_ = refl
_ : Rel.accepts tS [] tt ≡ true
_ = refl
