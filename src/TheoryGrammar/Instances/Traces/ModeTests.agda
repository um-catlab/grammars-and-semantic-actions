{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE PARTIALLY COMMUTATIVE MODE SEPARATES ordered from linear.

  Names 0 and 1 are independent; 2 commutes with nothing.  So the term
  that needs exchange is accepted at names {0,1} and REJECTED at names
  {0,2} -- the same term, the same grammar, one substrate, two answers.
  That is the substructural reading of the interpolation.

                        ordered  TRACE  linear
      λx.x                 T       T      T
      λx.λy.x              F       F      F     -- no weakening
      λx.x x               F       F      F     -- no contraction
      λ0.λ1. x1 x0         F       T      T     -- 0 ⌣ 1
      λ0.λ2. x2 x0         F       F      T     -- 0 not ⌣ 2
      λ0.λ1. x0 x1         T       T      T
-}
module TheoryGrammar.Instances.Traces.ModeTests where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool
open import Cubical.Data.Unit
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Nat using (ℕ; zero; suc; discreteℕ)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty as E using (⊥)

open import TheoryGrammar.Enumerable using (No)
open import TheoryGrammar.SemanticAction using (passes; _↦_; _at_)
open import TheoryGrammar.Instances.Lambda.Fibered

import TheoryGrammar.Instances.Traces.Mode as TrMode

-- 0 and 1 commute; nothing else does
Ind : ℕ → ℕ → Type₀
Ind zero       (suc zero) = Unit
Ind (suc zero) zero       = Unit
Ind _          _          = ⊥

decInd : (x y : ℕ) → Ind x y ⊎ No (Ind x y)
decInd zero          zero          = inr λ ()
decInd zero          (suc zero)    = inl tt
decInd zero          (suc (suc n)) = inr λ ()
decInd (suc zero)    zero          = inl tt
decInd (suc zero)    (suc m)       = inr λ ()
decInd (suc (suc n)) m             = inr λ ()

isPropInd : (x y : ℕ) → isProp (Ind x y)
isPropInd zero          zero          = E.isProp⊥
isPropInd zero          (suc zero)    = isPropUnit
isPropInd zero          (suc (suc n)) = E.isProp⊥
isPropInd (suc zero)    zero          = isPropUnit
isPropInd (suc zero)    (suc m)       = E.isProp⊥
isPropInd (suc (suc n)) m             = E.isProp⊥

open Terms ℕ using (Raw; var; app; lam)
open TrMode ℕ Ind decInd isPropInd discreteℕ using (module Trace)

tI tK tW tC01 tC02 tB : Raw
tI   = lam 0 (var 0)                          -- λx. x
tK   = lam 0 (lam 1 (var 0))                  -- λx. λy. x
tW   = lam 0 (app (var 0) (var 0))            -- λx. x x
tC01 = lam 0 (lam 1 (app (var 1) (var 0)))    -- exchange at an INDEPENDENT pair
tC02 = lam 0 (lam 2 (app (var 2) (var 0)))    -- exchange at a DEPENDENT pair
tB   = lam 0 (lam 1 (app (var 0) (var 1)))    -- no exchange needed

_ : passes ((λ t → Trace.run (Trace.accepts t) []) at
             ( tI   ↦ true
             ∷ tK   ↦ false
             ∷ tW   ↦ false
             ∷ tC01 ↦ true
             ∷ tC02 ↦ false
             ∷ tB   ↦ true
             ∷ [] ))
_ = refl

-- ==================================================================
-- THE `F` COLUMN, AS THEOREMS.
--
-- The batch above reports what the checker RETURNS.  The header table
-- claims something stronger: that no use-derivation exists.  `refute`
-- (TheoryGrammar.SemanticAction) turns each negative observation into
-- the refutation the decision was carrying all along, from the same
-- `refl` -- see `Instances/Lambda/Modes/Tests` for the four-mode
-- version of this block.
-- ==================================================================

refuteTr : (t : Raw) → Trace.run (Trace.accepts t) [] ≡ false
         → (Trace.¬G (Trace.Uses t)) []
refuteTr t = Trace.refute (Trace.Uses t) (Trace.¬G (Trace.Uses t)) (Trace.check t) []

no-trace-K : (Trace.¬G (Trace.Uses tK)) []      -- no weakening
no-trace-K = refuteTr tK refl

no-trace-W : (Trace.¬G (Trace.Uses tW)) []      -- no contraction
no-trace-W = refuteTr tW refl

-- THE SEPARATION, stated rather than observed: exchange at a DEPENDENT
-- pair is refuted, while `tC01` -- the same term at an independent pair
-- -- is accepted above.  One substrate, two answers.
no-trace-C02 : (Trace.¬G (Trace.Uses tC02)) []
no-trace-C02 = refuteTr tC02 refl
