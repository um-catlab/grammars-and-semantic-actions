{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE VALUE-LEVEL SQUARE IS FALSE FOR THE TERM-DIRECTED BACKEND TOO --
  AND FOR A COMPLETELY DIFFERENT REASON THAN `noBlindBackend`.

  `Compile/Semantics/Simulation.agda` shows the three HEAP backends can
  never satisfy the square: their compilers take a `Usage` and never a
  term, so two distinct closed terms at the same usage are sent to the
  same program.  That is a failure of INJECTIVITY, and it is fixed by
  making the compiler term-directed.

  `Compile.LinToRust.Codegen.compileRust` IS term-directed, and the
  `Simulation` module there states

      Simulates = (t v : Tm []) → t ⇓ₛ v → compileRust t ⇓ compileRust v

  with the intention that `_⇓ₛ_` be `Compile.Semantics.CBV._⇓_`.  THIS
  IS STILL FALSE, and this file proves it.  The obstruction is not
  blindness; it is that

      LEVEL-BASED NAMING IS NOT STABLE UNDER SUBSTITUTION.

  ------------------------------------------------------------------
  THE WITNESS
  ------------------------------------------------------------------

      bigT  =  (λf. λx. f x) (λy. y)          -- closed, linear

  The SOURCE contracts the outer redex.  `Opt.subS`'s `tlam` clause
  pushes the argument under the residual binder with `insT mhere`, so
  the substituted copy of `λy.y` ends up ONE BINDER DEEPER than it was,
  and `compileE` -- which names a binder by the DEPTH it occurs at --
  gives it the level `1`.  The residual `λx` is now outermost, so it
  gets level `0`:

      compileRust (evalV bigT)
        = rClos 0 (rCall (rClos 1 (rVar (bnd 1))) (rVar (bnd 0)))

  The TARGET contracts the same redex with `Eval.substE`, which plants
  the argument VERBATIM.  The argument was compiled at depth 0, so it
  keeps level `0`; the residual binder was compiled at depth 1, so it
  keeps level `1`:

      evalRust (compileRust bigT)
        = rClos 1 (rCall (rClos 0 (rVar (bnd 0))) (rVar (bnd 1)))

  The two are α-equivalent and DISTINCT.  Both computations are `refl`
  below, so nothing here is an argument by hand.

  ------------------------------------------------------------------
  WHY THIS IS THE INTERESTING FAILURE
  ------------------------------------------------------------------

  Every ingredient of the square is correct.  `compileRust` is a
  faithful translation; `usesCompile` proves it linear in exactly the
  source's names; `⇓` is deterministic; CBV is the right strategy in
  the right order (S2); values are λs (S3).  What fails is the
  EQUALITY in the conclusion, and only the equality: the target's
  answer and the compilation of the source's answer are the same term
  up to renaming of binders.

  So the repair is not to the compiler or to the semantics but to the
  STATEMENT: the conclusion must be relatedness by a binary logical
  relation between source terms and target expressions, of which
  `compileRust` is one section.  That relation is
  `Compile.Relational.Base`, and `Compile.Relational.Square` is the
  repaired square.

  Note what this says about `Codegen`'s own `refl` block: line 558's

      valOf (evalRust 20 (rCall (compileRust appLin) (compileRust idLin)))
        ≡ just (rClos 1 (rCall (rClos 0 (rVar (bnd 0))) (rVar (bnd 1))))

  is exactly the left-hand side of the counterexample.  The `refl`
  block checks the target's answer; it never compares it with the
  compilation of the SOURCE's answer, which is where the discrepancy
  lives.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1: `IsJust`/`theJust` (a `Maybe` eliminator at a `Unit`/`⊥`
  motive, in `Syntax.Same`'s style, so that the derivation carried by
  `evalRust` can be projected out by computation and never by a match
  on a neutral), and `clevel`, a tag on `RExpr`.  Everything else is a
  composite.
-}
open import Cubical.Foundations.Prelude

module Compile.Relational.Refutation where

open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Nat using (ℕ; zero; suc; snotz)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import Compile.LinToRust.Codegen
import Compile.Semantics.CBV as S
import TheoryGrammar.Instances.LinLam.Syntax as L

-- ==================================================================
-- §0  PROJECTING THE DERIVATION OUT OF `evalRust`.
--
-- `Result e = Maybe (Σ[ v ] (e ⇓ v))`, so the executable evaluator
-- already carries the derivation the square is about; all that is
-- needed is to observe that on a CONCRETE closed expression it is a
-- `just`.  PRIMITIVE (phase 1): the motive is `Unit`/`⊥` so the
-- observation is `tt` and never blocks a `refl`.
-- ==================================================================

IsJust : {A : Type₀} → Maybe A → Type₀
IsJust nothing  = ⊥
IsJust (just _) = Unit

theJust : {A : Type₀} (m : Maybe A) → IsJust m → A
theJust (just a) _ = a

-- ==================================================================
-- §1  THE WITNESS.
-- ==================================================================

-- `(λf. λx. f x) (λy. y)`.  `appLin` and `idLin` are `Codegen`'s own
-- test terms; the splitting is `unil` because both are closed.
bigT : L.Tm []
bigT = L.tapp L.unil appLin L.idLin

-- the SOURCE's answer, by `CBV.eval` -- which is total, so this is a
-- definition and not an assumption
bigV : L.Tm []
bigV = S.evalV bigT

bigStep : bigT S.⇓ bigV
bigStep = S.evalD bigT

-- ------------------------------------------------------------------
-- the two sides, computed.  Both `refl`.
-- ------------------------------------------------------------------

-- the compilation of the SOURCE's answer: the residual binder is now
-- OUTERMOST, hence level 0, and the substituted `λy.y` sits one binder
-- deeper, hence level 1
_ : compileRust bigV
  ≡ rClos 0 (rCall (rClos 1 (rVar (bnd 1))) (rVar (bnd 0)))
_ = refl

-- the TARGET's answer: `substE` plants the argument verbatim, so the
-- substituted `λy.y` keeps the level 0 it was compiled with and the
-- residual binder keeps its level 1
targetRun : Σ[ w ∈ RExpr ] (compileRust bigT ⇓ w)
targetRun = theJust (evalRust 20 (compileRust bigT)) tt

_ : targetRun .fst
  ≡ rClos 1 (rCall (rClos 0 (rVar (bnd 0))) (rVar (bnd 1)))
_ = refl

-- ==================================================================
-- §2  THE REFUTATION.
--
-- `Eval.⇓-det` turns the square into an EQUATION between the two
-- expressions above, and they differ already at their outermost
-- binder's level.  `clevel` reads that level off; it is PRIMITIVE
-- (phase 1) and its only job is to be `1` on one side and `0` on the
-- other.
-- ==================================================================

clevel : RExpr → ℕ
clevel (rVar _)       = 0
clevel (rClos n _)    = n
clevel (rCall _ _)    = 0
clevel (rCtor _)      = 0
clevel (rMatch _ _ _) = 0
clevel (rLet _ _ _)   = 0

open Simulation S._⇓_

-- THE VERDICT.  A term-directed compiler escapes `noBlindBackend`, and
-- still cannot satisfy the square ON THE NOSE, because the equality in
-- its conclusion is too strong: `compileRust` does not commute with
-- substitution, only with substitution-up-to-renaming.
noNoseSquare : Simulates → ⊥
noNoseSquare sq = snotz (cong clevel (Eq.eqToPath step))
  where
  step : targetRun .fst Eq.≡ compileRust bigV
  step = ⇓-det (targetRun .snd) (sq bigT bigV bigStep)

-- ------------------------------------------------------------------
-- ... and, for the record, the two answers really are DIFFERENT terms
-- and not merely two names for one.  (`clevel` of the left is `1`, of
-- the right is `0`.)
-- ------------------------------------------------------------------

_ : clevel (targetRun .fst) ≡ 1
_ = refl

_ : clevel (compileRust bigV) ≡ 0
_ = refl
