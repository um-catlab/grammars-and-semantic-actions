{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE REPAIRED SIMULATION SQUARE.

  `Compile.LinToRust.Codegen.Simulation` states

      Simulates = (t v : Tm []) → t ⇓ₛ v → compileRust t ⇓ compileRust v

  and `Compile.Relational.Refutation` proves it FALSE: `compileE` names
  a binder by its absolute depth, source substitution moves the
  residual body one binder shallower, and `substE` plants the argument
  verbatim, so the two answers differ by a renaming.  This file states
  and proves the version that is true:

      square : t ⇓ₛ v  →  Rel ν t e
             →  Σ[ w ] (e ⇓ w) × Rel ν v w

  -- the target evaluates, and its answer REALISES the source's answer.
  Only the `≡` changed.

  ------------------------------------------------------------------
  WHY THE INDUCTION IS STRUCTURAL
  ------------------------------------------------------------------

  `_⇓_` is an inductive family, so `⇓app`'s three premises -- callee,
  argument, and BODY AT THE VALUE -- are all subderivations.  No
  well-founded recursion and no size measure is needed here; the
  measure `Compile.Semantics.Size` provides is what makes the
  NORMALISER terminate, and this file deliberately does not repeat it.

  Every term in a closed call-by-value derivation is closed, which is
  what discharges `relSubst`'s `Empty u₂` with `tt`.

  ------------------------------------------------------------------
  THE ONE HYPOTHESIS, AND WHY IT COSTS NOTHING
  ------------------------------------------------------------------

  `relSubst` wants `Avoid 0 (ext n ν)` -- the substituted position's
  name differs from every other position's.  At the binder that is

      (p : ℕ) → DifI (ν p) (bnd n)

  and `nameOf 0` is `fre`, so `DifI (fre p) (bnd n)` is `Unit` and the
  whole hypothesis is `λ p n → tt`.  A free variable is never a binder
  level; that is the entire content, and it is why `Ident` was split
  into `bnd` and `fre` in the first place.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1: this is a metatheorem about the compiler, not a program in
  the calculus.
-}
open import Cubical.Foundations.Prelude

module Compile.Relational.Square where

open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import Compile.LinToRust.Codegen
open import Compile.Relational.Base
open import Compile.Relational.Names
open import Compile.Relational.Subst
open import Compile.Relational.Refutation using (targetRun)
import Compile.Semantics.CBV as S
import TheoryGrammar.Instances.LinLam.Syntax as L
import TheoryGrammar.Instances.LinLam.Opt as O

-- ==================================================================
-- §1  THE HYPOTHESIS ON THE ASSIGNMENT, AND WHAT IT BUYS.
--
-- `FreeNames ν` says every position is called by a FREE variable, not
-- a binder level.  `nameOf 0` is exactly `fre`, so it holds by `tt`.
-- ==================================================================

FreeNames : NameF → Type₀
FreeNames ν = (p n : ℕ) → DifI (ν p) (bnd n)

freeNames-nameOf0 : FreeNames (nameOf 0)
freeNames-nameOf0 p n = tt

-- ... and it is precisely `relSubst`'s side condition at a binder
avoid₀ : {ν : NameF} → FreeNames ν → (n : ℕ) → Avoid 0 (ext n ν)
avoid₀ fr n zero    d = E.rec d
avoid₀ fr n (suc p) d = fr p n

-- ==================================================================
-- §2  THE SQUARE.
--
--   ⇓lam   a source value is a λ, a target value is a closure, and the
--          relation between them is the derivation we were handed.
--   ⇓app   evaluate the callee (which must be a closure, by `rlam`),
--          evaluate the argument, then `relSubst` -- whose conclusion
--          `substE ((ext n ν) 0) wa b''` IS the redex `⇓call`
--          contracts, because `(ext n ν) 0` reduces to `bnd n`.
-- ==================================================================

square : {ν : NameF} → FreeNames ν
       → {t v : L.Tm []} → t S.⇓ v → {e : RExpr}
       → Rel ν t e
       → Σ[ w ∈ RExpr ] ((e ⇓ w) × Rel ν v w)

square fr S.⇓lam (rlam n pn rb) =
  rClos n _ , ⇓clos n _ , rlam n pn rb

square fr (S.⇓app df da dw) (rapp rf ra)
  with square fr df rf | square fr da ra
... | (_ , df' , rlam n pn rb') | (_ , da' , ra') =
  let (w' , dw' , rw') =
        square fr dw (relSubst O.mhere L.unil tt (avoid₀ fr n) rb' ra')
  in w' , ⇓call df' da' dw' , rw'

-- ==================================================================
-- §3  AT THE COMPILER.
-- ==================================================================

squareRust : {t v : L.Tm []} → t S.⇓ v
           → Σ[ w ∈ RExpr ] ((compileRust t ⇓ w) × Rel (nameOf 0) v w)
squareRust {t} d = square freeNames-nameOf0 d (relCompileRust t)

-- THE FORM A CLIENT WANTS.  `Eval.⇓-det` upgrades "there is a target
-- run that realises the source value" to "EVERY target run does".
-- This is `Codegen.Simulation.evalAgrees` with `Rel` in place of the
-- `≡` that was refuted.
squareDet : {t v : L.Tm []} → t S.⇓ v
          → (w : RExpr) → compileRust t ⇓ w → Rel (nameOf 0) v w
squareDet d w dw =
  let (w₀ , d₀ , r₀) = squareRust d
  in Eq.transport (λ z → Rel _ _ z) (⇓-det d₀ dw) r₀

-- ==================================================================
-- §4  THE CAPSTONE.
--
-- `Refutation` exhibits a source value `bigV` and a target answer
-- `targetRun .fst` that are provably DISTINCT from `compileRust bigV`.
-- `squareDet` relates them anyway -- which is the whole point of the
-- repair, now obtained from the general theorem rather than by
-- exhibiting a derivation by hand.
-- ==================================================================

capstone : Rel (nameOf 0) bigV (targetRun .fst)
capstone = squareDet (S.evalD bigT) (targetRun .fst) (targetRun .snd)

-- and that answer really is the one `Refutation` measured
_ : targetRun .fst ≡ tgtV
_ = refl
