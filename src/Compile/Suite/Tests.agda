{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE SUITE, INSTANTIATED -- and the proof that it can SEE A FAILURE.

  ------------------------------------------------------------------
  WHAT IS HERE
  ------------------------------------------------------------------

  ONE suite (`Compile/Suite/Backend.agda`), instantiated four times:

      §2   ARM alone
      §3   Rust alone
      §4   ARM + Rust                -- and ARM + Rust + the IR
      §5   ARM + Rust, over GENERATED terms
      §6   ARM + a DELIBERATELY BROKEN Rust

  Nothing is copied between them: the terms are written once, the
  backends are written once (`Compile/Suite/Backends.agda`), and each
  section is a module application.

  ------------------------------------------------------------------
  §6 IS THE POINT
  ------------------------------------------------------------------

  A harness that cannot exhibit a failure is worthless, and "all my tests
  pass" is not evidence that it could.  So §6 mutates one clause of the
  Rust code generator -- `tlam` compiles its body at the SAME depth,
  i.e. one `suc` is deleted -- and shows:

    * the harness's Bool goes `false` on a term the honest pair agrees on;
    * the ROW says which backend said what, so the failure is legible;
    * and the failure is turned into a REFUTATION,

          brokenRefutation : (¬G (BR.Agree selfApp)) []

      a function that eats any purported agreement.  That is CLAUDE.md's
      rule taken seriously: `≡ false` says the algorithm returned no, and
      a refutation says there is nothing to return.  `SemanticAction.refute`
      is uniform in the error grammar, so it is the SAME `refl` that
      produces the theorem -- which is exactly why the two kinds of
      negative test look identical until they are put through it.

    * and §6.3 does it at a term the GENERATOR produced rather than one
      chosen by hand: `firstBadOr` searches the generated list, and the
      term it returns is the one the refutation is stated at.

  ------------------------------------------------------------------
  WHAT THE GREEN SECTIONS DO AND DO NOT SAY
  ------------------------------------------------------------------

  §4's agreement is a real, computed fact about three independent
  pipelines -- one of which EXECUTES AArch64 -- at an observable chosen
  so that it is not vacuous (`Backends.agda` §4: `bigT`'s answer is a
  closure over one capture, and all three say so).  It is not a proof
  that the backends agree on every term; it is a proof that they agree on
  these, and the generator in §5 is how that list stops being hand-picked.

  It is also NOT a value-level correctness theorem for any single
  backend.  `Correct.noNoseSquare` and `Relational.Refutation.noNoseSquare`
  refute those, for two different reasons, and the repaired statements
  are `Relational.Square.square` and `Correct.square`.  Agreement between
  backends is a weaker and differently-shaped fact, and its value is that
  it is CHEAP and it is DIFFERENTIAL: it needs no relation, and it fails
  loudly when one pipeline drifts.
-}
open import Cubical.Foundations.Prelude

module Compile.Suite.Tests where

open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.List using (List; []; _∷_; map; length)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty using (⊥*)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
import TheoryGrammar.Decidable.Additive as TD

open import TheoryGrammar.Instances.LinLam.Syntax
open import Compile.Suite.Backend
open import Compile.Suite.Backends
open import Compile.Suite.Generate

import Compile.ClosureConv.Convert as CC
import Compile.LinToRust.Codegen   as RS

-- `¬G` at this theory.  `Backend.agda`'s own application of the
-- decidability layer, so the error grammar below is literally the one
-- `refuteAgree` produces.
open LD using (¬G_)

-- ==================================================================
-- §1  THE TERMS UNDER TEST.
--
-- `Showcase`'s and `ARM.agda` §11's, written once.
--
--     idLin    λx. x
--     selfApp  (λx.x)(λx.x)          -- returns its ARGUMENT
--     bigT     (λf. λx. f x)(λy. y)  -- answer has a NON-EMPTY capture
--     applyK   (λf. f (λz.z))(λx.x)  -- contraction CREATES a redex,
--                                       hence two nested calls live at once
-- ==================================================================

terms : List (Tm [])
terms = idLin ∷ CC.selfApp ∷ CC.bigT ∷ CC.applyK ∷ []

-- ==================================================================
-- §2  (a)  ARM ALONE.
--
-- A one-backend suite agrees vacuously -- `agreeL` of a singleton is
-- `true` with nothing compared -- and saying so is the honest reading:
-- what this instantiation is FOR is the report, i.e. running the AArch64
-- pipeline on every term and reading the answers off in one table.
-- ==================================================================

module A = Suite (armB ∷ [])

_ : A.allAgree terms ≡ true
_ = refl

_ : A.report terms
  ≡ ((("arm64" , just vfun) ∷ []) , true)
  ∷ ((("arm64" , just vfun) ∷ []) , true)
  ∷ ((("arm64" , just vfun) ∷ []) , true)
  ∷ ((("arm64" , just vfun) ∷ []) , true)
  ∷ []
_ = refl

-- ==================================================================
-- §3  (b)  RUST ALONE.  The same suite, a different list.
-- ==================================================================

module R = Suite (rustB ∷ [])

_ : R.allAgree terms ≡ true
_ = refl

_ : R.report terms
  ≡ ((("rust" , just vfun) ∷ []) , true)
  ∷ ((("rust" , just vfun) ∷ []) , true)
  ∷ ((("rust" , just vfun) ∷ []) , true)
  ∷ ((("rust" , just vfun) ∷ []) , true)
  ∷ []
_ = refl

-- ==================================================================
-- §4  (c)  BOTH TOGETHER -- and this one is not vacuous.
--
-- Two pipelines with nothing in common: `armB` closure-converts, emits
-- AArch64 and EXECUTES it on `Control`'s machine, then reads the answer
-- out of the heap; `rustB` emits a Rust expression and evaluates it by
-- substitution.  They meet only at the observable.
-- ==================================================================

module AR = Suite (armB ∷ rustB ∷ [])

_ : AR.allAgree terms ≡ true
_ = refl

_ : AR.disagreements terms ≡ []
_ = refl

-- one row, spelled out.  What the two backends returned NATIVELY at this
-- term is in `Backends.agda` §4b, and it is not the same value in any
-- structural sense -- which is the whole reason the observable stops
-- where it does.
_ : AR.row CC.bigT
  ≡ ( ( ("arm64" , just vfun)
      ∷ ("rust"  , just vfun)
      ∷ [] )
    , true )
_ = refl

-- ... and three at once, adding the IR's own interpreter.  `irB` and
-- `armB` share a `compile` and differ only in `run`, so this row is
-- `ARM.agda` §11's `answerT ≡ runP` recomputed by the harness.
module AIR = Suite (irB ∷ armB ∷ rustB ∷ [])

_ : AIR.allAgree terms ≡ true
_ = refl

-- ==================================================================
-- §5  THE GENERATOR, WIRED IN.
--
-- `closedTms 4` is every closed linear λ-term of derivation height ≤ 4 --
-- nine of them, built AT the empty usage rather than filtered afterwards
-- (`Generate.agda`).  So this is the agreement check over terms nobody
-- chose, which is the whole difference between a regression suite and a
-- property test.
--
-- AND IT IS THE SECTION THAT DID ITS JOB.  On the first draft's finer
-- observable -- the capture tree -- these nine terms produced FOUR
-- disagreements between two backends that are both correct, starting
-- with `λf. λx. f x`.  That is what sent `Backend.agda`'s observable
-- back to `vfun`, and it is the argument that a hand-written table of
-- four terms is not a substitute: all four of those agreed.
-- ==================================================================

_ : length (closedTms 4) ≡ 9
_ = refl

_ : AR.allAgree (closedTms 4) ≡ true
_ = refl

_ : AR.disagreements (closedTms 4) ≡ []
_ = refl

-- ==================================================================
-- §6  THE DELIBERATELY BROKEN BACKEND, AND THE REFUTATION IT PRODUCES.
--
-- ------------------------------------------------------------------
-- 6.1  THE MUTATION.  `Codegen.compileE`'s three clauses, with ONE
-- character deleted: `tlam` compiles its body at depth `d` instead of
-- `suc d`, so the binder it introduces is not counted and the body's
-- variables are named as though they were free.  That is a plausible
-- off-by-one and not a strawman -- `Codegen.agda`'s header says the ONLY
-- thing the compiler decides is a name.
-- ------------------------------------------------------------------

badE : ℕ → {u : Usage} → Tm u → RS.RExpr
badE d (tvar {u} s) = RS.rVar (RS.nameOf d (RS.soloAt 0 u s))
badE d (tapp s f a) = RS.rCall (badE d f) (badE d a)
badE d (tlam b)     = RS.rClos d (badE d b)          -- DROPPED: `suc d`

badRustB : Backend
badRustB .name    = "rust(broken)"
badRustB .Target  = RS.RExpr
badRustB .Answer  = Maybe RS.RExpr
badRustB .compile = badE 0
badRustB .run     = λ e → RS.valOf (RS.evalRust 40 e)
badRustB .decode  = decRM

-- the mutant is not obviously wrong: on `λx.x` it still produces a
-- closure, and the observable cannot tell.  A harness that only tested
-- `idLin` would report green.
_ : Backend.obs badRustB idLin ≡ just vfun
_ = refl

module BR = Suite (armB ∷ badRustB ∷ [])

_ : BR.agreeOn idLin ≡ true
_ = refl

-- ------------------------------------------------------------------
-- 6.2  ... AND THE HARNESS SEES IT ANYWAY.  `(λx.x)(λx.x)` substitutes
-- for a binder the mutant never bound, so the redex contracts to a free
-- variable and `evalRust` is stuck.  The row says which backend said
-- what: DATA, not a typecheck failure.
-- ------------------------------------------------------------------

_ : BR.agreeOn CC.selfApp ≡ false
_ = refl

_ : BR.row CC.selfApp
  ≡ ( ( ("arm64"        , just vfun)
      ∷ ("rust(broken)" , nothing)
      ∷ [] )
    , false )
_ = refl

_ : BR.allAgree terms ≡ false
_ = refl

-- THE WHOLE VERDICT on the four hand-written terms.  TWO of them do not
-- catch the mutant: `idLin` because a mis-depthed binder still produces
-- a closure, and `bigT` because its outer redex substitutes for a binder
-- neither compiler ever consults, so the answer is still an `rClos`.
-- That is the honest reading of a coarse observable -- and it is exactly
-- why §6.4 asks the GENERATOR instead of a hand-written table.
_ : map BR.agreeOn terms ≡ true ∷ false ∷ true ∷ false ∷ []
_ = refl

_ : BR.disagreements terms
  ≡ ( ( ("arm64" , just vfun) ∷ ("rust(broken)" , nothing) ∷ [] ) , false )
  ∷ ( ( ("arm64" , just vfun) ∷ ("rust(broken)" , nothing) ∷ [] ) , false )
  ∷ []
_ = refl

-- ------------------------------------------------------------------
-- 6.3  THE REFUTATION.
--
-- `agrees!` is the decision `agreeDec` observed by `okA` -- the same
-- Bool as `agreeOn`, but arrived at THROUGH the calculus, which is what
-- makes the next line possible.
-- ------------------------------------------------------------------

_ : BR.agrees! CC.selfApp ≡ false
_ = refl

_ : BR.agrees! idLin ≡ true
_ = refl

-- THE PINNED REFUTATION.  The `refl` is the observation of 6.2; what
-- comes back is the ERROR GRAMMAR's payload, and here that is a proof
-- that no agreement on `selfApp` exists.
brokenRefutation : (¬G (BR.Agree CC.selfApp)) []
brokenRefutation = BR.refuteAgree CC.selfApp refl

-- ... and it has content: unfolded, it eats any purported agreement.
noSuchAgreement : BR.Agree CC.selfApp [] → ⊥*
noSuchAgreement = brokenRefutation

-- THE CONTRAST, which is the whole reason the shape matters.  At the
-- HONEST pair the same term, the same suite, the same `refl` -- and what
-- comes back is the agreement ITSELF rather than its refutation.
honestAgreement : AR.Agree CC.selfApp []
honestAgreement = AR.witnessAgree CC.selfApp refl

-- ------------------------------------------------------------------
-- 6.4  ... AT A GENERATED TERM.
--
-- `firstBadOr` searches the generator's output for a disagreement and
-- hands back THE TERM, so the refutation below is stated at a term
-- nobody wrote.  That it turns out to be `selfApp` is the generator
-- rediscovering `Showcase`'s witness, and it is pinned so the reader can
-- see which draw was the culprit.
-- ------------------------------------------------------------------

genBad : Tm []
genBad = BR.firstBadOr idLin (closedTms 4)

_ : genBad ≡ CC.selfApp
_ = refl

genRefutation : (¬G (BR.Agree genBad)) []
genRefutation = BR.refuteAgree genBad refl

-- the honest pair, on the same generated list, has no such term ...
_ : AR.firstBadOr idLin (closedTms 4) ≡ idLin
_ = refl

-- ... and FOUR of the nine generated terms defeat the mutant, against
-- two of the four hand-written ones.  The generator is not producing
-- more terms than a human would; it is producing terms a human did not
-- think to write, which is the only thing a fuzzer is for.
_ : length (BR.disagreements (closedTms 4)) ≡ 4
_ = refl
