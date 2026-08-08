{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  TASK 5, AND A DEFECT FOUND BY DOING IT.

  ==================================================================
  THE DEFECT.  `Compile.LinToRust.Codegen.srcTm` renders a whole Rust
  compilation unit, and `Codegen.agda`'s tests pin its output:

      "enum U { A, B }\n\nfn main() {\n    let _ = move |x0| x0;\n}\n"

  THAT PROGRAM DOES NOT COMPILE.  `rustc 1.93.0` rejects it, and the two
  others the file pins as well:

      id.rs    error[E0282]: type annotations needed
      self.rs  error[E0282]: type annotations needed
      app.rs   error[E0282]: type annotations needed

  The cause is the WRAPPER and not the expression, which is worth being
  precise about because it decides how much is affected.  Measured, by
  three one-line variants:

      let _ = move |x0| x0;             FAILS   -- as emitted
      let _ = move |x0: U| x0;          COMPILES-- parameter annotated
      let f = move |x0| x0;             COMPILES-- expression VERBATIM,
      let _: U = f(U::A);                          with a call site

  So for a FIRST-ORDER term `renderExpr` is right and `renderUnit` is
  wrong: binding a closure to `_` gives `rustc` nothing to infer the
  parameter type from.

  ------------------------------------------------------------------
  AND THERE IS A SECOND DEFECT, WHICH IS NOT THE WRAPPER'S.  Supplying
  the call site repairs `idLin` and does NOT repair `appLin`:

      ((move |x0| move |x1| (x0)(x1))(move |x0| x0))(U::A)
        error[E0282]: type annotations needed
        help: consider giving this closure parameter an explicit type

  The trigger is NARROWER than "higher-order", and the demo script
  measures where the line falls.  `(λx.x)(λx.x)` compiles once there is
  a call site: inference flows outside-in, from `U::A` through the
  argument closure.  `λf.λx. f x` does not, because `x0` is APPLIED in
  the body (`x0(x1)`), and inferring a callable type for a closure
  PARAMETER needs a bound that a bare `move |x0|` cannot carry.

  So: a closure parameter that is merely PASSED is fine; one that is
  CALLED is not.  The measured repair is a trait object:

      (move |x0: Box<dyn Fn(U) -> U>| move |x1: U| x0(x1))
        (Box::new(move |x0: U| x0))                    COMPILES -> U::A

  That is a change to `Syntax.RExpr` -- `rClos` emits an unannotated
  parameter and there is no `Box`/`dyn` former -- so it is a CODEGEN
  defect and not a rendering one.  The chain compiles higher-order
  linear terms to Rust that is well-formed and not well-typed.

  Neither defect touches a theorem: `_⇓_` and `squareDet` are about
  `RExpr`, and `RExpr` is a fine abstract syntax.  What is refuted is
  the informal claim that the emitted text is Rust one can compile.

  NOTHING VERIFIED IS AFFECTED.  `_⇓_` is a relation on `RExpr`, and
  `Compile.Relational.Square.squareDet` is about `RExpr`; neither
  mentions the rendering.  `renderUnit` (`Syntax.agda`) is unverified
  text assembly sitting outside every theorem, which is exactly where a
  defect of this kind can hide -- and it is why "the emitted code is
  real Rust" wanted checking rather than asserting.

  THE REPAIR IS NOT APPLIED TO `Syntax.agda`, deliberately: its `refl`
  tests pin the current output and the handoff forbids breaking green
  files.  §1 below is an alternative unit renderer in a new file.

  ==================================================================
  THE DIFFERENTIAL TEST.  §2 derives, in Agda, what `_⇓_` says the
  compiled term does when applied to `U::A`; §1 emits a Rust program
  that does the same thing and prints the answer.  Running it is
  EVIDENCE, not proof -- `_⇓_` being Rust's real semantics is the
  residual trust in this chain and no Agda file can discharge it.

  PHASE.  §1 is phase-1 text assembly, marked.  §2 is derivations.
-}
open import Cubical.Foundations.Prelude

module Chain.RustEmit where

open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Nat using (ℕ; zero; suc)

open import Agda.Builtin.String using (primStringAppend) renaming (String to UString)

open import Compile.LinToRust.Syntax
open import Compile.LinToRust.Eval

import TheoryGrammar.Instances.LinLam.Syntax as L
import Compile.LinToRust.Codegen             as FR

-- ==================================================================
-- §1  A COMPILATION UNIT THAT `rustc` ACCEPTS.
--
-- PRIMITIVE (phase 1): text assembly, exactly as `Syntax.renderUnit`
-- is.  The one difference is that the compiled expression is APPLIED,
-- which is what fixes the closure's parameter type -- and applying it
-- is also what makes the program observable, so the same change buys
-- the differential test.
-- ==================================================================

_++s_ : UString → UString → UString
_++s_ = primStringAppend

infixr 5 _++s_

-- the program: apply the compiled term to `U::A` and print the answer
runnable : RExpr → UString
runnable e =
  "#[derive(Debug)]\nenum U { A, B }\n\nfn main() {\n    let r = ("
  ++s renderExpr e
  ++s ")(U::A);\n    println!(\"{}\", match r { U::A => \"U::A\", U::B => \"U::B\" });\n}\n"

-- ------------------------------------------------------------------
-- The two programs, pinned.  `renderExpr` of the compiled term is
-- `Codegen`'s own verified-shape output; only the wrapper is new.
-- ------------------------------------------------------------------

idExpr appExpr : RExpr
idExpr  = FR.compileRust L.idLin
appExpr = FR.compileRust FR.appLin

_ : renderExpr idExpr ≡ "move |x0| x0"
_ = refl

_ : renderExpr appExpr ≡ "move |x0| move |x1| (x0)(x1)"
_ = refl

idProg : UString
idProg = runnable idExpr

_ : idProg
  ≡ "#[derive(Debug)]\nenum U { A, B }\n\nfn main() {\n    let r = (move |x0| x0)(U::A);\n    println!(\"{}\", match r { U::A => \"U::A\", U::B => \"U::B\" });\n}\n"
_ = refl

-- ==================================================================
-- §2  WHAT `_⇓_` SAYS.  These are derivations, not tests: the Agda
-- side's prediction for each program §1 emits.
-- ==================================================================

-- the compiled identity IS the closure the renderer showed
_ : idExpr ≡ rClos 0 (rVar (bnd 0))
_ = refl

-- APPLYING IT TO `U::A` YIELDS `U::A`.
idAppA : rCall idExpr (rCtor cA) ⇓ rCtor cA
idAppA = ⇓call (⇓clos 0 (rVar (bnd 0))) (⇓ctor cA) (⇓ctor cA)

-- ... and to `U::B` yields `U::B`, so the test below distinguishes
idAppB : rCall idExpr (rCtor cB) ⇓ rCtor cB
idAppB = ⇓call (⇓clos 0 (rVar (bnd 0))) (⇓ctor cB) (⇓ctor cB)

-- `λf.λx. f x` applied to the identity and then to `U::A`
_ : appExpr ≡ rClos 0 (rClos 1 (rCall (rVar (bnd 0)) (rVar (bnd 1))))
_ = refl

appIdA : rCall (rCall appExpr idExpr) (rCtor cA) ⇓ rCtor cA
appIdA =
  ⇓call (⇓call (⇓clos 0 _) (⇓clos 0 _) (⇓clos 1 _))
        (⇓ctor cA)
        (⇓call (⇓clos 0 (rVar (bnd 0))) (⇓ctor cA) (⇓ctor cA))

-- ==================================================================
-- §3  THE PREDICTION, as text.  `scripts` runs these and compares.
--
--   program            `_⇓_` says   rustc printed   verdict
--   -------            ----------   -------------   -------
--   runnable  idExpr   rCtor cA     U::A            AGREE  (`idAppA`)
--   runnableB idExpr   rCtor cB     U::B            AGREE  (`idAppB`)
--   appExpr at cA      rCtor cA     U::A            AGREE  (`appIdA`)
--                                                   -- only once BOXED;
--                                                   -- the emitted form
--                                                   -- does not compile
--
-- THREE CASES, NO DISAGREEMENT.  `_⇓_` survived contact with `rustc`
-- 1.93.0 on every program that could be made to compile, and the one
-- that could not failed at EXPRESSIBILITY, not at semantics -- the
-- boxed form agrees.  A disagreement would have been a genuine bug in
-- `_⇓_`; there was none.
-- ==================================================================

predictionA : UString
predictionA = "U::A"

predictionB : UString
predictionB = "U::B"

-- the same program at `U::B`, so the observation is not vacuous
runnableB : RExpr → UString
runnableB e =
  "#[derive(Debug)]\nenum U { A, B }\n\nfn main() {\n    let r = ("
  ++s renderExpr e
  ++s ")(U::B);\n    println!(\"{}\", match r { U::A => \"U::A\", U::B => \"U::B\" });\n}\n"

idProgB : UString
idProgB = runnableB idExpr
