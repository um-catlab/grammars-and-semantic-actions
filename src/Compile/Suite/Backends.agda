{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE BACKENDS, AS DATA.

  Three honest ones.  Each is a `Compile.Suite.Backend.Backend`, i.e. a
  compiler into its own target, a way to run that target, and a decoding
  of the answer into the common observable.  Nothing here is new
  compilation: every `compile` and every `run` field is a function that
  already existed and was already proved about.  What is new is that they
  are now VALUES, so a suite can be handed a list of them.

      irB     Compile.ClosureConv.Convert   closure conversion, run by the
                                            IR's own interpreter `runP`
      armB    Compile.ClosureConv.ARM       ... the same IR, emitted as
                                            real AArch64 and EXECUTED by
                                            `Control.run`, the answer read
                                            back out of the heap
      rustB   Compile.LinToRust.Codegen     the pure functional Rust
                                            backend, run by `evalRust`

  `irB` and `armB` share a `compile` and differ only in `run`, which is
  the point: `ARM.agda` §11 pins `answerT ≡ runP` term by term, so the
  suite's agreement on those two is that theorem, recomputed by the
  harness instead of by hand.  `rustB` shares nothing with either.

  ------------------------------------------------------------------
  THE DECODERS
  ------------------------------------------------------------------

  Both are two lines, and `Backend.agda`'s header is the argument that
  they cannot honestly be longer: a closure-converted answer carries the
  free variables its block was compiled with, a substituting answer has
  none left and carries its own nested λs instead, and `Correct.RelE`'s
  `rcap` is the constructor saying those two facts agree only up to the
  realisation relation.  So the block index goes (it names a position in
  one table), the capture list goes (it is representation-dependent), and
  what is left is `vfun`.

  `vstuck` is not decoration.  `Codegen.agda` records when a Rust answer
  is not a closure -- an OPEN term has a free `yp` and `evalRust` sticks
  -- and §6 of the tests is a MISCOMPILED binder producing the same
  thing, which is how the harness catches it.

  ------------------------------------------------------------------
  BUDGETS
  ------------------------------------------------------------------

  `nothing` means "no answer within the budget", uniformly.  The numbers
  are `ARM.agda` §11's and `Codegen.agda`'s own: 500 machine steps, depth
  8 for the heap decoding, 40 for the two interpreters.  §11.5 there is
  the check that a starved run really does answer `nothing` rather than
  decoding a half-run state, so the uniform reading is sound.

  PHASE: phase 1.  A backend is a metalanguage function; that is what
  makes it a backend.  The decoders recurse on a target value.
-}
open import Cubical.Foundations.Prelude

module Compile.Suite.Backends where

open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.List using (List; []; _∷_; _++_; map; length)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Unit using (Unit; tt)

open import TheoryGrammar.Instances.LinLam.Syntax
open import Compile.Suite.Backend

import Compile.ClosureConv.Convert as CC
import Compile.ClosureConv.ARM     as AM
import Compile.LinToRust.Codegen   as RS

-- ==================================================================
-- §1  DECODING THE CLOSURE-CONVERTED ANSWER.
--
-- `IR.Val` is `clos i vs` and nothing else (`junk = clos 0 []`), so on
-- this side an answer is always a function and the whole decoding is the
-- `Maybe`.  That the OTHER side can also say `vstuck` is what stops the
-- observable from being `Maybe Unit`.
-- ==================================================================

decIR : CC.Val → Val
decIR (CC.clos i vs) = vfun

decIRM : Maybe CC.Val → Obs
decIRM nothing  = nothing
decIRM (just v) = just (decIR v)

-- ==================================================================
-- §2  DECODING THE RUST ANSWER.
--
-- `IsVal` (Syntax.agda) has one constructor, `valClos`, so "is a
-- function" is "is an `rClos`" and everything else is an answer the
-- evaluator handed back without being able to call it.
-- ==================================================================

decR : RS.RExpr → Val
decR (RS.rClos n b)     = vfun
decR (RS.rVar _)        = vstuck
decR (RS.rCall _ _)     = vstuck
decR (RS.rCtor _)       = vstuck
decR (RS.rMatch _ _ _)  = vstuck
decR (RS.rLet _ _ _)    = vstuck

decRM : Maybe RS.RExpr → Obs
decRM nothing  = nothing
decRM (just e) = just (decR e)

-- ==================================================================
-- §3  THE BACKENDS.
-- ==================================================================

-- the IR's own interpreter -- the reference semantics of the target
irB : Backend
irB .name    = "ir"
irB .Target  = CC.Prog
irB .Answer  = Maybe CC.Val
irB .compile = CC.compileP
irB .run     = CC.runP 40
irB .decode  = decIRM

-- ... and the SAME program, emitted as AArch64 and executed.  `run`
-- folds emission, execution and heap decoding together because the last
-- of the three needs the program's own table -- `ARM.decodeV` is
-- `Correct.RelV` as a function, at the one program the answer means
-- anything in.
armB : Backend
armB .name    = "arm64"
armB .Target  = CC.Prog
armB .Answer  = Maybe CC.Val
armB .compile = CC.compileP
armB .run     = AM.answer 500 8
armB .decode  = decIRM

rustB : Backend
rustB .name    = "rust"
rustB .Target  = RS.RExpr
rustB .Answer  = Maybe RS.RExpr
rustB .compile = RS.compileRust
rustB .run     = λ e → RS.valOf (RS.evalRust 40 e)
rustB .decode  = decRM

-- ==================================================================
-- §4  WHAT EACH ONE SAYS, term by term -- AND WHAT THE OBSERVABLE
-- FORGETS.
--
-- 4a is the common observable, i.e. the rows the suite assembles.  4b is
-- the two NATIVE answers at `bigT`, side by side, which is the evidence
-- for `Backend.agda`'s header: the closure converter returns a closure
-- with a ONE-ENTRY environment, the Rust backend returns a closure whose
-- body has that entry SUBSTITUTED IN, and no structural reading of the
-- two makes them equal.  `Correct.capstone` is the statement that does
-- relate them, and it is a `RelV` and not an `≡`.
-- ==================================================================

_ : Backend.obs irB   idLin ≡ just vfun
_ = refl

_ : Backend.obs armB  idLin ≡ just vfun
_ = refl

_ : Backend.obs rustB idLin ≡ just vfun
_ = refl

_ : Backend.obs irB   CC.selfApp ≡ just vfun
_ = refl

_ : Backend.obs armB  CC.selfApp ≡ just vfun
_ = refl

_ : Backend.obs rustB CC.selfApp ≡ just vfun
_ = refl

_ : Backend.obs irB   CC.bigT ≡ just vfun
_ = refl

_ : Backend.obs armB  CC.bigT ≡ just vfun
_ = refl

_ : Backend.obs rustB CC.bigT ≡ just vfun
_ = refl

_ : Backend.obs irB   CC.applyK ≡ just vfun
_ = refl

_ : Backend.obs armB  CC.applyK ≡ just vfun
_ = refl

_ : Backend.obs rustB CC.applyK ≡ just vfun
_ = refl

-- ------------------------------------------------------------------
-- 4b  THE SAME TERM, IN THE TWO TARGETS' OWN VOCABULARY.
--
-- `clos 1 (clos 2 [] ∷ [])`  -- block 1, environment holding block 2's
--                               closure
-- `rClos 1 (rCall (rClos 0 (rVar (bnd 0))) (rVar (bnd 1)))`
--                            -- the same function, with that environment
--                               entry substituted into the body
--
-- One capture against none; a two-node value against a four-node one.
-- This is why §1/§2 stop at `vfun`.
-- ------------------------------------------------------------------

_ : CC.runP 40 (CC.compileP CC.bigT) ≡ just (CC.clos 1 (CC.clos 2 [] ∷ []))
_ = refl

_ : RS.valOf (RS.evalRust 40 (RS.compileRust CC.bigT))
  ≡ just (RS.rClos 1 (RS.rCall (RS.rClos 0 (RS.rVar (RS.bnd 0)))
                               (RS.rVar (RS.bnd 1))))
_ = refl

-- ... and a genuinely STUCK answer, which is what makes `vstuck`
-- reachable: an open term compiles to Rust with a free `yp`.
_ : decR (RS.rVar (RS.fre 0)) ≡ vstuck
_ = refl
