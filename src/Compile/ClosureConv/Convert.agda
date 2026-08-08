{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  CLOSURE CONVERSION, AS AN ALGEBRA.

  ------------------------------------------------------------------
  1.  THE PASS IS A TERM OF THE CALCULUS
  ------------------------------------------------------------------

  `TheoryGrammar/Instances/LinLam/Opt.agda` does the one structural
  recursion on `Tm` that this development is allowed, in `foldTm`, and
  everything downstream is an ALGEBRA for

      StepG A = SoloG ⊕ ((A ⊛ A) ⊕ BodyOf A)

  whose three summands are the three typing rules.  Closure conversion
  is such an algebra and nothing more:

      convVar : SoloG          ⊢ ConvG        a slot read
      convApp : (ConvG ⊛ ConvG)⊢ ConvG        a call
      convLam : BodyOf ConvG   ⊢ ConvG        a BLOCK, plus a closure

      convT   = foldTm ConvG (⊕-E convVar (⊕-E convApp convLam))

  Read `convLam`'s type: the binder's premise sits at the REINDEXED
  motive `BodyOf ConvG` -- `Opt.agda`'s "abstraction is reindexing along
  weakening" -- and the conclusion sits at `ConvG`.  That step, from a
  reindexed premise to an unreindexed conclusion, IS closure
  conversion: what crosses it is the block (which keeps the extended
  scope, as its shape) and the capture (which pays for the crossing).

  The corollary is the theorem the index buys:

      convertT : TmG ⊢ IRG

  -- conversion preserves the usage on the nose, so it cannot invent,
  drop or duplicate a variable.  In an unindexed development "closure
  conversion captures exactly the free variables" is a lemma with a
  proof; here it is the type, and `Opt.agda`'s `noSelfSplit` is the
  sharp form of the "duplicate" half.

  ------------------------------------------------------------------
  2.  THE STATE, AND WHY IT IS A NUMBER
  ------------------------------------------------------------------

      ConvG u = ℕ → IR u × Table

  The `ℕ` is the first free block index; the `Table` returned is the
  blocks this subterm allocated, in order, the head being index `n`.
  So `convApp` has to offset the right premise by `length` of the left
  premise's table -- the ONE place the pass does arithmetic, and the
  reason the block numbering is a global property of the program rather
  than a local one.  `Correct.agda`'s refutation is that observation
  turned into a counterexample.

  This is the same shape as `Compile/LinToRust/Codegen.agda`'s depth
  parameter, with one difference that matters: a depth is determined by
  where a binder SITS, an index by how many binders came BEFORE it.
  Neither is stable under evaluation, and the second fails for a reason
  no renaming can absorb -- see `Correct.agda` §2.

  ------------------------------------------------------------------
  3.  THE SHAPE OF A BLOCK IS THE USAGE AT ITS λ
  ------------------------------------------------------------------

  `convLam u B n` emits the block `(u , body)`.  Taking the shape to be
  `u` itself -- rather than a compacted vector of the live slots -- is
  what makes the capture the IDENTITY capture `idCap u`, and hence what
  makes

      spread u (capVals σ (idCap u))   agree with   σ

  on every live position.  A compacted layout would be smaller and
  would put a renaming between the two sides of every proof; this one
  puts none, which is the same trade `Compile/Relational/Base.agda`
  makes when it gives `rapp` the SAME assignment on both premises.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 2 for the pass itself: §2 is three algebra clauses and a
  `foldTm`, with no match on `Tm` anywhere.  The clauses' BODIES are
  semantic actions at the constant part of the motive (`ℕ`, `Table`) --
  the `Quicksort.qalg` licence, and the same one `Size.agda`'s
  `sizeAppA` uses.  Phase 1 is `IR.agda`.
-}
open import Cubical.Foundations.Prelude

module Compile.ClosureConv.Convert where

open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.List using (List; []; _∷_; _++_; length)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib

open import TheoryGrammar.Instances.LinLam.Opt public
open import Compile.ClosureConv.IR public

-- ==================================================================
-- §1  THE MOTIVE.
--
-- `IRG` is the IR as a grammar over usages -- the codomain of the pass.
-- `ConvG` is that with the block counter threaded; the counter and the
-- table are CONSTANT in the index, so they are the semantic-action part
-- of the motive and the `IR u` is the part `⊢` pins.
-- ==================================================================

IRG : Ctx
IRG = IR

ConvG : Ctx
ConvG u = ℕ → IR u × Table

-- ==================================================================
-- §2  THE THREE CLAUSES.
-- ==================================================================

-- a variable becomes a frame read, at the same slot.  No block, no
-- capture, and the counter is untouched.
convVar : SoloG ⊢ ConvG
convVar u s n = ivar s , []

-- a call becomes a call.  The splitting is carried over VERBATIM --
-- `iapp` wants exactly the `Use⊎ u₁ u₂ u` that `tapp` had -- so this
-- clause is where "linearity survives the pass" is discharged, and it
-- is discharged by there being nothing to do.
--
-- The one piece of arithmetic in the file: the right premise's blocks
-- start after the left premise's.
convApp : (ConvG ⊛ ConvG) ⊢ ConvG
convApp = ⊛-E' ConvG ConvG λ u u₁ u₂ sp F A n →
  let rf = F n
      ra = A (n + length (rf .snd))
  in iapp sp (rf .fst) (ra .fst) , (rf .snd ++ ra .snd)

-- THE CLAUSE THAT IS THE PASS.  The premise is at `BodyOf ConvG`, i.e.
-- at the EXTENDED usage `true ∷ u`; the conclusion is at `u`.  The body
-- is not returned -- it is filed in the table, at index `n`, keeping
-- the extended scope as the block's shape -- and what is returned is a
-- closure: the index, and the capture of everything live in `u`.
--
-- After this clause no constructor of the result binds anything.
convLam : BodyOf ConvG ⊢ ConvG
convLam u B n =
  let r = B (suc n)
  in iclos n (idCap u) , ((u , r .fst) ∷ r .snd)

convAlg : StepG ConvG ⊢ ConvG
convAlg = ⊕-E convVar (⊕-E convApp convLam)

-- THE PASS.  `foldTm` is `Opt.agda`'s primitive recursion, used and not
-- repeated; there is no match on `Tm` in this file.
convT : TmG ⊢ ConvG
convT = foldTm ConvG convAlg

-- ==================================================================
-- §3  THE COMPILER.
-- ==================================================================

-- PRIMITIVE (phase 1): the ONE recursion over `Tm` in this pass, exactly
-- as `LinToRust/Codegen.compileE` is in that one.  Marked here so the
-- four backends carry the same marking.
convert : ∀ {u} → Tm u → IR u
convert {u} t = convT u t 0 .fst

tableOf : ∀ {u} → Tm u → Table
tableOf {u} t = convT u t 0 .snd

-- THE THEOREM THE INDEX BUYS.  A term of the calculus: the usage is
-- preserved, so the conversion is linear in exactly the source's
-- variables.  In an unindexed setting this is the lemma "the capture
-- set is the free-variable set", proved by induction.
--
-- NOTE THE CONTRAST WITH THE OTHER BACKENDS, because it is a difference
-- of PRESENTATION and not of strength.  `LinToRust`, `LinToC` and
-- `LinToISA` emit an UNINDEXED target (`RExpr`, C, ISA), so their
-- linearity guarantee has to be carried extrinsically, as a payload in
-- `Obj = ⊕ᴰ RExpr Scoped` with `usesCompile` to build it.  Here the IR
-- is INTRINSICALLY usage-indexed, so `⊢` alone already says it and no
-- payload is needed.  Intrinsic where the target admits it, extrinsic
-- where it does not; `convertT` is not the weaker of the two.
convertT : TmG ⊢ IRG
convertT u t = convert t

compileP : Tm [] → Prog
compileP t = tableOf t , convert t

-- ==================================================================
-- §4  IT COMPUTES.
--
-- Everything below is `Eq.refl`, so the pass really reduces on closed
-- terms and the emitted code really runs on the machine of `IR.agda`.
-- ==================================================================

-- ------------------------------------------------------------------
-- 4.1  `λx. x`.  One block, shape `[]` (nothing to capture), body =
-- the argument; and a closure naming it with an EMPTY capture.
-- ------------------------------------------------------------------

_ : convert idLin Eq.≡ iclos 0 (cnil tt)
_ = Eq.refl

_ : tableOf idLin Eq.≡ (([] , ivar tt) ∷ [])
_ = Eq.refl

_ : runP 20 (compileP idLin) Eq.≡ just (clos 0 [])
_ = Eq.refl

-- ------------------------------------------------------------------
-- 4.2  `(λx.x) (λx.x)`.  TWO blocks, because the two λs are two
-- distinct pieces of code as far as the pass is concerned, and the
-- answer is the SECOND one -- the argument, returned by the identity.
-- ------------------------------------------------------------------

_ : convert selfApp Eq.≡ iapp unil (iclos 0 (cnil tt)) (iclos 1 (cnil tt))
_ = Eq.refl

_ : runP 20 (compileP selfApp) Eq.≡ just (clos 1 [])
_ = Eq.refl

-- ------------------------------------------------------------------
-- 4.3  `λf. λx. f x` -- the first term with a NON-EMPTY capture.
--
-- The inner λ sits at usage `true ∷ []` (`f` is live), so its block
-- has shape `true ∷ []` and the closure the outer block returns
-- captures slot 0.  This is the whole point of the pass: the inner
-- code is closed, and what was a free variable is now an environment
-- entry.
-- ------------------------------------------------------------------

appLin : Tm []
appLin = tlam (tlam (tapp (uright (uleft unil)) (tvar tt) (tvar tt)))

_ : convert appLin Eq.≡ iclos 0 (cnil tt)
_ = Eq.refl

_ : tableOf appLin
  Eq.≡ ( ([] , iclos 1 (idCap (true ∷ [])))
       ∷ ((true ∷ []) , iapp (uright (uleft unil)) (ivar tt) (ivar tt))
       ∷ [] )
_ = Eq.refl

-- the environment really is one slot wide, and it is slot 0's value
_ : capVals (extF (clos 5 []) emptyF) (idCap (true ∷ [])) Eq.≡ (clos 5 [] ∷ [])
_ = Eq.refl

-- ------------------------------------------------------------------
-- 4.4  `(λf. λx. f x) (λy. y)` -- three blocks, and the answer is a
-- closure WITH an environment.  Compare `Compile/Relational` §7: this
-- is the same witness, and it is about to be the counterexample again.
-- ------------------------------------------------------------------

bigT : Tm []
bigT = tapp unil appLin idLin

_ : convert bigT Eq.≡ iapp unil (iclos 0 (cnil tt)) (iclos 2 (cnil tt))
_ = Eq.refl

_ : runP 20 (compileP bigT) Eq.≡ just (clos 1 (clos 2 [] ∷ []))
_ = Eq.refl

-- ------------------------------------------------------------------
-- 4.5  `(λf. f (λz.z)) (λx.x)` -- `Normalise.agda`'s separating term,
-- whose contraction CREATES a redex.  The machine has no trouble with
-- it, because it never rewrites anything.
-- ------------------------------------------------------------------

Kterm : Tm []
Kterm = tlam (tapp (uleft unil) (tvar tt) idLin0)

applyK : Tm []
applyK = tapp unil Kterm idLin

_ : runP 40 (compileP applyK) Eq.≡ just (clos 1 [])
_ = Eq.refl

-- ------------------------------------------------------------------
-- 4.6  ... and the derivations, extracted from those computations by
-- `IR.evalSound`.  These are what `Correct.agda`'s square consumes.
-- ------------------------------------------------------------------

bigDeriv : Ev (tableOf bigT) emptyF (convert bigT) (clos 1 (clos 2 [] ∷ []))
bigDeriv = evalSound 20 (tableOf bigT) emptyF (convert bigT)
                     (clos 1 (clos 2 [] ∷ [])) Eq.refl

-- ==================================================================
-- §5  WHAT IS NOT PROVED HERE.
--
-- WELL-FORMEDNESS OF THE TABLE, in general.  "Every `iclos i` the pass
-- emits has a block at `i`" is true, and the two lemmas it needs are in
-- `IR.agda` (`at-++ˡ`, `at-++ʳ`); the induction also needs
-- associativity of `_++_` and `length (T₁ ++ T₂) = length T₁ + length
-- T₂`, transported through the offset in `convApp`.  That is
-- bookkeeping about the numbering scheme and not about closure
-- conversion, so it is left out rather than half-done; at the concrete
-- programs of §4 the witnesses are `ahere` / `athere ahere` and appear
-- in `Correct.agda` where they are used.
-- ==================================================================
