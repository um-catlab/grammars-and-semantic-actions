{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  SOURCE TEXT TO AArch64 THAT RUNS, PINNED AT EVERY STAGE.

      program                     parse  type  linear   assembly
      --------------------------------------------------------------
      \x. x                         ok    ok     ok     13 instrs, exit 6
      (\x. x) (\x. x)               ok    ok     ok     13 instrs, exit 6
      \x. x x                       ok    NO     --     --
      \x. \y. x                     ok    NO     --     --
      \x. y                         --    --     --     --   (unbound)

  The third column MOVED.  This chain used to begin at `Instances.Spans`
  with no type stage, so `\x. x x` and `\x. \y. x` came out at
  `linear?`.  `LinTyped`'s context is itself linear, so `closed-infer?`
  refuses them one stage earlier; §4 proves that, at `¬G (Syn [])`.

  Source is parenthesised and annotated because `parenGuarded` needs a
  literal before every recursive occurrence and `closed-infer?` needs
  something to synthesise from -- see `Chain.Paren.Grammar`.
-}
open import Cubical.Foundations.Prelude

module Compile.ClosureConv.PipelineTests where

open import Cubical.Data.Bool using (false)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.String using () renaming (String to UString)

open import Chain.Paren.Tokens
open import Chain.Paren.Grammar
open import TheoryGrammar.SemanticAction
open import TheoryGrammar.RulesFib using (module RulesF)

open ActFib strFib using (Δ; runΔ)
open RulesF strFib using (Result)

open import TheoryGrammar.Instances.LinLam.Syntax using (Tm; idLin; selfApp)
open import Compile.ClosureConv.IR using (Val; clos)

import Compile.ClosureConv.ARM      as A
import Compile.ClosureConv.Emit     as EM
import Compile.ClosureConv.Pipeline as CP
import Chain.Paren.Front            as F
import TheoryGrammar.Instances.LinTyped as LT

-- §1  THE OBSERVATION.  `run` at the token list, and `lexS` is the exit
-- from `Char`.  This is the only place either appears.

obs : {X : Type₀} → (⊤G ⊢ Result F.Err (Δ X)) → UString → Maybe X
obs {X = X} p s = go (lexS s)
  where go : Maybe (List Tok) → Maybe X
        go (just ts) = runΔ X F.Err p ts
        go nothing   = nothing

srcId srcBeta srcDup srcDrop srcFree : UString
srcId   = "((\\x. x) : (o -o o))"
srcBeta = "(((\\x. x) : ((o -o o) -o (o -o o))) (\\y. y))"
srcDup  = "((\\x. (x x)) : ((o -o o) -o o))"
srcDrop = "((\\x. \\y. x) : (o -o (o -o o)))"
srcFree = "(\\x. y)"

-- §2  `\x. x`, ALL THE WAY TO THE ASSEMBLER.

_ : obs CP.asmLen srcId ≡ just 13
_ = refl

_ : obs (CP.answerARM 500 8) srcId ≡ just (just (clos 0 []))
_ = refl

_ : obs (CP.answerIR 20) srcId ≡ just (just (clos 0 []))
_ = refl

-- `Emit.agda` §3.1 pins `asmId` as 1715 characters; this says the
-- PARSER's output reaches exactly that text.
_ : obs CP.asm srcId ≡ just EM.asmId
_ = refl

-- assembled with clang and executed on Apple silicon, this exits 6
_ : obs (CP.exitStatus 500) srcId ≡ just 6
_ = refl

-- §3  A β-REDEX, AND THE OPTIMISER MEASURED IN INSTRUCTIONS.
--
-- Unoptimised: three blocks, 36 instructions, exit 29.  Optimised: β
-- fires and the unit is `\x.x`'s, to the character.  Neither the answer
-- nor the exit status is invariant under β -- both are intensional, and
-- `Correct.agda` §2 is the sharp form of that.  What IS invariant is
-- that both run and both halt.

_ : obs CP.asmLenRaw srcBeta ≡ just 36
_ = refl

_ : obs (CP.exitStatusRaw 500) srcBeta ≡ just 29
_ = refl

_ : obs CP.asmLen srcBeta ≡ just 13
_ = refl

_ : obs CP.asm srcBeta ≡ just EM.asmId
_ = refl

_ : obs (CP.exitStatus 500) srcBeta ≡ just 6
_ = refl

_ : EM.unitLen selfApp ≡ 36
_ = refl

_ : EM.exitOf A.selfRun ≡ 29
_ = refl

-- §4  REJECTED, AND THE REJECTION IS A THEOREM.
--
-- `≡ nothing` says the pipeline returned no, which is weaker than what
-- a decision proves.  `Front.noType` is the generic upgrade
-- (`SemanticAction.refute`): it takes the `refl` and hands back the
-- error grammar's content.  These were `LinLam.PipelineTests`' `no-dup`
-- / `no-drop` at `¬G Lin`; they are at `¬G (Syn [])` now.

_ : obs CP.asm srcDup ≡ nothing
_ = refl

_ : obs CP.asm srcDrop ≡ nothing
_ = refl

-- the two offending terms, as `LinTyped.Raw`
dupRaw dropRaw : LT.Raw
dupRaw  = LT.ann (LT.lam (LT.app (LT.var 0) (LT.var 0)))
                 ((LT.base LT.⊸ᵗ LT.base) LT.⊸ᵗ LT.base)
dropRaw = LT.ann (LT.lam (LT.lam (LT.var 1)))
                 (LT.base LT.⊸ᵗ (LT.base LT.⊸ᵗ LT.base))

no-dup : (LT.¬G (LT.Syn [])) dupRaw
no-dup = F.noType dupRaw refl

no-drop : (LT.¬G (LT.Syn [])) dropRaw
no-drop = F.noType dropRaw refl

-- §5  REJECTED AT RESOLUTION, and this one is NOT a refutation.
--
-- `\x. y` is open.  The span chain refused it with `¬G (Scoped [])`; here
-- resolution is a `SynAlg` over the constant family `Env → ScopeRes`, so
-- its failure is the CONSTRUCTOR `unbound n` -- it names the variable,
-- which is the better diagnostic, and it is not a refutation.  That is
-- the cost a constant carrier exacts, recorded rather than papered over.

_ : obs CP.asm srcFree ≡ nothing
_ = refl
