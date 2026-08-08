{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE BACK END: closure conversion, codegen, emit.

  `Convert.convertT : TmG ⊢ IRG` is already a term.  Everything after it
  is `Tm [] → _`, because a machine has no activation record for a free
  variable (`ARM.initSt` sets `x19 := 0`), and `Front.front` delivers a
  CLOSED term -- `LinIR`'s scope equation is used rather than discarded,
  so there is no `crossClosed` and no `Maybe` between stages.

  Every stage below is therefore `Δ-map`, and each pipeline is one term
  of `strFib`.  `run` appears only in `PipelineTests`.
-}
open import Cubical.Foundations.Prelude

module Compile.ClosureConv.Pipeline where

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Maybe using (Maybe)
open import Agda.Builtin.String using () renaming (String to UString)

open import Chain.Paren.Tokens
open import Chain.Paren.Grammar
open import TheoryGrammar.SemanticAction
open import TheoryGrammar.RulesFib using (module RulesF)

open ActFib strFib using (Δ; Δ-map)
open RulesF strFib using (_∘g_; Result; mapR)

import Chain.Paren.Front as F

open import TheoryGrammar.Instances.LinLam.Syntax using (Tm)

open import Compile.ArithToARM.Control using (CProg; Conf)
open import Compile.ClosureConv.IR      using (Prog; Val; runP)
open import Compile.ClosureConv.Convert using (compileP)
open import Compile.ClosureConv.ARM     using (compileARM; runARM; answerT; progLen)
open import Compile.ClosureConv.Emit    using (asmT; unitLen; exitOf)

-- §1  STAGES 4-6 AS ACTIONS.  Each is a total function on a closed
-- linear term, so each is `Δ-map` and none is a decision: after stage 3
-- the compiler cannot say no.

stage : {X : Type₀} → (Tm [] → X)
      → ⊤G ⊢ Result F.Err (Δ (Tm [])) → ⊤G ⊢ Result F.Err (Δ X)
stage {X = X} f p = mapR F.Err (Δ X) (Δ-map f) ∘g p

-- optimised, and the same without the pass
pipelineIR  pipelineIRRaw  : ⊤G ⊢ Result F.Err (Δ Prog)
pipelineARM pipelineARMRaw : ⊤G ⊢ Result F.Err (Δ CProg)
asm         asmRaw         : ⊤G ⊢ Result F.Err (Δ UString)
asmLen      asmLenRaw      : ⊤G ⊢ Result F.Err (Δ ℕ)

pipelineIR     = stage compileP   F.front
pipelineIRRaw  = stage compileP   F.frontRaw
pipelineARM    = stage compileARM F.front
pipelineARMRaw = stage compileARM F.frontRaw
asm            = stage asmT       F.front
asmRaw         = stage asmT       F.frontRaw
asmLen         = stage unitLen    F.front
asmLenRaw      = stage unitLen    F.frontRaw

-- §2  THE OBSERVATIONS: three readings of one program at three levels,
-- so a disagreement says WHICH level.

answerIR : ℕ → ⊤G ⊢ Result F.Err (Δ (Maybe Val))
answerIR f = stage (λ t → runP f (compileP t)) F.front

answerARM : ℕ → ℕ → ⊤G ⊢ Result F.Err (Δ (Maybe Val))
answerARM f k = stage (answerT f k) F.front

-- the code index in field 0 of the record the machine halted holding
exitStatus exitStatusRaw : ℕ → ⊤G ⊢ Result F.Err (Δ ℕ)
exitStatus    f = stage (λ t → exitOf (runARM f (compileP t))) F.front
exitStatusRaw f = stage (λ t → exitOf (runARM f (compileP t))) F.frontRaw
