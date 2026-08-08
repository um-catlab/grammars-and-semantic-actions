{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  A LINEAR λ-TERM WITH ARITHMETIC, AS AN ASSEMBLY UNIT.

  `Compile/ClosureConv/Emit.agda` at this backend.  The three constants
  it names -- `memBytes`, `stackBase`, `heapBase` -- are that file's and
  are IMPORTED, so the preamble the process gets is the same preamble,
  and `finCode` is the same postlude.  Nothing about emission changed
  when numbers were added; that is the point of `ARM.agda` §A's
  representation decision.

  ------------------------------------------------------------------
  WHAT THE EXIT STATUS MEANS NOW
  ------------------------------------------------------------------

  `finCode` is still

      ldr  x0, [x9]
      and  x0, x0, #255

  -- FIELD 0 OF THE ANSWER RECORD, masked.  `ClosureConv/Emit.agda` §B
  argued at length that this is the best eight-bit observable available
  for a language whose only values are closures, and that it forgets the
  environment.  For an ARITHMETIC answer it forgets nothing: field 0 IS
  the number.  So the exit status of `(λx. x + 1) 41` is 42, and §3
  below pins that against the model before the runner ever assembles it.

  `refWord` is the same word computed on the IR side, so the model and
  the machine are compared as `Maybe ℕ` -- for BOTH kinds of value, a
  closure's word being its block's code address.  That is a strictly
  wider agreement than `ClosureConv/Emit.agda` §3.5's, which had to
  restate the three numbers by hand.

  PHASE.  Phase 1: rendering.
-}
open import Cubical.Foundations.Prelude

module Compile.LinNum.Emit where

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Unit using (tt)
open import Agda.Builtin.String using (String)
import Cubical.Data.Equality as Eq

open import Compile.ArithToARM.Control using (CProg)
open import Compile.ArithToARM.ControlEmit using (unitWith; finCode)

open import Compile.ClosureConv.ARM using (stackBase; heapBase)
open import Compile.ClosureConv.Emit using (memBytes; asmId)

open import Compile.LinNum.ARM
import TheoryGrammar.Instances.LinLam.Syntax as L

-- ==================================================================
-- §1  THE COMPOSITE.
-- ==================================================================

asmC : CProg → String
asmC = unitWith memBytes stackBase heapBase finCode

asmN : NTm [] → String
asmN t = asmC (compileARM t)

unitLen : NTm [] → ℕ
unitLen t = progLen (compileP t)

-- ==================================================================
-- §2  THE WORD THE MODEL SAYS THE MACHINE WILL HOLD.
--
-- A closure's word is its block's CODE ADDRESS -- which is what
-- `ClosureConv/ARM.unAddr` inverts -- and a number's word is itself.
-- So this is total, and `armWord` is comparable to it directly.
-- ==================================================================

wordOfVal : Prog → Val → ℕ
wordOfVal P (num n)    = n
wordOfVal P (clos i _) = addrOf P i

refWordM : Prog → Maybe Val → Maybe ℕ
refWordM P nothing  = nothing
refWordM P (just v) = just (wordOfVal P v)

refWord : NTm [] → Maybe ℕ
refWord t = refWordM (compileP t) (obsN t)

-- ==================================================================
-- §3  THE OUTPUT, PINNED.
-- ==================================================================

-- ------------------------------------------------------------------
-- 3.1  THE TARGET.  `(λx. x + 1) 41`: the model and the machine agree
-- on the word, and the word is 42.
-- ------------------------------------------------------------------

_ : refWord  incApp     Eq.≡ just 42
_ = Eq.refl

_ : armWord 400 incApp  Eq.≡ just 42
_ = Eq.refl

-- ... so the process will exit 42.  `tools/run-arm.sh incApp` is that
-- sentence, checked against a real one.

_ : refWord  sum42      Eq.≡ just 42
_ = Eq.refl

_ : armWord 100 sum42   Eq.≡ just 42
_ = Eq.refl

_ : refWord  addApp     Eq.≡ just 42
_ = Eq.refl

_ : armWord 900 addApp  Eq.≡ just 42
_ = Eq.refl

_ : refWord  applyInc   Eq.≡ just 42
_ = Eq.refl

_ : armWord 900 applyInc Eq.≡ just 42
_ = Eq.refl

_ : refWord  sum143     Eq.≡ just 143
_ = Eq.refl

_ : armWord 900 sum143  Eq.≡ just 143
_ = Eq.refl

-- ------------------------------------------------------------------
-- 3.2  THE SIZES.  `λx. x + 1` applied to a literal is 41 instructions;
-- compare `ClosureConv/Emit.agda` §3.2's 13/36/62/59 for the pure
-- λ-terms.  Arithmetic is CHEAP on this machine: a literal is four
-- instructions and a `+` is eight, against a call's twelve.
-- ------------------------------------------------------------------

_ : unitLen lit41   Eq.≡ 6
_ = Eq.refl

_ : unitLen sum42   Eq.≡ 18
_ = Eq.refl

_ : unitLen incApp  Eq.≡ 41
_ = Eq.refl

-- ------------------------------------------------------------------
-- 3.3  AND THE OLD FRAGMENT EMITS THE SAME TEXT.
--
-- `ClosureConv/Emit.asmId` is pinned character for character in that
-- file; this says the arithmetic backend reproduces it exactly on a
-- term with no arithmetic in it.  Adding a base type perturbed nothing.
-- ------------------------------------------------------------------

_ : asmN (fromTm L.idLin) Eq.≡ asmId
_ = Eq.refl

-- ... and the old exit statuses, recomputed through the new observable
_ : refWord (fromTm L.idLin)   Eq.≡ just 6
_ = Eq.refl

_ : refWord (fromTm L.selfApp) Eq.≡ just 29
_ = Eq.refl

_ : armWord 500 (fromTm L.selfApp) Eq.≡ just 29
_ = Eq.refl
