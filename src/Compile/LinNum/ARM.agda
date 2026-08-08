{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE LINEAR λ-CALCULUS WITH NUMBERS, ON AArch64.

  `Compile/ClosureConv/ARM.agda` with two more clauses in `sizeE` and
  `emitE`.  The activation record, the call sequence, the epilogue, the
  layout and the two register conventions are that file's and are not
  restated -- `loadSlot`, `emitCap`, `callSeq`, `epilogue`, `packIx`,
  `capPos`, `liveCount` are IMPORTED.  What is forked is only what
  mentions `IR`.

  ------------------------------------------------------------------
  §A  THE REPRESENTATION DECISION, WHICH IS THE WHOLE FILE
  ------------------------------------------------------------------

  `ClosureConv/ARM.agda`'s header says

      A `Val` is a heap address throughout; there is no other kind of
      value, which is `IR.agda` §4 read as a representation decision.

  and a number has to fit that.  It does, with NO tag and NO new
  instruction, because of what field 0 of a record is used for:

      CLOSURE at `a`      [a + 0]  the block's CODE ADDRESS
                          [a + 8j] captured value j

      NUMBER  at `a`      [a + 0]  THE NUMBER

  A value is a one-word-headed heap record either way, and every
  consumer already reads field 0: `iapp` does `ldr w9, [w9, #0]` to get
  the code address, and `iadd` does the same load to get the summand.
  So `ilit` is `movI` + a store + a push + a bump, and `iadd` is two
  pops, two loads, one `addR` (which `AArch64.Instr` already had), a
  store, a push and a bump.  Four and eight instructions, and neither
  needs a branch.

  THE EXIT STATUS COMES OUT RIGHT FOR FREE.  `ControlEmit.finCode` is

      ldr  x0, [x9]
      and  x0, x0, #255

  -- field 0 of the answer record, masked.  For a closure that is the
  block's code address, which is what `Compile/ClosureConv/Emit.agda`
  §B is about; for a NUMBER it is the number.  So a program computing
  42 exits 42, with no change to the emitter's postlude at all.

  ------------------------------------------------------------------
  §B  WHERE THE MACHINE AND THE MODEL PART, AND IT IS SAID OUT LOUD
  ------------------------------------------------------------------

  `IR.addV` answers `nothing` when a summand is a closure.  The machine
  cannot: an untagged record is an untagged record, so `iadd` on a
  closure ADDS ITS CODE ADDRESS and carries on.  The two therefore agree
  exactly on programs that do not go wrong, and §9 pins the agreement on
  the terms this development runs rather than claiming it in general.

  That is not a gap that tagging would close honestly -- a tag is a
  runtime type check, and this source has no types.  The right repair is
  a type system for `NTm`, which is a separate piece of work; naming the
  divergence is what keeps it from being invisible.

  PHASE.  Phase 1: this is a compiler.  `emitLit` and `emitAdd` are
  PRIMITIVE and marked.
-}
open import Cubical.Foundations.Prelude

module Compile.LinNum.ARM where

open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.List using (List; []; _∷_; _++_; length)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Data.Unit using (Unit; tt)
import Cubical.Data.Equality as Eq

open import Compile.ArithToARM.AArch64 hiding (Prog)
open import Compile.ArithToARM.Control

-- the machine-level macros, unchanged
open import Compile.ClosureConv.ARM
  using ( off8; fRET; fSAV; fENV; fARG; fTOP
        ; packIx; liveCount; loadSlot; emitCap; callSeq; epilogue
        ; sizeLoad; sizeCap; length-++; loadLen; capLen
        ; stackBase; heapBase )

open import Compile.LinNum.Convert public
import TheoryGrammar.Instances.LinLam.Syntax as L

-- ==================================================================
-- §1  THE CAPTURE, AS FRAME POSITIONS.  `IR.capVals` with `σ` erased;
-- forked only because `Cap`'s home module now has two `capPos`es and
-- this one must agree with THIS file's `capVals`.
-- ==================================================================

capPos : ∀ {sh u} → Cap sh u → List ℕ
capPos (cnil _)                  = []
capPos (cdead c)                 = capPos c
capPos (clive {u₁ = u₁} sp so c) = slotOf 0 u₁ so ∷ capPos c

-- ==================================================================
-- §2  THE TWO NEW MACROS.  PRIMITIVE (phase 1).
-- ==================================================================

-- PRIMITIVE: a LITERAL.  Allocate a one-field record holding `n`, push
-- its address, bump HP.  Four instructions, no branch.
emitLit : ℕ → CProg
emitLit n = base (movI w9 n)
          ∷ base (strO w9 w0 0)
          ∷ base (strPost w0 x20 8)
          ∷ base (addI w0 w0 8)
          ∷ []

-- PRIMITIVE: the PRIMITIVE.  On entry the operand stack holds the left
-- summand (below) and the right one (above); both are addresses.
--
--   0  pop the right operand's address        SP -= 8
--   1  pop the left  operand's address        SP -= 8
--   2  w9  := [left  + 0]      -- §A: field 0 of a number IS the number
--   3  w10 := [right + 0]
--   4  w9  := w9 + w10         -- the one `addR` in the file
--   5  [HP + 0] := w9          -- the answer record
--   6  push HP
--   7  bump HP
--
-- Eight instructions, and the one-slot invariant of `ClosureConv/ARM`'s
-- header is respected: two pops, one push.
emitAdd : CProg
emitAdd = base (ldrPre w10 x20 8)
        ∷ base (ldrPre w9  x20 8)
        ∷ base (ldrO w9  w9  0)
        ∷ base (ldrO w10 w10 0)
        ∷ base (addR w9 w9 w10)
        ∷ base (strO w9 w0 0)
        ∷ base (strPost w0 x20 8)
        ∷ base (addI w0 w0 8)
        ∷ []

-- ==================================================================
-- §3  MEASURING, BEFORE EMITTING.  The three old clauses verbatim, so
-- that on the `fromTm` fragment this file's numbers ARE that file's.
-- ==================================================================

sizeE : ∀ {u} → IR u → ℕ
sizeE (ivar {u} s)  = suc (sizeLoad (slotOf 0 u s))
sizeE (iclos i cap) = 2 + (sizeCap (capPos cap) + 2)
sizeE (iapp _ f a)  = sizeE f + (sizeE a + 12)
sizeE (ilit _ _)    = 4
sizeE (iadd _ a b)  = sizeE a + (sizeE b + 8)

-- ==================================================================
-- §4  THE CODE GENERATOR.
-- ==================================================================

emitE : (am : ℕ → ℕ) (sh : Usage) (pc : ℕ) {u : Usage} → IR u → CProg

emitE am sh pc (ivar {u} s) =
  loadSlot sh (slotOf 0 u s) ++ (base (strPost w9 x20 8) ∷ [])

emitE am sh pc (iclos i cap) =
    base (movI w9 (am i))
  ∷ base (strO w9 w0 0)
  ∷ ( emitCap sh 1 (capPos cap)
      ++ ( base (strPost w0 x20 8)
         ∷ base (addI w0 w0 (off8 (suc (length (capPos cap)))))
         ∷ [] ) )

emitE am sh pc (iapp _ f a) =
    emitE am sh pc f
  ++ ( emitE am sh (sizeE f + pc) a
       ++ callSeq (11 + (sizeE a + (sizeE f + pc))) )

emitE am sh pc (ilit _ n) = emitLit n

-- `pc` is threaded but never read: `emitAdd` contains no address.  That
-- is why `iadd` costs no layout reasoning at all -- compare `iapp`,
-- whose return address is the one position-dependent immediate in the
-- whole backend.
emitE am sh pc (iadd _ a b) =
  emitE am sh pc a ++ (emitE am sh (sizeE a + pc) b ++ emitAdd)

-- ==================================================================
-- §5  ... AND THE SIZE IS THE LENGTH.  The one thing §3 could get
-- wrong, proved away, exactly as in `ClosureConv/ARM.agda` §6.
-- ==================================================================

sizeIsLength : (am : ℕ → ℕ) (sh : Usage) (pc : ℕ) {u : Usage} (e : IR u)
             → length (emitE am sh pc e) Eq.≡ sizeE e
sizeIsLength am sh pc (ivar {u} s) = go (slotOf 0 u s)
  where
  go : (p : ℕ)
     → length (loadSlot sh p ++ (base (strPost w9 x20 8) ∷ [])) Eq.≡ suc (sizeLoad p)
  go zero    = Eq.refl
  go (suc q) = Eq.refl
sizeIsLength am sh pc (iclos i cap) =
  Eq.ap (λ z → 2 + z)
    ( length-++ (emitCap sh 1 (capPos cap))
                ( base (strPost w0 x20 8)
                ∷ base (addI w0 w0 (off8 (suc (length (capPos cap))))) ∷ [] )
      Eq.∙ Eq.ap (λ z → z + 2) (capLen sh 1 (capPos cap)) )
sizeIsLength am sh pc (iapp _ f a) =
  length-++ (emitE am sh pc f)
            ( emitE am sh (sizeE f + pc) a
              ++ callSeq (11 + (sizeE a + (sizeE f + pc))) )
  Eq.∙ ( Eq.ap (λ z → z + length ( emitE am sh (sizeE f + pc) a
                                   ++ callSeq (11 + (sizeE a + (sizeE f + pc)))))
               (sizeIsLength am sh pc f)
         Eq.∙ Eq.ap (λ z → sizeE f + z)
               ( length-++ (emitE am sh (sizeE f + pc) a)
                           (callSeq (11 + (sizeE a + (sizeE f + pc))))
                 Eq.∙ Eq.ap (λ z → z + 12) (sizeIsLength am sh (sizeE f + pc) a) ) )
sizeIsLength am sh pc (ilit _ n) = Eq.refl
sizeIsLength am sh pc (iadd _ a b) =
  length-++ (emitE am sh pc a) (emitE am sh (sizeE a + pc) b ++ emitAdd)
  Eq.∙ ( Eq.ap (λ z → z + length (emitE am sh (sizeE a + pc) b ++ emitAdd))
               (sizeIsLength am sh pc a)
         Eq.∙ Eq.ap (λ z → sizeE a + z)
               ( length-++ (emitE am sh (sizeE a + pc) b) emitAdd
                 Eq.∙ Eq.ap (λ z → z + 8) (sizeIsLength am sh (sizeE a + pc) b) ) )

-- ==================================================================
-- §6  THE LAYOUT.  `ClosureConv/ARM.agda` §7, at this `sizeE`.
-- ==================================================================

blkSize : Blk → ℕ
blkSize (sh , b) = 5 + sizeE b

tblSize : Table → ℕ
tblSize []      = 0
tblSize (B ∷ T) = blkSize B + tblSize T

blkAddr : ℕ → Table → ℕ → ℕ
blkAddr b []      i       = b
blkAddr b (B ∷ T) zero    = b
blkAddr b (B ∷ T) (suc i) = blkAddr (blkSize B + b) T i

emitBlk : (ℕ → ℕ) → ℕ → Blk → CProg
emitBlk am pc (sh , b) = emitE am sh pc b ++ epilogue

emitTbl : (ℕ → ℕ) → ℕ → Table → CProg
emitTbl am pc []      = []
emitTbl am pc (B ∷ T) = emitBlk am pc B ++ emitTbl am (blkSize B + pc) T

mainLen : IR [] → ℕ
mainLen e = 2 + sizeE e

addrOf : Prog → ℕ → ℕ
addrOf P = blkAddr (mainLen (P .snd)) (P .fst)

progLen : Prog → ℕ
progLen P = mainLen (P .snd) + tblSize (P .fst)

compileC : Prog → CProg
compileC P =
  ( emitE (addrOf P) [] 0 (P .snd)
    ++ ( base (ldrPre w9 x20 8) ∷ bra (progLen P) ∷ [] ) )
  ++ emitTbl (addrOf P) (mainLen (P .snd)) (P .fst)

compileARM : NTm [] → CProg
compileARM t = compileC (compileP t)

-- ==================================================================
-- §7  THE INITIAL MACHINE, and running it.  `stackBase`/`heapBase` are
-- `ClosureConv/ARM`'s, imported, so the emitted preamble is the same
-- one and `Compile/ClosureConv/Emit.agda`'s three constants still
-- describe this backend.
-- ==================================================================

initSt : St
initSt = setR w0 heapBase (setR x19 0 (setR x20 stackBase (λ _ → 0)))
       , (λ _ → 0)

initC : Conf
initC = 0 , 0 , initSt

runARM : ℕ → Prog → Maybe Conf
runARM f P = run f (compileC P) initC

-- ==================================================================
-- §8  READING THE ANSWER.
--
-- FIELD 0 OF THE ANSWER RECORD, which is what `finCode` loads, and
-- which §A says is the number when the answer is a number.  This is a
-- narrower observable than `ClosureConv/ARM.answerT`'s decoded `Val` --
-- deliberately: a record carries no tag, so a DECODER would have to
-- guess, and guessing is what §B refuses to do.
-- ==================================================================

wordOf : Maybe Conf → Maybe ℕ
wordOf nothing  = nothing
wordOf (just c) = just (memOf (just c) (regOf (just c) w9))

-- the machine's answer, as a word
armWord : ℕ → NTm [] → Maybe ℕ
armWord f t = wordOf (runARM f (compileP t))

-- What the PROCESS exits with is this word masked to eight bits by
-- `finCode`'s `and x0, x0, #255`.  The masking is left to the runner
-- (`tools/run-arm.sh`) rather than done here: it is a property of the
-- POSTLUDE, not of the machine, and every number in §9 is below 256.

-- ==================================================================
-- §9  IT RUNS, AND IT RUNS NUMBERS.
--
-- Everything below is `Eq.refl`, so a closed linear λ-term with
-- arithmetic really is compiled to real AArch64 and really is executed
-- by `Control.run`.
-- ==================================================================

-- ------------------------------------------------------------------
-- 9.1  A BARE LITERAL.  Four instructions of main, a pop and a halt.
-- ------------------------------------------------------------------

_ : compileARM lit41
  Eq.≡ ( base (movI w9 41)
       ∷ base (strO w9 w0 0)
       ∷ base (strPost w0 x20 8)
       ∷ base (addI w0 w0 8)
       ∷ base (ldrPre w9 x20 8)
       ∷ bra 6
       ∷ [] )
_ = Eq.refl

_ : armWord 100 lit41 Eq.≡ just 41
_ = Eq.refl

-- ------------------------------------------------------------------
-- 9.2  `40 + 2`, ON THE MACHINE.
-- ------------------------------------------------------------------

_ : armWord 100 sum42 Eq.≡ just 42
_ = Eq.refl

-- ------------------------------------------------------------------
-- 9.3  THE TARGET: `(λx. x + 1) 41` ⇓ 42, in AArch64.
--
-- The `42` here came out of a heap record built by `emitAdd`, whose
-- left operand was loaded from the activation record's argument slot
-- by `loadSlot`, inside a block entered by `blr`.  Compare `numN
-- incApp` in `Convert.agda`: same number, different machine.
-- ------------------------------------------------------------------

_ : armWord 400 incApp Eq.≡ just 42
_ = Eq.refl

-- and the model says the same
_ : numN incApp Eq.≡ just 42
_ = Eq.refl

-- ------------------------------------------------------------------
-- 9.4  TWO BINDERS, so the summand comes out of a CLOSURE ENVIRONMENT
-- rather than out of the argument slot -- i.e. `loadSlot`'s two-load
-- branch, the one that is closure conversion at the machine level.
-- ------------------------------------------------------------------

_ : armWord 900 addApp Eq.≡ just 42
_ = Eq.refl

_ : numN addApp Eq.≡ just 42
_ = Eq.refl

-- ------------------------------------------------------------------
-- 9.5  A CALL THROUGH A VARIABLE.
-- ------------------------------------------------------------------

_ : armWord 900 applyInc Eq.≡ just 42
_ = Eq.refl

-- ------------------------------------------------------------------
-- 9.6  AND THE OLD FRAGMENT IS EMITTED IDENTICALLY.
--
-- This is the check that adding a base type did not perturb anything:
-- on a term with no arithmetic in it, this backend's `CProg` is
-- `ClosureConv.ARM.compileARM`'s, on the nose.
-- ------------------------------------------------------------------

open import Compile.ClosureConv.ARM using () renaming (compileARM to compileARM₀)

_ : compileARM (fromTm L.idLin) Eq.≡ compileARM₀ L.idLin
_ = Eq.refl

_ : compileARM (fromTm L.selfApp) Eq.≡ compileARM₀ L.selfApp
_ = Eq.refl
