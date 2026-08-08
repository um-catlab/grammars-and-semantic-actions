{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  A LINEAR λ-TERM, AS AN ASSEMBLY UNIT THAT CLANG ACCEPTS.

  `ClosureConv.ARM` takes a `Tm []` to a `CProg` and RUNS it on
  `Control.run`; `ArithToARM.ControlEmit` takes a `CProg` to AArch64
  text.  This file is the composite, at the three constants that make
  the text a faithful rendering of `ARM.initSt`, and §3 pins the output
  by `refl`.

  ------------------------------------------------------------------
  §A  THE THREE CONSTANTS, AND WHY THEY ARE THE ONLY PARAMETERS
  ------------------------------------------------------------------

  `ARM.initSt` is three register writes over the constant-zero memory:

      w0  := heapBase  = 512      x19 := 0      x20 := stackBase = 64

  `ControlEmit.preamble bytes sOff hOff` realises exactly that, with
  the model's address `a` rendered as `membase + a`.  So the only thing
  this file supplies beyond `ARM.stackBase` and `ARM.heapBase` is
  `memBytes` -- HOW MUCH of the model's infinite `Mem` the process
  actually gets.

  `memBytes` is a HYPOTHESIS, not a theorem, and it is the one place
  where the emitted program can differ from the model: the model's
  memory is infinite, so a term whose heap outgrows `memBytes` runs on
  the model and corrupts its own stack frame on the machine.  Naming
  the number here rather than burying it in the preamble is what makes
  that checkable -- §3.4 records the actual high-water mark of each
  witness (`regOf bigRun w0 ≡ 544`) beside the bound.

  ------------------------------------------------------------------
  §B  WHAT THE EXIT STATUS MEANS
  ------------------------------------------------------------------

  The machine halts holding a heap ADDRESS -- `IR.agda` §4's "a value
  is a closure and nothing else", read at the machine level.  An
  address is not an observable: it depends on `heapBase`, and a process
  exit status is eight bits wide.

  So the observable emitted is `finCode`: THE CODE INDEX STORED IN THE
  ANSWER RECORD'S FIELD 0 -- the instruction the answer closure would
  jump to if it were called.  Three reasons it is the right one:

    * it is already pinned on the model side, in `ARM.agda` §11, as
      `memOf idRun 512 ≡ 6`, `memOf selfRun 520 ≡ 29`,
      `memOf bigRun 528 ≡ 33`.  So the process's exit status can be
      compared against a number this development already proved;

    * `ARM.unAddr` maps it to the BLOCK INDEX, which is the first
      component of `ARM.answerT`'s `clos i vs` -- so it determines the
      answer's head and agrees with `IR.runP` through §11's `Eq.refl`s;

    * it does NOT determine the answer's ENVIRONMENT, and that is the
      honest limit of an eight-bit channel.  `answerT 500 8 bigT` is
      `just (clos 1 (clos 2 [] ∷ []))`; the exit status sees `clos 1`
      and not the `clos 2` inside it.  A wider channel (printing the
      record) would see it; this one does not, and saying so is the
      point of §3.5.
-}
open import Cubical.Foundations.Prelude

module Compile.ClosureConv.Emit where

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.String using (String)
import Cubical.Data.Equality as Eq

open import Compile.ArithToARM.AArch64 using (Reg; w0; w9; w10; x19; x20)
open import Compile.ArithToARM.Control using (CProg; Conf; memOf; regOf; pcOf)
open import Compile.ArithToARM.ControlEmit
open import Compile.ClosureConv.Convert
  using (Tm; idLin; selfApp; bigT; applyK; compileP)
open import Compile.ClosureConv.IR using (Val; clos)
open import Compile.ClosureConv.ARM

-- ==================================================================
-- §1  THE COMPOSITE.
-- ==================================================================

-- HOW MUCH MEMORY THE PROCESS GETS.  See §A: a hypothesis, and the one
-- place the process can diverge from the model.
memBytes : ℕ
memBytes = 2048

-- a control program, as an assembly unit
asmC : CProg → String
asmC = unitWith memBytes stackBase heapBase finCode

-- A CLOSED LINEAR λ-TERM, AS AN ASSEMBLY UNIT.  Everything to the left
-- of `asmC` is `ARM.compileARM`, which is `Convert.compileP` followed
-- by `ARM.compileC`; nothing here is new compilation.
asmT : Tm [] → String
asmT t = asmC (compileARM t)

-- ==================================================================
-- §2  THE SIZE OF THE UNIT, structurally.
--
-- `ARM.sizeE`'s discipline, one level up: the number of instructions
-- is available WITHOUT emitting, so a test can check that a program
-- fits without measuring the string.  `progLen` is `ARM.progLen` and
-- §6 of that file proves it is the length of the emitted `CProg`.
-- ==================================================================

unitLen : Tm [] → ℕ
unitLen t = progLen (compileP t)

-- ==================================================================
-- §3  THE OUTPUT, PINNED.
-- ==================================================================

-- ------------------------------------------------------------------
-- 3.1  `λx. x`: THIRTEEN instructions, and small enough to read.
--
-- Read it against `ARM.agda` §11.1, which pins the same program as a
-- `CProg`: `.L0`-`.L3` build the closure record, `.L4` pops the answer
-- and `.L5` branches to `.L13` -- one past the end, which is the halt.
-- `.L6`-`.L7` are block 0's body and `.L8`-`.L12` its epilogue, never
-- entered here because the identity is never applied.
-- ------------------------------------------------------------------

asmId : String
asmId = asmT idLin

-- THE ASSEMBLY, IN FULL.  This exact text was written to a file,
-- assembled with clang on Apple silicon and executed; see §3.5 for what
-- the exit status was and what it means.
_ : asmId
  ≡ "        .section __TEXT,__text\n        .globl _main\n        .p2align 2\n_main:\n        stp     x29, x30, [sp, #-16]!\n        stp     x19, x20, [sp, #-16]!\n        stp     x21, x22, [sp, #-16]!\n        sub     sp, sp, #2048\n        mov     x19, sp\n        mov     x21, #0\n.Lzloop:\n        str     xzr, [x19, x21]\n        add     x21, x21, #8\n        cmp     x21, #2048\n        b.lo    .Lzloop\n        add     x20, x19, #64\n        add     x0, x19, #512\n.L0:\n        mov     x9, #6\n.L1:\n        str     x9, [x0, #0]\n.L2:\n        str     x0, [x20], #8\n.L3:\n        add     x0, x0, #8\n.L4:\n        ldr     x9, [x20, #-8]!\n.L5:\n        b       .L13\n.L6:\n        ldr     x9, [x19, #24]\n.L7:\n        str     x9, [x20], #8\n.L8:\n        ldr     x9, [x19, #32]\n.L9:\n        ldr     x10, [x19, #0]\n.L10:\n        mov     x20, x19\n.L11:\n        ldr     x19, [x19, #8]\n.L12:\n        adr     x21, .Lcodetab\n        ldr     x22, [x21, x10, lsl #3]\n        add     x21, x21, x22\n        blr     x21\n.L13:\n        ldr     x0, [x9]\n        and     x0, x0, #255\n        add     sp, sp, #2048\n        ldp     x21, x22, [sp], #16\n        ldp     x19, x20, [sp], #16\n        ldp     x29, x30, [sp], #16\n        ret\n        .p2align 3\n.Lcodetab:\n        .quad   .L0-.Lcodetab\n        .quad   .L1-.Lcodetab\n        .quad   .L2-.Lcodetab\n        .quad   .L3-.Lcodetab\n        .quad   .L4-.Lcodetab\n        .quad   .L5-.Lcodetab\n        .quad   .L6-.Lcodetab\n        .quad   .L7-.Lcodetab\n        .quad   .L8-.Lcodetab\n        .quad   .L9-.Lcodetab\n        .quad   .L10-.Lcodetab\n        .quad   .L11-.Lcodetab\n        .quad   .L12-.Lcodetab\n        .quad   .L13-.Lcodetab\n"
_ = refl

-- ------------------------------------------------------------------
-- 3.2  THE OTHER THREE UNITS ARE TOO BIG TO PRINT, so what is pinned
-- is their SIZE -- which is `ARM.progLen`, hence the label the halt
-- branches to, hence the number of `.quad`s minus one.  Compare
-- `ARM.agda` §11's `pcOf` lines: a halted machine's counter IS the
-- program length, so these four numbers are that file's, reread.
-- ------------------------------------------------------------------

_ : unitLen idLin   ≡ 13
_ = refl

_ : unitLen selfApp ≡ 36
_ = refl

_ : unitLen bigT    ≡ 62
_ = refl

_ : unitLen applyK  ≡ 59
_ = refl

-- ------------------------------------------------------------------
-- 3.3  ... AND THE FOUR UNITS ARE FOUR DIFFERENT TEXTS.  Worth saying
-- because `Showcase.agda` §7 is about the opposite: the USAGE-directed
-- backends send `idLin` and `selfApp` to the same empty program, and
-- no theorem about them can see the difference.  This backend is
-- term-directed all the way to the assembler, and the sizes above are
-- the cheapest possible witness of it.
-- ------------------------------------------------------------------

-- ------------------------------------------------------------------
-- 3.4  THE HEAP HIGH-WATER MARKS, against `memBytes`.
--
-- `regOf _ w0` is the bump allocator after the program halted, so it
-- is the highest address the run touched.  All three are far below
-- `memBytes`, which is what §A asks to be checked rather than assumed.
-- ------------------------------------------------------------------

_ : regOf idRun  w0 ≡ 520
_ = refl

_ : regOf bigRun w0 ≡ 544
_ = refl

-- ------------------------------------------------------------------
-- 3.5  THE PREDICTED EXIT STATUS, from the model.
--
-- `finCode` emits `ldr x0, [x9]`, so the process exits with
-- `memOf run (regOf run w9)` masked to eight bits.  These are the
-- numbers `ARM.agda` §11 already proved, restated as the prediction
-- the executable is checked against.
--
-- AND MEASURED.  Each unit below was written to a `.s` file, assembled
-- with `clang` and executed on Apple silicon.  The observed exit
-- statuses were
--
--     λx. x                          6
--     (λx.x) (λx.x)                 29
--     (λf. λx. f x) (λy. y)         33
--     (λf. f (λz.z)) (λx.x)         45
--
-- -- four numbers, four different programs, and each one is the `refl`
-- immediately below it.  Compare `Chain.Run`, whose exit status is the
-- TOKEN COUNT because its backend is usage-directed and cannot see the
-- term; and compare `AArch64Emit`, which did the same experiment for
-- the FIRST-ORDER backend and got 12.
-- ------------------------------------------------------------------

exitOf : Maybe Conf → ℕ
exitOf c = memOf c (regOf c w9)

_ : exitOf idRun   ≡ 6            -- block 0 starts at instruction 6
_ = refl

_ : exitOf selfRun ≡ 29           -- block 1 starts at instruction 29
_ = refl

_ : exitOf bigRun  ≡ 33           -- block 1 of `bigT`, at instruction 33
_ = refl

applyKRun : Maybe Conf
applyKRun = runARM 200 (compileP applyK)

_ : exitOf applyKRun ≡ 45         -- block 1 of `applyK`, at instruction 45
_ = refl

-- ... and the block index those code addresses name, which is the head
-- of `ARM.answerT`'s answer.  `bigT`'s answer is `clos 1 (clos 2 ∷ [])`
-- and the exit status determines the `1` and not the `clos 2`.
_ : unAddr (mainLen (compileP bigT .snd)) (compileP bigT .fst) 0 33 ≡ 1
_ = refl

_ : answerT 500 8 bigT Eq.≡ just (clos 1 (clos 2 [] ∷ []))
_ = Eq.refl
