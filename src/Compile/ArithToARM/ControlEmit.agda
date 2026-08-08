{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE PRINTER FOR THE *CONTROL* MACHINE.

  `AArch64Emit` prints a `Prog` -- a straight line of the eight
  arithmetic instructions -- and has nothing to say about a branch,
  because `AArch64.exec` has no counter.  `Control.CProg` has one, and
  its five extra constructors all carry a BRANCH TARGET WHICH IS A LIST
  INDEX.  An index is not an address, so this file has exactly one
  problem to solve and everything else is spelling.

  ------------------------------------------------------------------
  §A  AN INDEX IS NOT AN ADDRESS -- THE TWO HALVES OF THE FIX
  ------------------------------------------------------------------

  (1)  STATIC targets (`bra`, `cbz`, `bl`) are indices known at emission
       time, so they become LABELS.  Every instruction of the program is
       preceded by its own label `.Li`, and index `i` prints as `.Li`.
       This is deliberately the least clever option available: computing
       a PC-relative displacement would put an arithmetic obligation
       between the model and the text, and the model has no arithmetic
       to discharge it with.  A label costs one line and cannot be off
       by one.

       The program of length `n` gets labels `.L0 .. .Ln` -- one PAST
       the end, because `Control.run` HALTS when the counter leaves the
       program, and `ClosureConv.ARM.compileC` reaches that halt by
       branching to `progLen P` explicitly.  So `.Ln` is where a halted
       program lands, and it is where the exit sequence goes.

  (2)  The DYNAMIC target (`blr r`) is a register, and the register
       holds an INDEX -- `ClosureConv.ARM` puts one there with
       `movI w9 (am i)` and reads one back out of a closure record with
       `ldrO w9 w9 0`.  Turning those into addresses at the `movI` would
       be wrong twice over: the printer would have to know which `movI`
       immediates are code addresses (`Control.callProg`'s `movI w9 21`
       is not one), and the machine's MEMORY would then hold addresses
       where the model says it holds indices -- so
       `ARM.agda`'s `memOf idRun 512 ≡ 6` would stop being a statement
       about the emitted program.

       Instead the indirection happens AT THE JUMP, through a table
       emitted after the code:

           .Lcodetab:  .quad .L0-.Lcodetab
                       .quad .L1-.Lcodetab
                       ...

       and `blr r` expands to four lines: take the table's address,
       index it by `r`, add, jump.  DIFFERENCES and not absolute
       addresses, because an absolute pointer relocation inside
       `__TEXT` is rejected by the linker on a position-independent
       target.

       The two scratch registers this needs -- `x21`, `x22` -- are
       chosen OUTSIDE `AArch64.Reg`, so no register the model reasons
       about is disturbed.  That is the same discipline `Control.agda`
       used when it put the link register in the configuration instead
       of in `Reg`.

  ------------------------------------------------------------------
  §B  SIXTY-FOUR BITS, NOT THIRTY-TWO
  ------------------------------------------------------------------

  `AArch64Emit` renders `movI`/`ldr`/`str` at the `w` (32-bit) view.
  That is sound for arithmetic on small numbers and UNSOUND the moment
  a stored word is a POINTER, which is exactly what `ClosureConv.ARM`
  stores: `Val` is a heap address and nothing else.  So this printer
  renders every register at the `x` view and every load and store at 64
  bits.  Nothing in `AArch64.exec1` distinguishes the two -- `Word` is
  `ℕ` -- so this is a strictly more faithful rendering of the same
  model, not a different one.

  ------------------------------------------------------------------
  §C  WHAT IS STILL RAW TEXT, AND THEREFORE TRUSTED
  ------------------------------------------------------------------

  The preamble and the exit sequence, as in `AArch64Emit`.  The
  preamble is longer here because the model's `Mem` is a function from
  `ℕ` and the machine's is not:

      the model's address `a` is rendered as `membase + a`

  where `membase` is a block of stack the preamble carves out and
  ZEROES (the model's memory is the constant `0`).  Every model
  register that holds an address is initialised to `membase + k` for
  the model's `k`, so every subsequent load, store and pointer
  arithmetic is the model's, shifted by one constant.  No instruction
  in the body knows about the shift.

  ------------------------------------------------------------------
  §D  THE PERFORMANCE TRAP THIS FILE AVOIDS
  ------------------------------------------------------------------

  `length p` is taken ONCE, at the top of `unitWith`, and threaded as a
  COUNT into the table printer.  Agda's `let` is substitution, so a
  `length` under a recursive emitter is recomputed per occurrence; that
  is the same trap `ClosureConv.ARM` §4 avoids with `sizeE`.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1: this is a printer, like `AArch64Emit`.
-}
open import Cubical.Foundations.Prelude

module Compile.ArithToARM.ControlEmit where

open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.List using (List; []; _∷_; _++_; length)
open import Agda.Builtin.String using (String; primStringAppend; primShowNat)

open import Compile.ArithToARM.AArch64 hiding (Prog)
open import Compile.ArithToARM.Control

_++s_ : String → String → String
_++s_ = primStringAppend

infixr 5 _++s_

-- ==================================================================
-- §1  NAMES.  Every register at the 64-bit view; see §B.
-- ==================================================================

xN : Reg → String
xN w0  = "x0"
xN w9  = "x9"
xN w10 = "x10"
xN x19 = "x19"
xN x20 = "x20"

n# : ℕ → String
n# n = "#" ++s primShowNat n

-- A LABEL, and the only place an index becomes a name.
lbl : ℕ → String
lbl n = ".L" ++s primShowNat n

lblLine : ℕ → String
lblLine n = lbl n ++s ":\n"

-- ==================================================================
-- §2  THE EIGHT ARITHMETIC INSTRUCTIONS.  One line each, exactly as in
-- `AArch64Emit.line`, at the `x` view.
-- ==================================================================

bline : Instr → String
bline (movI d n)      = "        mov     " ++s xN d ++s ", " ++s n# n ++s "\n"
bline (movR d n)      = "        mov     " ++s xN d ++s ", " ++s xN n ++s "\n"
bline (addR d a b)    = "        add     " ++s xN d ++s ", " ++s xN a ++s ", " ++s xN b ++s "\n"
bline (addI d n k)    = "        add     " ++s xN d ++s ", " ++s xN n ++s ", " ++s n# k ++s "\n"
bline (ldrO t n k)    = "        ldr     " ++s xN t ++s ", [" ++s xN n ++s ", " ++s n# k ++s "]\n"
bline (strO t n k)    = "        str     " ++s xN t ++s ", [" ++s xN n ++s ", " ++s n# k ++s "]\n"
bline (strPost t n k) = "        str     " ++s xN t ++s ", [" ++s xN n ++s "], " ++s n# k ++s "\n"
bline (ldrPre t n k)  = "        ldr     " ++s xN t ++s ", [" ++s xN n ++s ", #-" ++s primShowNat k ++s "]!\n"

-- ==================================================================
-- §3  THE FIVE CONTROL INSTRUCTIONS.
--
-- Four of them are one line.  `blr` is the table indirection of §A(2),
-- and it is the only expansion in the file.
-- ==================================================================

blrSeq : Reg → String
blrSeq r =
     "        adr     x21, .Lcodetab\n"
  ++s "        ldr     x22, [x21, " ++s xN r ++s ", lsl #3]\n"
  ++s "        add     x21, x21, x22\n"
  ++s "        blr     x21\n"

cline : CInstr → String
cline (base i)  = bline i
cline (bra t)   = "        b       " ++s lbl t ++s "\n"
cline (cbz r t) = "        cbz     " ++s xN r ++s ", " ++s lbl t ++s "\n"
cline (bl t)    = "        bl      " ++s lbl t ++s "\n"
cline (blr r)   = blrSeq r
cline ret       = "        ret\n"

-- THE BODY.  Every instruction gets its index as a label, and the
-- recursion ends by emitting the label ONE PAST THE END -- which is
-- where `Control.run` halts, and where §5's exit sequence goes.
renderAt : ℕ → CProg → String
renderAt i []      = lblLine i
renderAt i (x ∷ p) = lblLine i ++s cline x ++s renderAt (suc i) p

renderC : CProg → String
renderC = renderAt 0

-- ==================================================================
-- §4  THE CODE TABLE.  `n` entries starting at index `i`; the caller
-- passes `suc (length p)` so that the halt label is reachable too.
-- ==================================================================

tabFrom : ℕ → ℕ → String
tabFrom i zero    = ""
tabFrom i (suc n) = "        .quad   " ++s lbl i ++s "-.Lcodetab\n" ++s tabFrom (suc i) n

codeTab : ℕ → String
codeTab n = "        .p2align 3\n.Lcodetab:\n" ++s tabFrom 0 (suc n)

-- ==================================================================
-- §5  THE PREAMBLE AND THE EXIT.  RAW TEXT, hence trusted; see §C.
--
-- `preamble bytes sOff hOff` carves `bytes` bytes of stack, zeroes
-- them, and initialises the model's three address registers:
--
--     x19 := membase          the model's 0 -- also the frame pointer
--     x20 := membase + sOff   the operand stack base
--     x0  := membase + hOff   the heap base
--
-- so `ClosureConv.ARM.initSt` is realised by three `add`s.
-- ==================================================================

preamble : ℕ → ℕ → ℕ → String
preamble bytes sOff hOff =
     "        .section __TEXT,__text\n"
  ++s "        .globl _main\n"
  ++s "        .p2align 2\n"
  ++s "_main:\n"
  ++s "        stp     x29, x30, [sp, #-16]!\n"
  ++s "        stp     x19, x20, [sp, #-16]!\n"
  ++s "        stp     x21, x22, [sp, #-16]!\n"
  ++s "        sub     sp, sp, " ++s n# bytes ++s "\n"
  ++s "        mov     x19, sp\n"
  ++s "        mov     x21, #0\n"
  ++s ".Lzloop:\n"
  ++s "        str     xzr, [x19, x21]\n"
  ++s "        add     x21, x21, #8\n"
  ++s "        cmp     x21, " ++s n# bytes ++s "\n"
  ++s "        b.lo    .Lzloop\n"
  ++s "        add     x20, x19, " ++s n# sOff ++s "\n"
  ++s "        add     x0, x19, " ++s n# hOff ++s "\n"

teardown : ℕ → String
teardown bytes =
     "        add     sp, sp, " ++s n# bytes ++s "\n"
  ++s "        ldp     x21, x22, [sp], #16\n"
  ++s "        ldp     x19, x20, [sp], #16\n"
  ++s "        ldp     x29, x30, [sp], #16\n"
  ++s "        ret\n"

-- ------------------------------------------------------------------
-- 5.1  THE TWO OBSERVABLES, as the two things a halted machine can be
-- asked for.  An exit status is eight bits, so both are masked -- and
-- the mask is stated here rather than assumed, because it is the one
-- place the process's answer is narrower than the model's.
-- ------------------------------------------------------------------

-- "the value the machine halted holding", i.e. `regOf c w9`
finVal : String
finVal =
     "        and     x0, x9, #255\n"

-- "the CODE INDEX of the closure the machine halted holding", i.e.
-- `memOf c (regOf c w9)` -- a pointer is not an exit status, but the
-- block it names is.  This is the observable `ClosureConv.ARM`'s
-- `memOf bigRun 528 ≡ 33` already pins.
finCode : String
finCode =
     "        ldr     x0, [x9]\n"
  ++s "        and     x0, x0, #255\n"

-- ==================================================================
-- §6  THE WHOLE UNIT.  `length p` is taken ONCE; see §D.
-- ==================================================================

unitWith : ℕ → ℕ → ℕ → String → CProg → String
unitWith bytes sOff hOff fin p =
  preamble bytes sOff hOff
  ++s renderC p
  ++s fin
  ++s teardown bytes
  ++s codeTab (length p)

-- ==================================================================
-- §7  IT COMPUTES, at `Control.agda`'s own witnesses.
--
-- These three programs are the ones §10-§11 of that file RUN on the
-- model, so the text below and the numbers there are two readings of
-- one object.  `sumProg` and `callProg` answer with a VALUE, so they
-- take `finVal`; `indProg` is the one that exercises `blr`, hence the
-- code table.
-- ==================================================================

-- 7.1  the branch instructions alone, with no preamble in the way
_ : renderC sumProg
  ≡ ".L0:\n        ldr     x9, [x19, #0]\n.L1:\n        cbz     x9, .L5\n.L2:\n        add     x10, x10, x9\n.L3:\n        add     x19, x19, #8\n.L4:\n        b       .L0\n.L5:\n"
_ = refl

-- 7.2  `bl` and `ret`, which `ClosureConv.ARM` never emits but which
-- the machine has -- so the printer covers all six constructors
_ : renderC callProg
  ≡ ".L0:\n        mov     x9, #21\n.L1:\n        bl      .L3\n.L2:\n        b       .L5\n.L3:\n        add     x9, x9, x9\n.L4:\n        ret\n.L5:\n"
_ = refl

-- 7.3  THE INDIRECT CALL, and hence the table indirection of §A(2)
_ : cline (blr w0)
  ≡ "        adr     x21, .Lcodetab\n        ldr     x22, [x21, x0, lsl #3]\n        add     x21, x21, x22\n        blr     x21\n"
_ = refl

-- 7.4  the table, at a three-instruction program: FOUR entries
_ : codeTab 3
  ≡ "        .p2align 3\n.Lcodetab:\n        .quad   .L0-.Lcodetab\n        .quad   .L1-.Lcodetab\n        .quad   .L2-.Lcodetab\n        .quad   .L3-.Lcodetab\n"
_ = refl
