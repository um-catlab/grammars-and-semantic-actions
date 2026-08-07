{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  ARM64 (AArch64) FOR APPLE SILICON -- assembly that actually runs.

  `Compile.LinToISA.Asm` prints the toy ISA in a made-up syntax.  This
  file prints AArch64 in Apple's assembler syntax, so the output of

      clang -o prog prog.s && ./prog ; echo $?

  is a real number produced by real hardware.

  ------------------------------------------------------------------
  WHAT THE EMITTED PROGRAM DOES, and why that is the honest observable.

  `LinLam.Codegen.layout` sends variable position `i` to address `i`,
  and stores `v1` at every LIVE position.  So the heap the compiler is
  proved to produce (`Codegen.runU : exec (compileU u) [] Eq.≡ layout u`)
  is exactly "a cell holding 1 at each live position, and a gap at each
  dead one".  The emitted program materialises that heap on the stack
  and then reads it back:

      pass 1   one `str` per instruction, at offset 8·address
      pass 2   one `ldr`/`add` per instruction, accumulating into w0

  and `w0` is `main`'s return value, hence the process exit status.
  Since every stored value is `v1 = 1`, the exit status is the number of
  live positions -- i.e. `LinLam.Context.live u`, a quantity this
  development already reasons about (`liveSplit`, and `liveSplit≤` in
  the affine instance).

  The two passes are deliberate.  Storing and immediately reloading
  would prove nothing; separating them means the values genuinely
  persist in memory between the phases, so the exit status is a
  measurement of the materialised heap rather than of a register.

  ------------------------------------------------------------------
  WHAT IS AND IS NOT VERIFIED.  Unchanged from `Asm.agda`, and worth
  repeating because running the code makes it tempting to overclaim:

    VERIFIED   `compileU u`, by `Codegen.runU`.  The instruction list
               is the object with a theorem attached.
    NOT        the printer.  No theorem relates the STRING to the heap.
               The `refl` tests below pin the text at the terms tested,
               and running it on hardware is evidence, not proof.

  Closing that gap means a parser for AArch64 and a round-trip proof, or
  a semantics for the emitted subset; neither is done.

  ------------------------------------------------------------------
  LIMITS, stated rather than discovered later.  The frame is a fixed 256
  bytes (32 slots), so addresses must be < 32; every test here uses
  addresses 0-2.  `newI` is the nondeterministic allocator and has no
  fixed address, so it emits nothing -- consistent with
  `Machine.noPutLocal`, which is why `putI` and not `newI` is what the
  compiler emits.
-}
open import Cubical.Foundations.Prelude

module Compile.LinToISA.ARM64 where

open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Nat using (ℕ; _·_)
open import Cubical.Data.List using (List; []; _∷_; _++_)
open import Agda.Builtin.String using (String; primStringAppend; primShowNat)

import TheoryGrammar.Instances.Heap.Base      as H
import TheoryGrammar.Instances.LinLam.Codegen as L

open import Compile.LinToISA.Machine
open import Compile.LinToISA.Codegen

_++s_ : String → String → String
_++s_ = primStringAppend

infixr 5 _++s_

-- ==================================================================
-- VALUES AND SLOTS.
-- ==================================================================

valNat : H.Val → ℕ
valNat H.v0 = 0
valNat H.v1 = 1
valNat H.v2 = 2

-- eight bytes per cell, so the offset is a legal `str`/`ldr` immediate
slot : ℕ → ℕ
slot l = l · 8

-- ==================================================================
-- TOKENS.  A finite alphabet; `primShowNat` computes on numerals, so
-- `emitARM` of a closed program is a closed `String`.
-- ==================================================================

data Tok : Type₀ where
  tMovAcc : Tok            -- "        mov     w0, #0\n"
  tMovImm : ℕ → Tok        -- "        mov     w9, #<n>\n"
  tStr    : ℕ → Tok        -- "        str     w9, [sp, #<off>]\n"
  tLdr    : ℕ → Tok        -- "        ldr     w9, [sp, #<off>]\n"
  tAdd    : Tok            -- "        add     w0, w0, w9\n"
  tNop    : Tok            -- "        nop\n"

tokS : Tok → String
tokS tMovAcc     = "        mov     w0, #0\n"
tokS (tMovImm n) = "        mov     w9, #" ++s primShowNat n ++s "\n"
tokS (tStr off)  = "        str     w9, [sp, #" ++s primShowNat off ++s "]\n"
tokS (tLdr off)  = "        ldr     w9, [sp, #" ++s primShowNat off ++s "]\n"
tokS tAdd        = "        add     w0, w0, w9\n"
tokS tNop        = "        nop\n"

-- ==================================================================
-- THE TWO PASSES.
-- ==================================================================

storeToks : LI → List Tok
storeToks nopI       = tNop ∷ []
storeToks (putI l x) = tMovImm (valNat x) ∷ tStr (slot l) ∷ []
storeToks (newI _)   = []          -- no fixed address; see the header

loadToks : LI → List Tok
loadToks nopI       = []
loadToks (putI l _) = tLdr (slot l) ∷ tAdd ∷ []
loadToks (newI _)   = []

stores : Program → List Tok
stores []      = []
stores (i ∷ p) = storeToks i ++ stores p

loads : Program → List Tok
loads []      = []
loads (i ∷ p) = loadToks i ++ loads p

render : List Tok → String
render []       = ""
render (t ∷ ts) = tokS t ++s render ts

-- ==================================================================
-- THE COMPILATION UNIT.
-- ==================================================================

preamble : String
preamble =
  "        .section __TEXT,__text\n        .globl _main\n        .p2align 2\n_main:\n        sub     sp, sp, #256\n"

epilogue : String
epilogue = "        add     sp, sp, #256\n        ret\n"

emitARM : Program → String
emitARM p = preamble ++s tokS tMovAcc ++s render (stores p) ++s render (loads p) ++s epilogue

-- ==================================================================
-- THE OUTPUT.  Compiler output, pinned by `refl`.
-- ==================================================================

u2 : L.Usage                       -- two live variables
u2 = true ∷ true ∷ []

ugap : L.Usage                     -- three-variable scope, middle DEAD
ugap = true ∷ false ∷ true ∷ []

-- the body for the gap usage: stores at 0 and 16 (addresses 0 and 2),
-- nothing at 8 -- the dead position leaves a hole in the FRAME
_ : render (stores (compileU ugap))
  ≡ "        mov     w9, #1\n        str     w9, [sp, #0]\n        mov     w9, #1\n        str     w9, [sp, #16]\n"
_ = refl

_ : render (loads (compileU ugap))
  ≡ "        ldr     w9, [sp, #0]\n        add     w0, w0, w9\n        ldr     w9, [sp, #16]\n        add     w0, w0, w9\n"
_ = refl

-- a closed term stores nothing, so the program returns 0
_ : render (stores (compileU [])) ≡ ""
_ = refl

-- THE WHOLE UNIT, for `ugap`.  This exact string is what gets written
-- to disk, assembled with clang, and run.
armGap : String
armGap = emitARM (compileU ugap)

_ : armGap
  ≡ "        .section __TEXT,__text\n        .globl _main\n        .p2align 2\n_main:\n        sub     sp, sp, #256\n        mov     w0, #0\n        mov     w9, #1\n        str     w9, [sp, #0]\n        mov     w9, #1\n        str     w9, [sp, #16]\n        ldr     w9, [sp, #0]\n        add     w0, w0, w9\n        ldr     w9, [sp, #16]\n        add     w0, w0, w9\n        add     sp, sp, #256\n        ret\n"
_ = refl

-- ... and from a TERM, so `Tm → Program → AArch64` reduces end to end
armTwoVar : String
armTwoVar = emitARM (compileTm u2 L.twoVar .fst)

-- ==================================================================
-- THE PREDICTION.  Every stored value is `v1 = 1`, so the accumulated
-- `w0` -- the process exit status -- is the number of live positions.
--
--     live ugap = 2      live u2 = 2      live [] = 0
--
-- `live` is `LinLam.Context.live`, the degree of the linear grading.
-- So running the binary MEASURES the grading of the source usage.
-- ==================================================================

_ : L.live ugap ≡ 2
_ = refl

_ : L.live u2 ≡ 2
_ = refl

_ : L.live [] ≡ 0
_ = refl
