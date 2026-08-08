{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE PRINTER, WHICH NOW CARRIES NO SEMANTIC CONTENT.

  `Compile.ArithToARM.Emit` had to expand a three-constructor stack ISA
  into real AArch64, so the expansion -- the part where a transcription
  slip hides -- sat OUTSIDE the proof.  `Instr` is now the real
  instruction set, so this file is a one-to-one rendering: each
  constructor prints as the single line of assembly it denotes, and
  there is nothing left to get wrong except the spelling.

  Even the environment setup and the final pop are ordinary `Instr`s
  (`movI`/`strO`, and `ldrPre w0 x20 16`), so they are covered by
  `AArch64Codegen.correct` rather than bolted on in text.

  WHAT IS STILL RAW TEXT: the frame prologue and epilogue.  `sp`,
  `stp`/`ldp` and the calling convention are not modelled, so those
  four lines are trusted.  They allocate 2048 bytes, put the
  environment base in x19 and the operand stack base 1024 bytes above
  it -- which is the `Sep` hypothesis, discharged by construction and
  by inspection of two constants.
-}
open import Cubical.Foundations.Prelude

module Compile.ArithToARM.AArch64Emit where

open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.List using (List; []; _∷_; _++_)
open import Cubical.Data.Sigma using (_×_; _,_)
open import Agda.Builtin.String using (String; primStringAppend; primShowNat)

open import Compile.ArithToARM.AArch64
open import Compile.ArithToARM.AArch64Codegen
open import Compile.ArithToARM.Base using (Exp)
open import Compile.ArithToARM.Codegen using (egap; enest)

_++s_ : String → String → String
_++s_ = primStringAppend

infixr 5 _++s_

-- 32-bit and 64-bit views of the register file
wN : Reg → String
wN w0 = "w0"
wN w9 = "w9"
wN w10 = "w10"
wN x19 = "w19"
wN x20 = "w20"

xN : Reg → String
xN w0 = "x0"
xN w9 = "x9"
xN w10 = "x10"
xN x19 = "x19"
xN x20 = "x20"

n# : ℕ → String
n# n = "#" ++s primShowNat n

-- ONE LINE PER CONSTRUCTOR.  This is the whole printer.
line : Instr → String
line (movI d n)      = "        mov     " ++s wN d ++s ", " ++s n# n ++s "\n"
line (movR d n)      = "        mov     " ++s xN d ++s ", " ++s xN n ++s "\n"
line (addR d a b)    = "        add     " ++s wN d ++s ", " ++s wN a ++s ", " ++s wN b ++s "\n"
line (addI d n k)    = "        add     " ++s xN d ++s ", " ++s xN n ++s ", " ++s n# k ++s "\n"
line (ldrO t n k)    = "        ldr     " ++s wN t ++s ", [" ++s xN n ++s ", " ++s n# k ++s "]\n"
line (strO t n k)    = "        str     " ++s wN t ++s ", [" ++s xN n ++s ", " ++s n# k ++s "]\n"
line (strPost t n k) = "        str     " ++s wN t ++s ", [" ++s xN n ++s "], " ++s n# k ++s "\n"
line (ldrPre t n k)  = "        ldr     " ++s wN t ++s ", [" ++s xN n ++s ", #-" ++s primShowNat k ++s "]!\n"

render : Prog → String
render []      = ""
render (i ∷ p) = line i ++s render p

-- ==================================================================
-- THE WHOLE UNIT, as a PROGRAM.  Environment setup, the compiled
-- expression, and the pop into w0 are all `Instr`s.
-- ==================================================================

Assoc : Type₀
Assoc = List (ℕ × ℕ)

envProg : Assoc → Prog
envProg []             = []
envProg ((l , v) ∷ ρ) = movI w9 v ∷ strO w9 x19 (off8 l) ∷ envProg ρ

unit : ∀ {u} → Assoc → Exp u → Prog
unit ρ e = envProg ρ ++ (compile e ++ (ldrPre w0 x20 16 ∷ []))

preamble : String
preamble =
  "        .section __TEXT,__text\n        .globl _main\n        .p2align 2\n_main:\n        stp     x19, x20, [sp, #-16]!\n        sub     sp, sp, #2048\n        mov     x19, sp\n        add     x20, sp, #1024\n"

epilogue : String
epilogue =
  "        add     sp, sp, #2048\n        ldp     x19, x20, [sp], #16\n        ret\n"

emit : ∀ {u} → Assoc → Exp u → String
emit ρ e = preamble ++s render (unit ρ e) ++s epilogue

-- ==================================================================
-- THE OUTPUT, pinned.
-- ==================================================================

ρ0 : Assoc
ρ0 = (0 , 7) ∷ (1 , 99) ∷ (2 , 5) ∷ []

armGap : String
armGap = emit ρ0 egap

_ : render (compile egap)
  ≡ "        ldr     w9, [x19, #0]\n        str     w9, [x20], #16\n        ldr     w9, [x19, #16]\n        str     w9, [x20], #16\n        ldr     w9, [x20, #-16]!\n        ldr     w10, [x20, #-16]!\n        add     w9, w10, w9\n        str     w9, [x20], #16\n"
_ = refl

-- THE COMPLETE UNIT.  This exact text was assembled with clang and run
-- on Apple silicon; the exit status was 12, and `AArch64Codegen`'s
--
--     _ : mm (exec (compile egap) st0) 1024 ≡ 12
--
-- is the same number predicted by the verified model.  The `refl`
-- below is what makes that a statement about THIS development.
_ : armGap
  ≡ "        .section __TEXT,__text\n        .globl _main\n        .p2align 2\n_main:\n        stp     x19, x20, [sp, #-16]!\n        sub     sp, sp, #2048\n        mov     x19, sp\n        add     x20, sp, #1024\n        mov     w9, #7\n        str     w9, [x19, #0]\n        mov     w9, #99\n        str     w9, [x19, #8]\n        mov     w9, #5\n        str     w9, [x19, #16]\n        ldr     w9, [x19, #0]\n        str     w9, [x20], #16\n        ldr     w9, [x19, #16]\n        str     w9, [x20], #16\n        ldr     w9, [x20, #-16]!\n        ldr     w10, [x20, #-16]!\n        add     w9, w10, w9\n        str     w9, [x20], #16\n        ldr     w0, [x20, #-16]!\n        add     sp, sp, #2048\n        ldp     x19, x20, [sp], #16\n        ret\n"
_ = refl
