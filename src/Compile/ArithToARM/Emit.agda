{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  AArch64 FOR APPLE SILICON.  The last step, and the untrusted one.

      clang -o prog prog.s && ./prog ; echo $?

  prints `eval e σ`.

  ------------------------------------------------------------------
  THE MACHINE MODEL, MADE CONCRETE
  ------------------------------------------------------------------

  `Base`'s machine has an environment and a stack.  Both become memory:

      x19   ENVIRONMENT BASE.  Slot `l` is the word at `[x19, #8·l]`.
      x20   OPERAND STACK POINTER, growing DOWN, sixteen bytes a slot
            so the pointer stays 16-byte aligned.

  Neither is `sp` after the prologue, which is deliberate: `sp` on
  Darwin must stay 16-byte aligned and must not be used to address
  below itself, so an operand stack that rides on it would make every
  offset in the file depend on the current stack depth.  Two dedicated
  registers make each instruction's translation LOCAL -- one `AI`
  becomes a fixed token sequence, with no state threaded through the
  printer -- which is what keeps the untrusted part small enough to
  read.

      pushI n   mov w9, #n            ; str w9, [x20, #-16]!
      loadI l   ldr w9, [x19, #8·l]   ; str w9, [x20, #-16]!
      addI      ldr w9,  [x20], #16   -- the top, i.e. the RIGHT operand
                ldr w10, [x20], #16   -- beneath it, the LEFT operand
                add w9, w10, w9       -- left + right, in that order
                str w9, [x20, #-16]!

  `addI`'s operand order is the one place a transcription slip would be
  invisible in a `refl` test and visible only on hardware, so it is
  spelled out: `stepI addI σ (y ∷ x ∷ s) = (x + y) ∷ s` pops `y` first
  and computes `x + y`, and the two `ldr`s pop in the same order.
  Addition is commutative, so this particular slip is harmless; it is
  written down because the NEXT instruction added here will not be.

  x19 and x20 are callee-saved, so the prologue spills them.

  ------------------------------------------------------------------
  WHAT IS AND IS NOT VERIFIED.  Unchanged from
  `Compile.LinToISA.ARM64`, and worth repeating in full:

    VERIFIED   `compile e`, by `Codegen.correct`.  The `Prog` is the
               object with a theorem attached, and the theorem is a
               genuine simulation square -- the compiler is TERM-
               directed, so unlike the `Usage → Program` family it is
               not blocked by `Compile.Semantics.Simulation`'s
               `noBlindBackend`.
    NOT        this file.  No theorem relates the STRING to `exec`.

  Closing that gap means a semantics for the emitted AArch64 subset, or
  a parser and a round-trip proof.  Neither is done.  What HAS changed
  relative to the ISA backend is the size of what sits outside: a total
  function from a three-constructor instruction set to a fixed token
  list, with no source-language concept anywhere in it.

  ------------------------------------------------------------------
  THE ENVIRONMENT IS A HYPOTHESIS
  ------------------------------------------------------------------

  `Env` is a FUNCTION `ℕ → ℕ`, so it cannot be enumerated.  `emitARM`
  therefore takes the initial memory as an explicit association list and
  materialises it with one `mov`/`str` pair per entry.  The bridge to
  the theorem is a hypothesis, stated and not proved:

      if the list agrees with σ at every slot `compile e` READS,
      then the exit status is `eval e σ`.

  `Codegen.readsLive` says those slots are exactly the live positions of
  `u`, so the obligation is finite and checkable by inspection -- and
  `Codegen.readsDisjoint` says no two of them collide.  That is the
  linear discipline doing real work at the ABI boundary.

  ------------------------------------------------------------------
  LIMITS, stated rather than discovered later.  The frame is 1024 bytes,
  split as 512 for the environment (slots 0-63) and 512 for the operand
  stack (32 entries).  Deeper expressions and higher slot numbers
  overflow it silently; nothing here checks that, because nothing here
  is verified.
-}
open import Cubical.Foundations.Prelude

module Compile.ArithToARM.Emit where

open import Cubical.Data.Nat using (ℕ; zero; suc; _·_)
open import Cubical.Data.Sigma using (_×_; _,_)
open import Cubical.Data.List using (List; []; _∷_; _++_)
open import Agda.Builtin.String using (String; primStringAppend; primShowNat)

open import Compile.ArithToARM.Base
open import Compile.ArithToARM.Codegen
import TheoryGrammar.Instances.LinLam.Syntax as L

_++s_ : String → String → String
_++s_ = primStringAppend

infixr 5 _++s_

-- eight bytes per environment slot, so the offset is a legal `ldr`
-- immediate
slot : ℕ → ℕ
slot l = l · 8

-- ==================================================================
-- §1  TOKENS.  A finite alphabet; `primShowNat` computes on numerals,
-- so `emitARM` of a closed program is a closed `String`.
-- ==================================================================

data Tok : Type₀ where
  tMovImm  : ℕ → Tok       -- mov  w9, #n
  tStrEnv  : ℕ → Tok       -- str  w9, [x19, #off]
  tLdrEnv  : ℕ → Tok       -- ldr  w9, [x19, #off]
  tPush    : Tok           -- str  w9, [x20, #-16]!
  tPop9    : Tok           -- ldr  w9,  [x20], #16
  tPop10   : Tok           -- ldr  w10, [x20], #16
  tAdd     : Tok           -- add  w9, w10, w9
  tPopRes  : Tok           -- ldr  w0,  [x20], #16

tokS : Tok → String
tokS (tMovImm n) = "        mov     w9, #"   ++s primShowNat n ++s "\n"
tokS (tStrEnv o) = "        str     w9, [x19, #" ++s primShowNat o ++s "]\n"
tokS (tLdrEnv o) = "        ldr     w9, [x19, #" ++s primShowNat o ++s "]\n"
tokS tPush       = "        str     w9, [x20, #-16]!\n"
tokS tPop9       = "        ldr     w9, [x20], #16\n"
tokS tPop10      = "        ldr     w10, [x20], #16\n"
tokS tAdd        = "        add     w9, w10, w9\n"
tokS tPopRes     = "        ldr     w0, [x20], #16\n"

render : List Tok → String
render []       = ""
render (t ∷ ts) = tokS t ++s render ts

-- ==================================================================
-- §2  ONE INSTRUCTION AT A TIME.  Local, so the translation is a
-- `concatMap` and nothing is threaded through it.
-- ==================================================================

instrToks : AI → List Tok
instrToks (pushI n) = tMovImm n ∷ tPush ∷ []
instrToks (loadI l) = tLdrEnv (slot l) ∷ tPush ∷ []
instrToks addI      = tPop9 ∷ tPop10 ∷ tAdd ∷ tPush ∷ []

body : Prog → List Tok
body []      = []
body (i ∷ p) = instrToks i ++ body p

-- ==================================================================
-- §3  THE ENVIRONMENT, MATERIALISED.
-- ==================================================================

Assoc : Type₀
Assoc = List (ℕ × ℕ)               -- slot ↦ value

envToks : Assoc → List Tok
envToks []              = []
envToks ((l , v) ∷ ρ) = tMovImm v ∷ tStrEnv (slot l) ∷ envToks ρ

-- ==================================================================
-- §4  THE COMPILATION UNIT.
-- ==================================================================

preamble : String
preamble =
  "        .section __TEXT,__text\n        .globl _main\n        .p2align 2\n_main:\n        stp     x19, x20, [sp, #-16]!\n        sub     sp, sp, #1024\n        mov     x19, sp\n        add     x20, sp, #1024\n"

epilogue : String
epilogue =
  "        add     sp, sp, #1024\n        ldp     x19, x20, [sp], #16\n        ret\n"

emitARM : Assoc → Prog → String
emitARM ρ p =
  preamble ++s render (envToks ρ) ++s render (body p)
           ++s tokS tPopRes ++s epilogue

-- ... and from a SOURCE TERM, which is the whole point: `Exp → Prog →
-- AArch64` reduces end to end, and the middle arrow has a theorem.
emitExp : ∀ {u} → Assoc → Exp u → String
emitExp ρ e = emitARM ρ (compile e)

-- ==================================================================
-- §5  THE OUTPUT.  Compiler output, pinned by `refl`.
--
-- `egap` is `x0 + x2` in a three-variable scope whose middle position
-- is DEAD, and `ρ0` agrees with `Codegen.σ0` at the two live slots.
-- Position 1 is given a value it can never read, exactly to show that
-- `readsLive` is not vacuous: there is no `ldr` at offset 8.
-- ==================================================================

ρ0 : Assoc
ρ0 = (0 , 7) ∷ (1 , 99) ∷ (2 , 5) ∷ []

-- the two loads are at offsets 0 and 16 -- offset 8 is the dead middle
-- position, and it is simply absent
_ : render (body (compile egap))
  ≡ "        ldr     w9, [x19, #0]\n        str     w9, [x20, #-16]!\n        ldr     w9, [x19, #16]\n        str     w9, [x20, #-16]!\n        ldr     w9, [x20], #16\n        ldr     w10, [x20], #16\n        add     w9, w10, w9\n        str     w9, [x20, #-16]!\n"
_ = refl

-- THE WHOLE UNIT.  This exact string is what gets written to disk,
-- assembled with clang, and run.
armGap : String
armGap = emitExp ρ0 egap

-- ... and the nested one, which exercises `pushI` as well
armNest : String
armNest = emitExp ρ0 enest

-- The two `refl`s below are what make the hardware run EVIDENCE about
-- this development rather than about a file someone typed: they pin
-- `emitExp`'s output to the literal text that was assembled and run.
--
--     clang -o gap gap.s && ./gap   ; echo $?     -->  12
--     clang -o nst nst.s && ./nst   ; echo $?     -->  13
--
-- and `eval egap σ0 = 12`, `eval enest σ0 = 13` (§6).
_ : armGap
  ≡ "        .section __TEXT,__text\n        .globl _main\n        .p2align 2\n_main:\n        stp     x19, x20, [sp, #-16]!\n        sub     sp, sp, #1024\n        mov     x19, sp\n        add     x20, sp, #1024\n        mov     w9, #7\n        str     w9, [x19, #0]\n        mov     w9, #99\n        str     w9, [x19, #8]\n        mov     w9, #5\n        str     w9, [x19, #16]\n        ldr     w9, [x19, #0]\n        str     w9, [x20, #-16]!\n        ldr     w9, [x19, #16]\n        str     w9, [x20, #-16]!\n        ldr     w9, [x20], #16\n        ldr     w10, [x20], #16\n        add     w9, w10, w9\n        str     w9, [x20, #-16]!\n        ldr     w0, [x20], #16\n        add     sp, sp, #1024\n        ldp     x19, x20, [sp], #16\n        ret\n"
_ = refl

_ : armNest
  ≡ "        .section __TEXT,__text\n        .globl _main\n        .p2align 2\n_main:\n        stp     x19, x20, [sp, #-16]!\n        sub     sp, sp, #1024\n        mov     x19, sp\n        add     x20, sp, #1024\n        mov     w9, #7\n        str     w9, [x19, #0]\n        mov     w9, #99\n        str     w9, [x19, #8]\n        mov     w9, #5\n        str     w9, [x19, #16]\n        ldr     w9, [x19, #0]\n        str     w9, [x20, #-16]!\n        mov     w9, #1\n        str     w9, [x20, #-16]!\n        ldr     w9, [x19, #16]\n        str     w9, [x20, #-16]!\n        ldr     w9, [x20], #16\n        ldr     w10, [x20], #16\n        add     w9, w10, w9\n        str     w9, [x20, #-16]!\n        ldr     w9, [x20], #16\n        ldr     w10, [x20], #16\n        add     w9, w10, w9\n        str     w9, [x20, #-16]!\n        ldr     w0, [x20], #16\n        add     sp, sp, #1024\n        ldp     x19, x20, [sp], #16\n        ret\n"
_ = refl

-- ==================================================================
-- §6  THE PREDICTION.
--
-- `Codegen.run` proves `exec (compile e) σ [] Eq.≡ eval e σ ∷ []`, so
-- the single value left on the operand stack -- which the epilogue
-- pops into `w0`, and which becomes the process exit status -- is
-- `eval e σ`.  Running the binary MEASURES the denotation of the
-- source expression.
-- ==================================================================

_ : eval egap  σ0 ≡ 12
_ = refl

_ : eval enest σ0 ≡ 13
_ = refl
