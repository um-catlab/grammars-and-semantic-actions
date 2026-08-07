{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE CHAIN AS A FUNCTION OF THE INPUT STRING.

  `Chain.Pipeline` runs the whole pipeline on ONE hardcoded source
  string, with every stage pinned by `refl`.  That is the right shape
  for a proof artifact and the wrong shape for a command-line tool: to
  compile a string supplied at runtime there must be a FUNCTION of the
  string, because the answer is not known in advance and so cannot be
  pinned by `refl`.

  This module supplies those functions.  Nothing here is new
  mathematics; it is the plumbing that lets `scripts/compile-lambda.sh`
  normalise an expression with Agda's interaction mode and get the
  assembly back out.

  ------------------------------------------------------------------
  THE LANGUAGE.  `Lambda.Parse.Tok` is a FOUR token alphabet:

      vx  vy      the variables `x` and `y`
      lx  ly      the binders  `λx.` and `λy.`

  so the accepted programs are exactly the lambda terms over two
  variable names.  `λz. z` is a LEXICAL error, not a parse error, and
  `Chain.Lex` reports it as `nothing`.

  ------------------------------------------------------------------
  WHAT THE EXIT CODE MEASURES, and why it is the token count.

  The honest thing to say here is a negative result.  `Chain.Pipeline`
  parses at scope `[]`, so every ACCEPTED program is CLOSED, hence has
  usage `[]`, hence -- by `Compile.Semantics.Simulation.noBlindBackend`
  -- compiles to the EMPTY program and would exit 0 whatever it was.
  Two different closed terms give the same executable.  That is the
  blindness theorem showing up as a user-visible fact, not a defect of
  this file.

  So the observable used below is the LEXER's output length: one live
  position per token, hence one stack cell per token, hence an exit
  status equal to the token count.  That is a genuine function of the
  input, it is produced by the verified lexer, and it is honest about
  what it measures -- the SHAPE of the program, not its meaning.

  When a term-directed backend lands (`Compile.LinToRust.Codegen` is
  the one positioned for it -- see `Compile.Relational`), the observable
  can become the value the term computes, and this module is where that
  swap happens.
-}
open import Cubical.Foundations.Prelude

module Chain.Run where

open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.List using (List; []; _∷_; length)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.String using (String)

import Chain.Lex                              as LX
import TheoryGrammar.Instances.LinLam.Codegen as L

open import Compile.LinToISA.Codegen
open import Compile.LinToISA.ARM64

-- ==================================================================
-- §1  STAGE 1 -- LEXING, as total functions.
--
-- Explicit helpers rather than `with`: a `with`-abstraction can block
-- reduction, and every definition here has to normalise on a closed
-- string for the script to work.
-- ==================================================================

okOf : Maybe (List LX.LTok) → Bool
okOf (just _)  = true
okOf nothing   = false

countOf : Maybe (List LX.LTok) → ℕ
countOf (just ts) = length ts
countOf nothing   = 0

-- "does this string lex?"  The error branch is real: `λz. z` is not a
-- token of the language.
lexOK : String → Bool
lexOK s = okOf (LX.lexS s)

-- how many tokens.  `λx.` is ONE token spanning three characters.
tokCount : String → ℕ
tokCount s = countOf (LX.lexS s)

-- ==================================================================
-- §2  THE USAGE, and the assembly.
--
-- One live position per token.  `compileU` then emits one `str` per
-- live position at its own address, and `Codegen.runU` is the theorem
-- that the resulting heap is `layout u`.
-- ==================================================================

allLive : ℕ → L.Usage
allLive zero    = []
allLive (suc n) = true ∷ allLive n

usageOf : String → L.Usage
usageOf s = allLive (tokCount s)

progOf : String → Program
progOf s = compileU (usageOf s)

-- THE ENTRY POINT the script normalises.
asmFor : String → String
asmFor s = emitARM (progOf s)

-- ==================================================================
-- §3  IT COMPUTES.  These are `refl` at strings chosen here, which is
-- exactly what the script does at a string chosen by the user.
-- ==================================================================

_ : lexOK "λx. x λy. y" ≡ true
_ = refl

_ : lexOK "λz. z" ≡ false          -- lexical error: no `z` in the alphabet
_ = refl

_ : tokCount "λx. x λy. y" ≡ 4
_ = refl

_ : tokCount "x y" ≡ 2
_ = refl

_ : usageOf "x y" ≡ true ∷ true ∷ []
_ = refl

_ : L.live (usageOf "λx. x λy. y") ≡ 4
_ = refl

-- the emitted assembly for a two-token program, in full
_ : asmFor "x y"
  ≡ "        .section __TEXT,__text\n        .globl _main\n        .p2align 2\n_main:\n        sub     sp, sp, #256\n        mov     w0, #0\n        mov     w9, #1\n        str     w9, [sp, #0]\n        mov     w9, #1\n        str     w9, [sp, #8]\n        ldr     w9, [sp, #0]\n        add     w0, w0, w9\n        ldr     w9, [sp, #8]\n        add     w0, w0, w9\n        add     sp, sp, #256\n        ret\n"
_ = refl
