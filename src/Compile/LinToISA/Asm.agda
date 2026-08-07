{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  ASSEMBLY, AS TEXT.

  `Compile.LinToISA.Codegen` compiles a linear lambda term to a
  `Program` -- a list of `LI` -- and proves

      exec (compileU u) []  Eq.≡  layout u

  but a `List LI` is an Agda datatype, not assembly.  The C and Rust
  backends both emit real source text (`LinToC.Print.emitUnit`,
  `LinToRust.Alloc.Emit.renderProg`); the ISA backend stopped at the
  datatype, so "we have verified assembly" was true of the DATA and
  false of the OUTPUT.  This file closes that gap.

  It is deliberately a separate module rather than an addition to
  `Print`-then-`Codegen` (the shape `LinToC` uses), because the point
  here is to print the COMPILER'S OUTPUT, so it must import `Codegen`
  -- and `LinToC.Codegen` imports `LinToC.Print`, so the same
  arrangement would be a cycle.

  NOTHING IS PROVED HERE that is not already proved.  `emitAsm` is a
  function on the emitted program, and the correctness of that program
  is `Codegen.runU`.  Printing is not part of the trusted story: a
  printer bug produces wrong text from a right program, and the `refl`
  tests below are what rule that out, at the terms tested.

  Tokens are a finite alphabet and `primShowNat` computes on numerals,
  so `emitAsm` of a closed program is a closed `String` and every test
  below is `refl` -- the same discipline as the other two backends.
-}
open import Cubical.Foundations.Prelude

module Compile.LinToISA.Asm where

open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Nat using (ℕ)
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
-- TOKENS.  A finite alphabet, so `toks` never blocks a `refl`.
-- ==================================================================

data Tok : Type₀ where
  tIndent : Tok             -- "  "
  tNop    : Tok             -- "nop"
  tSt     : Tok             -- "st    "
  tAlloc  : Tok             -- "alloc "
  tAddr   : ℕ → Tok         -- "[<n>]"
  tComma  : Tok             -- ", "
  tLit    : H.Val → Tok     -- "#v0" | "#v1" | "#v2"
  tNL     : Tok             -- "\n"

showVal : H.Val → String
showVal H.v0 = "#v0"
showVal H.v1 = "#v1"
showVal H.v2 = "#v2"

tokS : Tok → String
tokS tIndent   = "  "
tokS tNop      = "nop"
tokS tSt       = "st    "
tokS tAlloc    = "alloc "
tokS (tAddr n) = "[" ++s primShowNat n ++s "]"
tokS tComma    = ", "
tokS (tLit x)  = showVal x
tokS tNL       = "\n"

-- ==================================================================
-- THE PRINTER.  One line per instruction.
--
-- `putI l x` names its address, which is why it is deterministic and
-- why `Machine.noPutLocal` says it fails `Local`.  `newI` does not name
-- one, which is why it frames and why it is the instruction the spill
-- demo uses.  The syntax below keeps that distinction visible.
-- ==================================================================

instrToks : LI → List Tok
instrToks nopI       = tIndent ∷ tNop ∷ tNL ∷ []
instrToks (putI l x) = tIndent ∷ tSt ∷ tAddr l ∷ tComma ∷ tLit x ∷ tNL ∷ []
instrToks (newI x)   = tIndent ∷ tAlloc ∷ tLit x ∷ tNL ∷ []

toks : Program → List Tok
toks []      = []
toks (i ∷ p) = instrToks i ++ toks p

-- ==================================================================
-- THE EDGE.  `render` is the only function that produces a `String`,
-- and it consumes a token list, not a source term.
-- ==================================================================

render : List Tok → String
render []       = ""
render (t ∷ ts) = tokS t ++s render ts

body : Program → String
body p = render (toks p)

preamble : String
preamble = "        .text\n        .globl frame\nframe:\n"

epilogue : String
epilogue = "        ret\n"

emitAsm : Program → String
emitAsm p = preamble ++s body p ++s epilogue

-- ==================================================================
-- THE OUTPUT.  These are the COMPILER'S programs, printed -- not
-- hand-written listings.  `ISA/RiscV/Base.agda`'s `prog` is a literal;
-- everything below comes out of `compileU`/`compileTm`.
-- ==================================================================

u2 : L.Usage                       -- two live variables
u2 = true ∷ true ∷ []

ugap : L.Usage                     -- three-variable scope, middle DEAD
ugap = true ∷ false ∷ true ∷ []

-- two live variables, two stores
_ : body (compileU u2) ≡ "  st    [0], #v1\n  st    [1], #v1\n"
_ = refl

-- ... and the dead middle position leaves an ADDRESS GAP in the
-- emitted assembly: there is no `[1]`, because positions are addresses
_ : body (compileU ugap) ≡ "  st    [0], #v1\n  st    [2], #v1\n"
_ = refl

-- a closed term allocates nothing, so the body is empty
_ : body (compileU []) ≡ ""
_ = refl

-- the whole compilation unit
_ : emitAsm (compileU ugap)
  ≡ "        .text\n        .globl frame\nframe:\n  st    [0], #v1\n  st    [2], #v1\n        ret\n"
_ = refl

-- ------------------------------------------------------------------
-- ... and from a TERM, through `compileTm`, so the chain
-- `Tm → Program → String` reduces end to end.
-- ------------------------------------------------------------------

_ : body (compileTm u2 L.twoVar .fst) ≡ "  st    [0], #v1\n  st    [1], #v1\n"
_ = refl

_ : body (compileTm [] L.idLin .fst) ≡ ""
_ = refl

-- ==================================================================
-- WHAT THIS DOES AND DOES NOT ADD.
--
-- ADDS: the ISA backend now emits text, so all three backends are
-- comparable at the level of concrete syntax, and `Compile.Showcase`'s
-- side-by-side is complete rather than two-thirds complete.
--
-- DOES NOT ADD: any new correctness.  `emitAsm` is unverified in the
-- sense that no theorem relates the STRING to the heap -- the verified
-- object is `compileU u`, and `Codegen.runU` is its theorem.  Closing
-- that last gap would mean a parser for the assembly syntax and a proof
-- that it inverts `emitAsm`, which is the standard "printer/parser
-- round trip" obligation and is NOT done here.
--
-- ALSO NOT DONE: this is the TOY ISA (`nopI`/`putI`/`newI`), not
-- RISC-V.  `ISA/RiscV/` has a machine model with `refl`-evaluating
-- programs, but nothing compiles into it, and `ISA/RiscV/RegAlloc.agda`
-- proves why the naive route is blocked: split preservation forces the
-- allocation to be injective (`presInj`), and no injective map into a
-- finite register file exists.  A LinLam → RISC-V backend must
-- therefore keep variables in MEMORY, where `layout` IS split-
-- preserving, and use registers only as scratch -- the "spill"
-- prescription in that file's header.
-- ==================================================================
