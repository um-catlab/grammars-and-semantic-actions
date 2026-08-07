{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  REAL C SOURCE TEXT, VIA A TOKEN LIST.

  The rule this file obeys is `CLAUDE.md`'s EXTERNALISE LATE: a producer
  must not mention `String` in its type.  So nothing here produces a
  compiled artefact.  The producer is `Compile.LinToC.Codegen.compileTm`,
  a term `L.TmG L.⊢ Obj` whose payload is a Hoare triple; this file only
  RENDERS an object that already exists.

  The rendering is staged so that it stays `refl`-computable:

      stmtToks : CStmt → List Tok        -- no strings anywhere
      toks     : CProg → List Tok
      render   : List Tok → String       -- the very edge
      emitUnit : CProg → String          -- + preamble, a compilable TU

  `Tok` is a finite datatype (plus two ℕ payloads for object names), so
  `toks` is as reducible as the program it prints, and a `refl` test on a
  token list is cheap.  `render` is a right fold of `primStringAppend`
  over string literals, which Agda evaluates, so a `refl` test against a
  literal C program also goes through -- and that is the test worth
  having, because it shows the ACTUAL SOURCE.

  The emitted translation unit is genuine C99:

      #include <stdlib.h>

      typedef enum { V0, V1, V2 } val_t;
      static val_t mem[64];

      void frame(void) {
        val_t x0 = V1;
        val_t x2 = V1;
      }

  `mem` exists only so that `cstore` -- the aliasing statement, which the
  compiler never emits -- has something to point into.  `x<l>` is the
  object at layout address `l`, and the DEAD positions of the usage leave
  gaps in the numbering, which is `LinLam/Codegen.lay`'s "positions are
  addresses" visible in the source text.
-}
open import Cubical.Foundations.Prelude

module Compile.LinToC.Print where

open import Agda.Builtin.String
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.List using (List; []; _∷_; _++_)

open import Compile.LinToC.Machine

-- ==================================================================
-- Strings, at the edge only.
-- ==================================================================

_++s_ : String → String → String
_++s_ = primStringAppend

infixr 5 _++s_

-- ==================================================================
-- TOKENS.  A finite alphabet, so `toks` never blocks a `refl`.
-- ==================================================================

data Tok : Type₀ where
  tIndent  : Tok            -- "  "
  tValT    : Tok            -- "val_t "
  tObj     : ℕ → Tok        -- "x<n>"        -- the object at address n
  tCell    : ℕ → Tok        -- "*(mem + <n>)"
  tPtr     : Tok            -- "val_t *p = malloc(sizeof(val_t)); *p"
  tAssign  : Tok            -- " = "
  tLit     : Val → Tok      -- "V0" | "V1" | "V2"
  tSemi    : Tok            -- ";"
  tNL      : Tok            -- "\n"

showVal : Val → String
showVal v0 = "V0"
showVal v1 = "V1"
showVal v2 = "V2"

tokS : Tok → String
tokS tIndent   = "  "
tokS tValT     = "val_t "
tokS (tObj n)  = "x" ++s primShowNat n
tokS (tCell n) = "*(mem + " ++s primShowNat n ++s ")"
tokS tPtr      = "val_t *p = malloc(sizeof(val_t)); *p"
tokS tAssign   = " = "
tokS (tLit x)  = showVal x
tokS tSemi     = ";"
tokS tNL       = "\n"

-- ==================================================================
-- THE PRINTER.  One line per statement.
-- ==================================================================

stmtToks : CStmt → List Tok
stmtToks cskip        = tIndent ∷ tSemi ∷ tNL ∷ []
stmtToks (cdecl l x)  =
  tIndent ∷ tValT ∷ tObj l ∷ tAssign ∷ tLit x ∷ tSemi ∷ tNL ∷ []
stmtToks (cstore l x) =
  tIndent ∷ tCell l ∷ tAssign ∷ tLit x ∷ tSemi ∷ tNL ∷ []
stmtToks (cmalloc x)  =
  tIndent ∷ tPtr ∷ tAssign ∷ tLit x ∷ tSemi ∷ tNL ∷ []

toks : CProg → List Tok
toks []      = []
toks (s ∷ p) = stmtToks s ++ toks p

-- ==================================================================
-- THE EDGE.  `render` is the only function below that produces a
-- `String`, and it consumes a token list, not a source term.
-- ==================================================================

render : List Tok → String
render []       = ""
render (t ∷ ts) = tokS t ++s render ts

body : CProg → String
body p = render (toks p)

preamble : String
preamble =
  "#include <stdlib.h>\n\ntypedef enum { V0, V1, V2 } val_t;\nstatic val_t mem[64];\n\nvoid frame(void) {\n"

epilogue : String
epilogue = "}\n"

emitUnit : CProg → String
emitUnit p = preamble ++s body p ++s epilogue

-- ==================================================================
-- OBSERVATION.  `refl` lines only.  These are about the PRINTER, not
-- about the compiler -- the compiled programs are printed in
-- `Compile.LinToC.Codegen`.
-- ==================================================================

_ : body (cdecl 0 v1 ∷ cdecl 2 v1 ∷ [])
  ≡ "  val_t x0 = V1;\n  val_t x2 = V1;\n"
_ = refl

_ : body [] ≡ ""
_ = refl

-- the aliasing program, printed.  It is legal C, and it looks it.
_ : body aliasC ≡ "  val_t x0 = V1;\n  *(mem + 0) = V1;\n"
_ = refl

_ : body (cmalloc v1 ∷ [])
  ≡ "  val_t *p = malloc(sizeof(val_t)); *p = V1;\n"
_ = refl
