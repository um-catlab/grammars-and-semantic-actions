{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE PRETTY-PRINTER: FROM THE STATEMENT MODEL TO REAL RUST SOURCE.

  `Compile.LinToRust.Alloc.Machine` fixes what a Rust program MEANS (a command
  over `heapFib`).  This file fixes what it LOOKS LIKE, and nothing
  else: it is a monoid homomorphism from program text to token lists,
  followed by a concatenation.

  ------------------------------------------------------------------
  WHY TOKENS, AND WHY THE TOKENS CARRY THEIR OWN SPACING
  ------------------------------------------------------------------

  The house constraint is that every test in this backend must be a
  `refl`, i.e. the emitted source must REDUCE.  Two consequences:

    * The intermediate representation is a `List Tok` over a small
      inductive `Tok`, so the interesting equation -- "these are the
      statements, in this order, at these addresses" -- is checkable
      without any string primitive at all (`toksProg` tests below).

    * `render` is then a plain `foldr primStringAppend ""`.  It does no
      layout: each token's spelling already contains whatever space,
      colon or newline follows it (`kLet = "let "`, `kColon = ": "`,
      `kSemi = ";\n"`).  A separator-aware pretty-printer would have to
      case on the neighbours, and every such case is one more thing
      standing between a test and its `refl`.

  `primStringAppend` computes on literals, and `primShowNat` computes on
  numerals, so `renderProg` of a closed program is a closed `String`
  literal and the source-level tests below are `refl` too.  Numbers are
  the ONLY thing computed rather than looked up, and they are the
  addresses -- which is the one part of the output the compiler actually
  chooses.

  ------------------------------------------------------------------
  THE SHAPE OF THE OUTPUT
  ------------------------------------------------------------------

  A program is one function body, because program text here is the free
  monoid on statements and a monoid is a body, not a module:

      fn frame() {
          let x0: Box<u8> = Box::new(1u8);
          let x2: Box<u8> = Box::new(1u8);
      }

  `x0`, `x2` are the LIVE variable positions of the source usage, and
  the missing `x1` is a dead position -- `LinLam/Codegen.lay`'s address
  gap, surviving all the way to the source text.  Every binding is
  `Box<u8>`, an OWNING allocation; there is no borrow, no `Rc`, no
  `Clone` and no `drop`, and `Machine`'s header says why that is a
  theorem about the source rather than a restriction of the printer.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1 throughout, and marked: this is a pass being BUILT (recursion
  on the carrier of program text, a match on `Tok`, a match on `Val`),
  not a program in the calculus.  The `⊢`-level producer that consumes
  it -- `Codegen.srcTm : TmG ⊢ Δ String` -- is phase 2 and is a
  composite of `Δ-map`, `⊕ᴰ-E` and `∘g`.
-}
open import Cubical.Foundations.Prelude

module Compile.LinToRust.Alloc.Emit where

open import Agda.Builtin.String using (String; primStringAppend; primShowNat)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.List using (List; []; _∷_; _++_)

open import Compile.LinToRust.Alloc.Machine

-- ==================================================================
-- TOKENS.  Each carries its own trailing separator, so `render` is a
-- concatenation and nothing else.
-- ==================================================================

data Tok : Type₀ where
  kFnOpen  : Tok        -- `fn frame() {` and a newline
  kFnClose : Tok        -- `}` and a newline
  kIndent  : Tok        -- four spaces
  kLet     : Tok        -- `let `
  kAnon    : Tok        -- `_`
  kColon   : Tok        -- `: `
  kBoxTy   : Tok        -- `Box<u8>`
  kAssign  : Tok        -- ` = `
  kBoxNew  : Tok        -- `Box::new(`
  kClose   : Tok        -- `)`
  kSemi    : Tok        -- `;` and a newline
  kUnitE   : Tok        -- `()`
  ident    : ℕ → Tok    -- `xN`
  litU8    : Val → Tok  -- `Nu8`

-- PRIMITIVE (phase 1): the spelling table.
valLit : Val → String
valLit v0 = "0u8"
valLit v1 = "1u8"
valLit v2 = "2u8"

-- PRIMITIVE (phase 1)
tokStr : Tok → String
tokStr kFnOpen    = "fn frame() {\n"
tokStr kFnClose   = "}\n"
tokStr kIndent    = "    "
tokStr kLet       = "let "
tokStr kAnon      = "_"
tokStr kColon     = ": "
tokStr kBoxTy     = "Box<u8>"
tokStr kAssign    = " = "
tokStr kBoxNew    = "Box::new("
tokStr kClose     = ")"
tokStr kSemi      = ";\n"
tokStr kUnitE     = "()"
tokStr (ident n)  = primStringAppend "x" (primShowNat n)
tokStr (litU8 x)  = valLit x

-- ==================================================================
-- THE HOMOMORPHISM.  One statement, one line.
-- ==================================================================

-- PRIMITIVE (phase 1): the layout of a single statement.
toks : RStmt → List Tok
toks unitS      = kIndent ∷ kUnitE ∷ kSemi ∷ []
toks (letS l x) =
  kIndent ∷ kLet ∷ ident l ∷ kColon ∷ kBoxTy ∷ kAssign
         ∷ kBoxNew ∷ litU8 x ∷ kClose ∷ kSemi ∷ []
toks (boxS x)   =
  kIndent ∷ kLet ∷ kAnon ∷ kAssign
         ∷ kBoxNew ∷ litU8 x ∷ kClose ∷ kSemi ∷ []

-- PRIMITIVE (phase 1): the extension along the universal property of
-- the free monoid.  `toksBody` is a monoid homomorphism
-- `RustProg → List Tok` -- concatenation to concatenation -- which is
-- what makes `render (p ++ q)` the two renderings in order.
toksBody : RustProg → List Tok
toksBody []      = []
toksBody (s ∷ p) = toks s ++ toksBody p

toksProg : RustProg → List Tok
toksProg p = kFnOpen ∷ (toksBody p ++ kFnClose ∷ [])

-- ==================================================================
-- ... AND THE EDGE.  The only string operation in the backend.
-- ==================================================================

-- PRIMITIVE (phase 1)
render : List Tok → String
render []       = ""
render (t ∷ ts) = primStringAppend (tokStr t) (render ts)

renderProg : RustProg → String
renderProg p = render (toksProg p)

-- ==================================================================
-- OBSERVATION.  That the printer itself reduces; the tests that matter
-- -- the Rust emitted for an actual linear λ-term -- are in `Codegen`.
-- ==================================================================

_ : renderProg [] ≡ "fn frame() {\n}\n"
_ = refl

_ : renderProg (letS 0 v1 ∷ [])
  ≡ "fn frame() {\n    let x0: Box<u8> = Box::new(1u8);\n}\n"
_ = refl

-- the address really is computed: `letS 2` prints `x2`
_ : renderProg (letS 2 v1 ∷ [])
  ≡ "fn frame() {\n    let x2: Box<u8> = Box::new(1u8);\n}\n"
_ = refl

-- the allocator-chosen box, and the unit statement
_ : renderProg (boxS v0 ∷ unitS ∷ [])
  ≡ "fn frame() {\n    let _ = Box::new(0u8);\n    ();\n}\n"
_ = refl
