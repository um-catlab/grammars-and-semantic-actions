{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE PURE FUNCTIONAL FRAGMENT OF RUST, AND ITS PRETTY-PRINTER.

  ------------------------------------------------------------------
  WHY THIS FRAGMENT
  ------------------------------------------------------------------

  Compiling the linear λ-calculus into Rust's PURE fragment is close to
  the identity translation, and that is the point:

      tvar  ↦  a variable
      tlam  ↦  a closure   `move |x0| BODY`
      tapp  ↦  a call      `(F)(A)`

  Nothing is allocated, nothing is mutated, and no heap is mentioned
  anywhere in this file or the two that follow it.  The correctness
  statement downstream is an equation between VALUES.

  ------------------------------------------------------------------
  OWNERSHIP: WHY `rustc` ACCEPTS THE OUTPUT, AS A THEOREM
  ------------------------------------------------------------------

  Rust's ownership discipline is AFFINE: a value has exactly one owner,
  a `move` invalidates the source, and a value MAY be dropped.  It is
  not linear -- nothing forces a binding to be used.

  `TheoryGrammar.Instances.Affine.Contrast` proves both halves of the
  comparison this backend rests on:

      linTm→aff : Tm u → ATm u     -- every LINEAR term is an affine
                                      term, at the SAME usage
      lin⊊aff                       -- and strictly: `adrop`, the
                                      splitting where the whole owns a
                                      variable and neither premise
                                      claims it, is affine but not
                                      linear

  So the source's discipline is a SUBSET of the target's, and the extra
  affine constructor is exactly the one that would force a `drop`.  In
  the pure fragment this argument is sharper than in an allocating one:

    * NOTHING IS DROPPED.  `adrop` is absent from `Use⊎`, so every
      bound name is consumed.  No `Drop`, no dead `let`.
    * NOTHING IS ALIASED.  `tapp` carries a `Use⊎`, so the two premises
      of a call own DISJOINT sets of names -- `Codegen.linScope` turns
      that into the statement that the emitted expression uses each
      name exactly once.  No `&`, no `&mut`, no `Rc`, no `Clone`.
    * Hence every closure is a `move` closure and every capture is a
      move of a uniquely-owned value, which is precisely the case the
      borrow checker admits without a lifetime.

  HONEST CAVEAT, CHECKED AGAINST A REAL `rustc`.  The output is
  syntactically Rust and satisfies Rust's OWNERSHIP discipline for the
  reason above.  It does NOT in general satisfy Rust's TYPE inference:
  the source calculus is untyped, and closure parameters carry no
  annotation, so `rustc` reports E0282 ("type annotations needed") on
  the emitted units -- a TYPE error, reached after parsing and name
  resolution, and never E0425 ("cannot find value").  Feeding `rustc`
  the same terms with the one annotation it asks for separates the two
  claims cleanly:

      let _ = (move |x0: U| x0)(U::A);           -- compiles, and runs

      let _ = (move |x0: U|                      -- x0 used TWICE:
                 ((move |x1: U| move |_x2: U| x1)(x0))(x0))(U::A);
                                                 -- E0382, use of moved
                                                 --   value `x0`

  The second is the compilation of a NON-linear term, and `rustc`
  rejects it for exactly the reason `Use⊎` has no `(true,true)`
  constructor.  So the ownership claim is not decorative: the borrow
  checker really is the thing linearity is buying, and it bites the
  moment linearity is dropped.  Typing is a further constraint this
  file deliberately does not model; giving the untyped λ-calculus a
  Rust type needs a universal domain (`enum V { …, F(Box<dyn Fn(V) ->
  V>) }`), which would reintroduce the allocation this fragment exists
  to avoid.

  ------------------------------------------------------------------
  THE FRAGMENT, AND WHAT IS DELIBERATELY LEFT OUT
  ------------------------------------------------------------------

      rVar x            `x0` / `y0`
      rClos n e         `move |xn| e`
      rCall f a         `(f)(a)`
      rCtor c           `U::A` / `U::B`      -- one `enum U { A, B }`
      rMatch s a b      `match (s) { U::A => (a), U::B => (b) }`
      rLet n e b        `{ let xn = e; b }`  -- IMMUTABLE let

  `enum`, `match` and `let` are in the fragment because the target was
  specified as the pure functional fragment, and they are what makes it
  OBSERVABLE: without a base type there is no closed value to compare,
  and every equation would be between closures.  `Eval`'s tests apply
  compiled terms to `U::A` and read the answer back.

  Deliberately absent:

    * `mut`, `&mut`, interior mutability, `Box`, `Vec`, `Rc` -- the
      whole allocating half.  (`Compile.LinToRust.Alloc` is the
      separate, heap-based backend; it is a different specification and
      does not import this file or vice versa.)
    * `&T` borrows and LIFETIMES.  A borrow is a non-owning shared
      view; the affine promodel's splitting has no room for one, and
      the linear source never asks for one.
    * `while` / `loop` / recursion.  There is no `fn` item in the
      fragment at all, so there is nothing to recur into; the source
      calculus has no fixed point either.
    * generics, traits, `impl` blocks, modules.
    * type ANNOTATIONS on closures.  See the caveat above.

  ------------------------------------------------------------------
  NAMES
  ------------------------------------------------------------------

  Two kinds of identifier, and the distinction is load-bearing:

      bnd n   `xn`   a λ-binder, named by its LEVEL (0 = outermost)
      fre n   `yn`   the n-th free variable of the initial context

  Levels rather than de Bruijn indices, because Rust source has names:
  with levels a binder's name never changes as one descends, no two
  nested binders collide, and no source variable ever SHADOWS another.
  That in turn is what makes the naive substitution in `Eval` correct.
  `Codegen.nameOf` is the (three-clause, arithmetic-free) translation
  from "depth `d`, de Bruijn index `p`" to one of these.

  ------------------------------------------------------------------
  THE PRINTER
  ------------------------------------------------------------------

  A `List Tok` where each token carries its own trailing separator,
  then `render = foldr primStringAppend ""`.  No layout decisions, so
  no case on neighbours, so every test is a `refl`.  Calls and match
  scrutinees are FULLY PARENTHESISED, which costs nothing and removes
  every precedence question -- `(move |x0| x0)(U::A)` is unambiguous
  Rust however it is nested.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1 throughout, and marked: this is a language being DEFINED and
  a pass being BUILT (matches on `Tok`, on `RExpr`, on `Ident`).  The
  `⊢`-level producers that consume it live in `Codegen` and are
  composites of `Δ-map`, `⊕ᴰ-E` and `∘g`.
-}
open import Cubical.Foundations.Prelude

module Compile.LinToRust.Syntax where

open import Agda.Builtin.String using (String; primStringAppend; primShowNat)
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.List using (List; []; _∷_; _++_)
open import Cubical.Data.Unit
open import Cubical.Data.Empty as E using (⊥)

-- ==================================================================
-- IDENTIFIERS.
-- ==================================================================

data Ident : Type₀ where
  bnd : ℕ → Ident        -- `xN`, a λ-binder at level N
  fre : ℕ → Ident        -- `yN`, a free variable of the initial context

-- PRIMITIVE (phase 1): Unit/⊥-valued equality on levels, in the style
-- of `Heap/Base.Diff` -- so a proof is a `tt` and never blocks a `refl`.
Same : ℕ → ℕ → Type₀
Same zero    zero    = Unit
Same zero    (suc _) = ⊥
Same (suc _) zero    = ⊥
Same (suc m) (suc n) = Same m n

-- PRIMITIVE (phase 1): ... and its decision, as a `Bool`, which is what
-- substitution needs.
eqℕ : ℕ → ℕ → Bool
eqℕ zero    zero    = true
eqℕ zero    (suc _) = false
eqℕ (suc _) zero    = false
eqℕ (suc m) (suc n) = eqℕ m n

-- PRIMITIVE (phase 1)
eqIdent : Ident → Ident → Bool
eqIdent (bnd m) (bnd n) = eqℕ m n
eqIdent (fre m) (fre n) = eqℕ m n
eqIdent (bnd _) (fre _) = false
eqIdent (fre _) (bnd _) = false

-- ==================================================================
-- THE ONE ENUM, AND THE EXPRESSIONS.
-- ==================================================================

-- `enum U { A, B }`
data Ctor : Type₀ where
  cA cB : Ctor

data RExpr : Type₀ where
  rVar   : Ident → RExpr
  rClos  : ℕ → RExpr → RExpr                  -- `move |xn| e`
  rCall  : RExpr → RExpr → RExpr              -- `(f)(a)`
  rCtor  : Ctor → RExpr                       -- `U::A`
  rMatch : RExpr → RExpr → RExpr → RExpr      -- `match (s) { … }`
  rLet   : ℕ → RExpr → RExpr → RExpr          -- `{ let xn = e; b }`

-- the weak head normal forms: a closure or a constructor.  These are
-- the only closed expressions `Eval` can stop at, and they are exactly
-- Rust's two kinds of owned value in this fragment.
data IsVal : RExpr → Type₀ where
  valClos : (n : ℕ) (e : RExpr) → IsVal (rClos n e)
  valCtor : (c : Ctor)          → IsVal (rCtor c)

RValue : Type₀
RValue = Σ[ e ∈ RExpr ] IsVal e

-- ==================================================================
-- TOKENS.  Each carries its own trailing separator, so `render` is a
-- concatenation and nothing else.
-- ==================================================================

data Tok : Type₀ where
  kEnumDecl : Tok        -- `enum U { A, B }` and a blank line
  kFnOpen   : Tok        -- `fn main() {` and a newline
  kFnClose  : Tok        -- `}` and a newline
  kIndent   : Tok        -- four spaces
  kLetAnon  : Tok        -- `let _ = `
  kSemi     : Tok        -- `;` and a newline
  kMove     : Tok        -- `move |`
  kBarSp    : Tok        -- `| `
  kOpen     : Tok        -- `(`
  kClose    : Tok        -- `)`
  kMatch    : Tok        -- `match `
  kArmsOpen : Tok        -- ` { `
  kArmA     : Tok        -- `U::A => `
  kArmB     : Tok        -- `U::B => `
  kComma    : Tok        -- `, `
  kArmsEnd  : Tok        -- ` }`
  kBlkOpen  : Tok        -- `{ let `
  kEq       : Tok        -- ` = `
  kBlkMid   : Tok        -- `; `
  kBlkEnd   : Tok        -- ` }`
  ctorTok   : Ctor → Tok -- `U::A` / `U::B`
  identTok  : Ident → Tok

-- PRIMITIVE (phase 1): the spelling tables.
ctorStr : Ctor → String
ctorStr cA = "U::A"
ctorStr cB = "U::B"

identStr : Ident → String
identStr (bnd n) = primStringAppend "x" (primShowNat n)
identStr (fre n) = primStringAppend "y" (primShowNat n)

-- PRIMITIVE (phase 1)
tokStr : Tok → String
tokStr kEnumDecl     = "enum U { A, B }\n\n"
tokStr kFnOpen       = "fn main() {\n"
tokStr kFnClose      = "}\n"
tokStr kIndent       = "    "
tokStr kLetAnon      = "let _ = "
tokStr kSemi         = ";\n"
tokStr kMove         = "move |"
tokStr kBarSp        = "| "
tokStr kOpen         = "("
tokStr kClose        = ")"
tokStr kMatch        = "match "
tokStr kArmsOpen     = " { "
tokStr kArmA         = "U::A => "
tokStr kArmB         = "U::B => "
tokStr kComma        = ", "
tokStr kArmsEnd      = " }"
tokStr kBlkOpen      = "{ let "
tokStr kEq           = " = "
tokStr kBlkMid       = "; "
tokStr kBlkEnd       = " }"
tokStr (ctorTok c)   = ctorStr c
tokStr (identTok x)  = identStr x

-- ==================================================================
-- THE LAYOUT.  PRIMITIVE (phase 1): structural on `RExpr`.
-- Every call and every scrutinee is parenthesised, so precedence never
-- enters and the printer never inspects a subterm's shape.
-- ==================================================================

toks : RExpr → List Tok
toks (rVar x)      = identTok x ∷ []
toks (rClos n e)   = kMove ∷ identTok (bnd n) ∷ kBarSp ∷ toks e
toks (rCall f a)   =
  kOpen ∷ (toks f ++ (kClose ∷ kOpen ∷ (toks a ++ (kClose ∷ []))))
toks (rCtor c)     = ctorTok c ∷ []
toks (rMatch s a b) =
  kMatch ∷ kOpen ∷ (toks s ++ (kClose ∷ kArmsOpen ∷ kArmA ∷
    (toks a ++ (kComma ∷ kArmB ∷ (toks b ++ (kArmsEnd ∷ []))))))
toks (rLet n e b)  =
  kBlkOpen ∷ identTok (bnd n) ∷ kEq ∷
    (toks e ++ (kBlkMid ∷ (toks b ++ (kBlkEnd ∷ []))))

-- a whole compilation unit: the enum declaration and one `main`
toksUnit : RExpr → List Tok
toksUnit e =
  kEnumDecl ∷ kFnOpen ∷ kIndent ∷ kLetAnon ∷ (toks e ++ (kSemi ∷ kFnClose ∷ []))

-- ==================================================================
-- ... AND THE EDGE.  The only string operation in the backend.
-- ==================================================================

-- PRIMITIVE (phase 1)
render : List Tok → String
render []       = ""
render (t ∷ ts) = primStringAppend (tokStr t) (render ts)

-- the emitted expression, on its own
renderExpr : RExpr → String
renderExpr e = render (toks e)

-- ... and as a compilation unit `rustc` would accept
renderUnit : RExpr → String
renderUnit e = render (toksUnit e)

-- ==================================================================
-- OBSERVATION.  That the printer reduces; the tests that matter -- the
-- Rust emitted for an actual linear λ-term -- are in `Codegen`.
-- ==================================================================

_ : renderExpr (rClos 0 (rVar (bnd 0))) ≡ "move |x0| x0"
_ = refl

_ : renderExpr (rCall (rClos 0 (rVar (bnd 0))) (rCtor cA))
  ≡ "(move |x0| x0)(U::A)"
_ = refl

_ : renderExpr (rMatch (rVar (fre 0)) (rCtor cB) (rCtor cA))
  ≡ "match (y0) { U::A => U::B, U::B => U::A }"
_ = refl

_ : renderExpr (rLet 3 (rCtor cA) (rVar (bnd 3)))
  ≡ "{ let x3 = U::A; x3 }"
_ = refl

_ : renderUnit (rClos 0 (rVar (bnd 0)))
  ≡ "enum U { A, B }\n\nfn main() {\n    let _ = move |x0| x0;\n}\n"
_ = refl
