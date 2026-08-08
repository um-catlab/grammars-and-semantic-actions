{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE EMITTED RUST, AS A PROGRAM THAT PRINTS ITS ANSWER.

  ------------------------------------------------------------------
  WHY `Codegen.renderUnit` IS NOT ENOUGH
  ------------------------------------------------------------------

  `Codegen.srcTm` emits

      enum U { A, B }

      fn main() {
          let _ = move |x0| x0;
      }

  and that unit has two defects as an EXECUTABLE.  The first is that it
  observes nothing -- the value is bound to `_`.  The second is fatal
  and was measured, not guessed: `rustc` REJECTS it,

      error[E0282]: type annotations needed
        --> id.rs:4:19
         |
       4 |     let _ = move |x0| x0;
         |                   ^^

  because an untyped λ has no Rust type.  A closure parameter must have
  one, and `x0` is used at whatever type its call site says.

  ------------------------------------------------------------------
  THE REPAIR: ONE UNIVERSAL VALUE TYPE
  ------------------------------------------------------------------

  The untyped λ-calculus has one type, so give it one:

      enum V { Fun(Box<dyn FnOnce(V) -> V>), Ctor(U) }

  and compile

      move |xn| e   ↦   V::Fun(Box::new(move |xn: V| e))
      (f)(a)        ↦   apply(f, a)
      U::A          ↦   V::Ctor(U::A)

  Two things about this are worth saying rather than assuming.

  `FnOnce`, NOT `Fn`.  A `Box<dyn FnOnce(V) -> V>` may be called AT MOST
  ONCE, and `move` takes every capture by value.  So the emitted program
  is not merely accepted by a borrow checker that tolerates linearity --
  it is accepted by the AFFINE discipline, which is the strongest thing
  `rustc` can be asked to confirm about this output.  A source term that
  used a variable twice would compile to Rust that moves out of a moved
  value, and `rustc` would reject it with E0382.  That is an INDEPENDENT
  check of `Use⊎`'s missing `(true,true)` constructor: the source type
  makes the bad term unwritable, and the target compiler makes the bad
  output unbuildable, and neither knows about the other.

  `show` IS THE COMMON OBSERVABLE.  `Compile/Suite/Backend.agda`'s

      data Val = vfun | vstuck

  is exactly the two shapes a `V` can have, so the string this program
  prints -- `fun` or `U::A`/`U::B` -- IS the row the Agda-side harness
  computes.  The runner compares them; nothing here has to be trusted.

  ------------------------------------------------------------------
  WHAT IS AND IS NOT PROVED
  ------------------------------------------------------------------

  `renderMain` is a RENDERER, phase 1, and no theorem here says the
  Rust program's answer is `evalRust`'s answer -- `rustc` is not in
  this development's trusted base and cannot be.  What the runner gets
  is a DIFFERENTIAL check between two independent implementations, plus
  the borrow checker's verdict on linearity.  §3 pins the emitted text
  by `refl`, which is the part that IS a theorem: the string the runner
  hands to `rustc` is the string this file says it is.

  PHASE.  Phase 1 throughout, and marked: `renderMain` recurses on a
  target expression, exactly as `Syntax.toks` does.  `mainTm` is the
  `⊢`-term that carries it, so the pipeline stays inside the calculus
  and `runAt` remains the only exit.
-}
open import Cubical.Foundations.Prelude

module Compile.LinToRust.Run where

open import Agda.Builtin.String using (String; primStringAppend; primShowNat)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.List using (List; []; _∷_)

open import Compile.LinToRust.Codegen
import TheoryGrammar.Instances.LinLam.Syntax as L

private
  infixr 5 _<>_
  _<>_ : String → String → String
  _<>_ = primStringAppend

-- ==================================================================
-- §1  THE PRELUDE.  Five declarations, fixed, and every emitted unit
-- carries the same one.
-- ==================================================================

prelude : String
prelude =
     "#![allow(dead_code, unused_parens, unused_variables)]\n"
  <> "\n"
  <> "enum U { A, B }\n"
  <> "\n"
  <> "// the ONE type an untyped linear lambda term has\n"
  <> "enum V { Fun(Box<dyn FnOnce(V) -> V>), Ctor(U) }\n"
  <> "\n"
  <> "fn apply(f: V, a: V) -> V {\n"
  <> "    match f { V::Fun(g) => g(a), V::Ctor(c) => { drop(a); V::Ctor(c) } }\n"
  <> "}\n"
  <> "\n"
  <> "// Compile/Suite/Backend.agda's `Val`, as a string\n"
  <> "fn show(v: &V) -> &'static str {\n"
  <> "    match v { V::Fun(_) => \"fun\",\n"
  <> "              V::Ctor(U::A) => \"U::A\",\n"
  <> "              V::Ctor(U::B) => \"U::B\" }\n"
  <> "}\n"
  <> "\n"

-- ==================================================================
-- §2  THE EXPRESSION.  PRIMITIVE (phase 1): a recursion on `RExpr`.
--
-- Six clauses, one per constructor, and `rMatch`/`rLet` are here for
-- totality only -- `Codegen.compileE` has three clauses and emits
-- neither.
-- ==================================================================

identR : Ident → String
identR (bnd n) = "x" <> primShowNat n
identR (fre n) = "y" <> primShowNat n

ctorR : Ctor → String
ctorR cA = "V::Ctor(U::A)"
ctorR cB = "V::Ctor(U::B)"

exprR : RExpr → String
exprR (rVar x)       = identR x
exprR (rClos n e)    = "V::Fun(Box::new(move |" <> identR (bnd n) <> ": V| "
                         <> exprR e <> "))"
exprR (rCall f a)    = "apply(" <> exprR f <> ", " <> exprR a <> ")"
exprR (rCtor c)      = ctorR c
exprR (rMatch s a b) =
     "match (" <> exprR s <> ") { V::Ctor(U::A) => " <> exprR a
  <> ", V::Ctor(U::B) => " <> exprR b
  <> ", V::Fun(g) => V::Fun(g) }"
exprR (rLet n e b)   =
  "{ let " <> identR (bnd n) <> ": V = " <> exprR e <> "; " <> exprR b <> " }"

-- ==================================================================
-- §3  THE UNIT.
-- ==================================================================

renderMain : RExpr → String
renderMain e =
     prelude
  <> "fn main() {\n"
  <> "    let r = " <> exprR e <> ";\n"
  <> "    println!(\"{}\", show(&r));\n"
  <> "}\n"

-- ... as a term of the calculus.  `Codegen.exprTm` is the `⊢`-term that
-- produces the expression; this only replaces the semantic action on
-- the far end of it, so no compilation happens here.
mainTm : L.TmG L.⊢ LA.Δ String
mainTm = LA.Δ-map renderMain L.∘g exprTm

-- ==================================================================
-- §4  THE OUTPUT, PINNED.  What the runner hands to `rustc`.
-- ==================================================================

-- the body of `main`, at the identity -- the whole unit is §1 plus this
_ : exprR (compileRust L.idLin) ≡ "V::Fun(Box::new(move |x0: V| x0))"
_ = refl

_ : exprR (compileRust L.selfApp)
  ≡ "apply(V::Fun(Box::new(move |x0: V| x0)), V::Fun(Box::new(move |x0: V| x0)))"
_ = refl

-- `λf. λx. f x` -- two binders, and the inner one is applied to the
-- outer one's variable, which is where `rustc` would object if the
-- source had used `x0` twice
_ : exprR (compileRust appLin)
  ≡ "V::Fun(Box::new(move |x0: V| V::Fun(Box::new(move |x1: V| apply(x0, x1)))))"
_ = refl
