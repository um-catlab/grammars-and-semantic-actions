{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE LINEAR λ-CALCULUS WITH NUMBERS, IN RUST.

  `Compile/LinToRust/{Syntax,Eval,Codegen}.agda` at this source, with
  two constructors added to the target and two rules added to `_⇓_`, and
  `Compile/LinToRust/Run.agda`'s universal value type carrying a number
  as well as a closure:

      enum V { Fun(Box<dyn FnOnce(V) -> V>), Num(u64) }

  ------------------------------------------------------------------
  WHY THE RUST BACKEND IS THE ONE THAT ANSWERS A QUESTION
  ------------------------------------------------------------------

  It is the only backend here whose target has an INDEPENDENT checker.
  `Control.run` is this development's own model of AArch64, so
  `run-arm.sh` agreeing with it is a check of the emitter against the
  model and not of the model against a chip.  `rustc` is not ours.  And
  what it checks is exactly the property the source type system was
  built to express:

      every emitted closure is `move`      -- captures taken by value
      every emitted binder is used ONCE    -- because `Use⊎` said so
      `Box<dyn FnOnce(V) -> V>`            -- callable at most once

  so a term that duplicated a variable would emit Rust that moves out of
  a moved value and be rejected with E0382.  The source makes such a
  term unwritable; `rustc` makes such an output unbuildable; the two
  facts are established by different tools that know nothing about each
  other.  `tools/run-rust.sh` reports rustc's verdict separately from
  the answer for that reason.

  ------------------------------------------------------------------
  EVALUATION IS BY SUBSTITUTION, AND STAYS THAT WAY
  ------------------------------------------------------------------

  `LinToRust/Eval.agda` substitutes; `ClosureConv/IR.agda` passes
  environments.  `Compile/Relational/Refutation.agda` is the record of
  what that difference costs (level-based naming is not stable under
  substitution), and adding numbers does not touch it: `rNum` is closed
  and `rAdd` is a congruence, so neither new rule mentions a binder.

  PHASE.  Phase 1 throughout, and marked: `substE`, `_⇓_`, `evalR`,
  `compileE` and the renderer all recurse on syntax.
-}
open import Cubical.Foundations.Prelude

module Compile.LinNum.Rust where

open import Agda.Builtin.String using (String; primStringAppend; primShowNat)
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Bool using (Bool; true; false; if_then_else_; _and_)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Sigma using (Σ-syntax; _×_; _,_; fst; snd)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

import TheoryGrammar.Instances.LinLam.Syntax as L
open import Compile.LinNum.Syntax
open import Compile.ClosureConv.IR using (slotOf)

private
  infixr 5 _<>_
  _<>_ : String → String → String
  _<>_ = primStringAppend

-- ==================================================================
-- §1  THE TARGET.
-- ==================================================================

data Ident : Type₀ where
  bnd : ℕ → Ident        -- `xN`, a λ-binder at LEVEL N
  fre : ℕ → Ident        -- `yN`, a free variable of the initial context

data RE : Type₀ where
  rVar  : Ident → RE
  rClos : ℕ → RE → RE          -- `move |xn: V| e`
  rCall : RE → RE → RE         -- `apply(f, a)`
  rNum  : ℕ → RE               -- `V::Num(n)`          -- NEW
  rAdd  : RE → RE → RE         -- `add(a, b)`          -- NEW

-- the two shapes a VALUE has, which is `Compile/LinToRust/Syntax`'s
-- `IsVal` with `valNum` where `valCtor` was
data IsVal : RE → Type₀ where
  valClos : (n : ℕ) (e : RE) → IsVal (rClos n e)
  valNum  : (n : ℕ)          → IsVal (rNum n)

eqℕ : ℕ → ℕ → Bool
eqℕ zero    zero    = true
eqℕ zero    (suc _) = false
eqℕ (suc _) zero    = false
eqℕ (suc m) (suc n) = eqℕ m n

eqIdent : Ident → Ident → Bool
eqIdent (bnd m) (bnd n) = eqℕ m n
eqIdent (fre m) (fre n) = eqℕ m n
eqIdent (bnd _) (fre _) = false
eqIdent (fre _) (bnd _) = false

-- PRIMITIVE (phase 1): substitution.  Capture-free because binders are
-- LEVELS -- distinct binders have distinct names by construction.
substE : Ident → RE → RE → RE
substE x v (rVar y)     = if eqIdent x y then v else rVar y
substE x v (rClos n b)  = rClos n (substE x v b)
substE x v (rCall f a)  = rCall (substE x v f) (substE x v a)
substE x v (rNum n)     = rNum n
substE x v (rAdd a b)   = rAdd (substE x v a) (substE x v b)

-- ==================================================================
-- §2  THE BIG-STEP RELATION.  Five rules; `⇓num` is immediate and
-- `⇓add` is the only new recursion.  PRIMITIVE (phase 1).
-- ==================================================================

infix 4 _⇓_

data _⇓_ : RE → RE → Type₀ where
  ⇓clos : (n : ℕ) (b : RE) → rClos n b ⇓ rClos n b
  ⇓num  : (n : ℕ)          → rNum n ⇓ rNum n
  ⇓call : ∀ {f a n b va w}
        → f ⇓ rClos n b → a ⇓ va → substE (bnd n) va b ⇓ w
        → rCall f a ⇓ w
  ⇓add  : ∀ {a b m n}
        → a ⇓ rNum m → b ⇓ rNum n
        → rAdd a b ⇓ rNum (m + n)

-- ==================================================================
-- §3  THE EXECUTABLE EVALUATOR, carrying its own derivation -- so that
-- a `refl` computation IS a derivation, exactly as in `LinToRust/Eval`.
-- ==================================================================

Result : RE → Type₀
Result e = Maybe (Σ[ v ∈ RE ] (e ⇓ v))

private
  bindD : {e : RE} {P : RE → Type₀}
        → ({w : RE} → e ⇓ w → P w) → Result e → Maybe (Σ[ v ∈ RE ] P v)
  bindD f nothing        = nothing
  bindD f (just (v , d)) = just (v , f d)

evalR  : (k : ℕ) (e : RE) → Result e
evCall : (k : ℕ) {f a : RE} → Result f → Result a → Result (rCall f a)
evApp  : (k : ℕ) {f a : RE} (v : RE) → f ⇓ v → Result a → Result (rCall f a)
evAdd  : (k : ℕ) {a b : RE} → Result a → Result b → Result (rAdd a b)
evSum  : (k : ℕ) {a b : RE} (v : RE) → a ⇓ v → Result b → Result (rAdd a b)

-- PRIMITIVE (phase 1)
evalR zero    e           = nothing
evalR (suc k) (rVar x)    = nothing              -- stuck: free variable
evalR (suc k) (rClos n b) = just (rClos n b , ⇓clos n b)
evalR (suc k) (rNum n)    = just (rNum n   , ⇓num n)
evalR (suc k) (rCall f a) = evCall k (evalR k f) (evalR k a)
evalR (suc k) (rAdd a b)  = evAdd  k (evalR k a) (evalR k b)

evCall k nothing        ra = nothing
evCall k (just (v , d)) ra = evApp k v d ra

evApp k (rVar _)     df ra = nothing
evApp k (rCall _ _)  df ra = nothing
evApp k (rAdd _ _)   df ra = nothing
evApp k (rNum _)     df ra = nothing            -- calling a number
evApp k (rClos n b)  df nothing         = nothing
evApp k (rClos n b)  df (just (va , da)) =
  bindD (λ d → ⇓call df da d) (evalR k (substE (bnd n) va b))

evAdd k nothing        rb = nothing
evAdd k (just (v , d)) rb = evSum k v d rb

evSum k (rVar _)    da rb = nothing
evSum k (rClos _ _) da rb = nothing             -- adding a closure
evSum k (rCall _ _) da rb = nothing
evSum k (rAdd _ _)  da rb = nothing
evSum k (rNum m)    da nothing = nothing
evSum k (rNum m)    da (just (rVar _    , db)) = nothing
evSum k (rNum m)    da (just (rClos _ _ , db)) = nothing
evSum k (rNum m)    da (just (rCall _ _ , db)) = nothing
evSum k (rNum m)    da (just (rAdd _ _  , db)) = nothing
evSum k (rNum m)    da (just (rNum n    , db)) = just (rNum (m + n) , ⇓add da db)

valOf : {e : RE} → Result e → Maybe RE
valOf nothing        = nothing
valOf (just (v , _)) = just v

-- the number, if the answer is one
numR : Maybe RE → Maybe ℕ
numR (just (rNum n)) = just n
numR _               = nothing

-- ==================================================================
-- §4  THE CODE GENERATOR.  PRIMITIVE (phase 1): one recursion on
-- `NTm`, five clauses.  `d` is the number of enclosing binders, so a
-- binder's NAME is its level and `nameOf` needs no arithmetic.
-- ==================================================================

nameOf : ℕ → ℕ → Ident
nameOf zero    p       = fre p
nameOf (suc d) zero    = bnd d
nameOf (suc d) (suc p) = nameOf d p

compileE : ℕ → {u : Usage} → NTm u → RE
compileE d (nvar {u} s)    = rVar (nameOf d (slotOf 0 u s))
compileE d (nlam b)        = rClos d (compileE (suc d) b)
compileE d (napp _ f a)    = rCall (compileE d f) (compileE d a)
compileE d (nlit _ n)      = rNum n
compileE d (nadd _ a b)    = rAdd (compileE d a) (compileE d b)

compileRust : {u : Usage} → NTm u → RE
compileRust = compileE 0

-- the Rust answer, and the number in it
rustAns : NTm [] → Maybe RE
rustAns t = valOf (evalR 60 (compileRust t))

rustNum : NTm [] → Maybe ℕ
rustNum t = numR (rustAns t)

-- ==================================================================
-- §5  RENDERING.  Two of them: the EXPRESSION alone (which is what a
-- table shows) and a whole `main.rs` that PRINTS its answer.
-- ==================================================================

identR : Ident → String
identR (bnd n) = "x" <> primShowNat n
identR (fre n) = "y" <> primShowNat n

-- the surface syntax, for reading -- `move |x0| x0`, `(f)(a)`, `a + b`
showE : RE → String
showE (rVar x)    = identR x
showE (rClos n e) = "move |" <> identR (bnd n) <> "| " <> showE e
showE (rCall f a) = "(" <> showE f <> ")(" <> showE a <> ")"
showE (rNum n)    = primShowNat n
showE (rAdd a b)  = "(" <> showE a <> " + " <> showE b <> ")"

showM : Maybe RE → String
showM nothing  = "TIMEOUT"
showM (just e) = showE e

-- WHAT THE EMITTED PROGRAM WILL PRINT.  `show` in the prelude below is
-- this function, transliterated: a closure prints `fun`, a number
-- prints itself.  So the runner compares two strings and neither side
-- had to be told about the other.
showPrinted : Maybe RE → String
showPrinted nothing            = "TIMEOUT"
showPrinted (just (rNum n))    = primShowNat n
showPrinted (just (rClos _ _)) = "fun"
showPrinted (just (rVar _))    = "STUCK"
showPrinted (just (rCall _ _)) = "STUCK"
showPrinted (just (rAdd _ _))  = "STUCK"

-- the RUST, in the universal value type
exprR : RE → String
exprR (rVar x)    = identR x
exprR (rClos n e) = "V::Fun(Box::new(move |" <> identR (bnd n) <> ": V| "
                      <> exprR e <> "))"
exprR (rCall f a) = "apply(" <> exprR f <> ", " <> exprR a <> ")"
exprR (rNum n)    = "V::Num(" <> primShowNat n <> ")"
exprR (rAdd a b)  = "add(" <> exprR a <> ", " <> exprR b <> ")"

prelude : String
prelude =
     "#![allow(dead_code, unused_parens, unused_variables)]\n"
  <> "\n"
  <> "// the ONE type an untyped linear lambda term with numbers has\n"
  <> "enum V { Fun(Box<dyn FnOnce(V) -> V>), Num(u64) }\n"
  <> "\n"
  <> "fn apply(f: V, a: V) -> V {\n"
  <> "    match f { V::Fun(g) => g(a), V::Num(n) => { drop(a); V::Num(n) } }\n"
  <> "}\n"
  <> "\n"
  <> "fn add(a: V, b: V) -> V {\n"
  <> "    match (a, b) {\n"
  <> "        (V::Num(m), V::Num(n)) => V::Num(m + n),\n"
  <> "        (x, y) => { drop(x); drop(y); V::Num(0) }\n"
  <> "    }\n"
  <> "}\n"
  <> "\n"
  <> "fn show(v: &V) -> String {\n"
  <> "    match v { V::Fun(_) => \"fun\".to_string(), V::Num(n) => n.to_string() }\n"
  <> "}\n"
  <> "\n"

renderMain : RE → String
renderMain e =
     prelude
  <> "fn main() {\n"
  <> "    let r = " <> exprR e <> ";\n"
  <> "    println!(\"{}\", show(&r));\n"
  <> "}\n"

srcOf : NTm [] → String
srcOf t = renderMain (compileRust t)

-- ==================================================================
-- §6  IT COMPUTES, AND IT COMPUTES 42.
-- ==================================================================

_ : compileRust incApp Eq.≡ rCall (rClos 0 (rAdd (rVar (bnd 0)) (rNum 1))) (rNum 41)
_ = Eq.refl

_ : showE (compileRust incApp) Eq.≡ "(move |x0| (x0 + 1))(41)"
_ = Eq.refl

-- THE TARGET, in the third backend
_ : rustNum incApp Eq.≡ just 42
_ = Eq.refl

_ : rustNum sum42    Eq.≡ just 42
_ = Eq.refl

_ : rustNum addApp   Eq.≡ just 42
_ = Eq.refl

_ : rustNum applyInc Eq.≡ just 42
_ = Eq.refl

_ : rustNum sum143   Eq.≡ just 143
_ = Eq.refl

-- ... and the DERIVATION, extracted from that computation
incDeriv : compileRust incApp ⇓ rNum 42
incDeriv = ⇓call (⇓clos 0 (rAdd (rVar (bnd 0)) (rNum 1)))
                 (⇓num 41)
                 (⇓add (⇓num 41) (⇓num 1))

-- a λ is still a closure, and `rustNum` says so
_ : rustNum inc Eq.≡ nothing
_ = Eq.refl

_ : rustAns inc Eq.≡ just (rClos 0 (rAdd (rVar (bnd 0)) (rNum 1)))
_ = Eq.refl

-- ==================================================================
-- §7  THE EMITTED RUST, PINNED.  These are the lines the runner hands
-- to `rustc`; `tools/run-rust.sh incApp` prints 42.
-- ==================================================================

_ : exprR (compileRust incApp)
  Eq.≡ "apply(V::Fun(Box::new(move |x0: V| add(x0, V::Num(1)))), V::Num(41))"
_ = Eq.refl

_ : exprR (compileRust addApp)
  Eq.≡ "apply(apply(V::Fun(Box::new(move |x0: V| V::Fun(Box::new(move |x1: V| add(x0, x1))))), V::Num(40)), V::Num(2))"
_ = Eq.refl

-- the OLD language, embedded, emits what `LinToRust/Run.agda` emits for
-- it -- modulo `Ctor`, which this target replaced with `Num`
_ : exprR (compileRust (fromTm L.idLin))
  Eq.≡ "V::Fun(Box::new(move |x0: V| x0))"
_ = Eq.refl
