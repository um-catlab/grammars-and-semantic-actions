{-
  Two precedence parsers, as instantiations of `Parser.Precedence`.

  `Free`  — `·` binding tighter than `+`, with the semantic action landing
            in the *free model* of an algebraic theory on ℕ-many constants.
            Because the target is the free model rather than a syntax
            tree, the theory's equations are available as paths: `1 + 2`
            and `2 + 1` parse to provably equal elements, and so do
            `1 · (2 + 3)` and `1 · 2 + 1 · 3`.

  `Arith` — the same tokens with three levels, `+` < `·` < `^`, evaluated
            into ℕ.  Same construction, different spec.

  The theory layer lives in `Algebra.Theory`, copied from
  cubical-categorical-logic's `alg-theory` branch.
-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Examples.AlgebraicTheory where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Nat as Nat using (ℕ ; zero ; suc ; isSetℕ)
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import Cubical.Data.Maybe as Mb
import Cubical.Data.Sum as Sum
open Sum using (_⊎_)

open import Agda.Builtin.Char using (Char)
open import Agda.Builtin.String using (primStringToList)
  renaming (String to Str)

open import Algebra.Theory

------------------------------------------------------------------------------
-- The theory: two binary operations, `⊹` commutative and associative,
-- `⊙` associative and distributing over `⊹` on both sides.
------------------------------------------------------------------------------

data Op : Type where
  ⊹ ⊙ : Op

Arity : Op → Type
Arity _ = Bool

ExprSig : AlgTheorySig ℓ-zero ℓ-zero
ExprSig = record { ops = Op ; arities = Arity }

data Eqn : Type where
  ⊹assoc ⊹comm ⊙assoc ⊙distL ⊙distR : Eqn

-- Every equation of this theory uses (at most) three variables.
data Vars : Type where
  vx vy vz : Vars

private
  Trm : Type
  Trm = Tm ExprSig Vars

  _t⊹_ _t⊙_ : Trm → Trm → Trm
  s t⊹ t = tnode ⊹ (λ { true → s ; false → t })
  s t⊙ t = tnode ⊙ (λ { true → s ; false → t })

  infixl 6 _t⊹_
  infixl 7 _t⊙_

  x y z : Trm
  x = tvar vx
  y = tvar vy
  z = tvar vz

  eqLhs eqRhs : Eqn → Trm

  eqLhs ⊹assoc = (x t⊹ y) t⊹ z
  eqLhs ⊹comm = x t⊹ y
  eqLhs ⊙assoc = (x t⊙ y) t⊙ z
  eqLhs ⊙distL = x t⊙ (y t⊹ z)
  eqLhs ⊙distR = (x t⊹ y) t⊙ z

  eqRhs ⊹assoc = x t⊹ (y t⊹ z)
  eqRhs ⊹comm = y t⊹ x
  eqRhs ⊙assoc = x t⊙ (y t⊙ z)
  eqRhs ⊙distL = (x t⊙ y) t⊹ (x t⊙ z)
  eqRhs ⊙distR = (x t⊙ z) t⊹ (y t⊙ z)

ExprEqns : AlgTheoryEqns ExprSig ℓ-zero ℓ-zero
ExprEqns = record
  { eqns = Eqn ; vars = λ _ → Vars ; lhs = eqLhs ; rhs = eqRhs }

-- The semantic domain: the free model on ℕ-many constants.
M : Type
M = FreeModel ExprEqns ℕ

mk : Op → M → M → M
mk op s t = node op (λ { true → s ; false → t })

infixl 6 _⊹̇_
infixl 7 _⊙̇_

_⊹̇_ _⊙̇_ : M → M → M
_⊹̇_ = mk ⊹
_⊙̇_ = mk ⊙

-- `TmRec` always produces `node op (λ a → …)`, never the `mk`-shape the
-- semantic action builds; this is the bridge between the two (cf.
-- `compBridge` in Cubical.Algebra.Instances.FreeCategory).
nodeBridge : ∀ (op : Op) (g : Bool → M) → node op g ≡ mk op (g true) (g false)
nodeBridge op g = cong (node op) (funExt (λ { true → refl ; false → refl }))

------------------------------------------------------------------------------
-- Tokens
------------------------------------------------------------------------------

data Tok : Type where
  [ ] : Tok       -- brackets
  + · ^ : Tok     -- the binary operators, loosest to tightest
  num : ℕ → Tok   -- constants

open Iso
opaque
  TokRep : Iso Tok (((Bool ⊎ Bool) ⊎ Unit) ⊎ ℕ)
  TokRep =
    iso
      (λ { [ → Sum.inl (Sum.inl (Sum.inl true))
         ; ] → Sum.inl (Sum.inl (Sum.inl false))
         ; + → Sum.inl (Sum.inl (Sum.inr true))
         ; · → Sum.inl (Sum.inl (Sum.inr false))
         ; ^ → Sum.inl (Sum.inr tt)
         ; (num n) → Sum.inr n })
      (λ { (Sum.inl (Sum.inl (Sum.inl true))) → [
         ; (Sum.inl (Sum.inl (Sum.inl false))) → ]
         ; (Sum.inl (Sum.inl (Sum.inr true))) → +
         ; (Sum.inl (Sum.inl (Sum.inr false))) → ·
         ; (Sum.inl (Sum.inr tt)) → ^
         ; (Sum.inr n) → num n })
      (λ { (Sum.inl (Sum.inl (Sum.inl true))) → refl
         ; (Sum.inl (Sum.inl (Sum.inl false))) → refl
         ; (Sum.inl (Sum.inl (Sum.inr true))) → refl
         ; (Sum.inl (Sum.inl (Sum.inr false))) → refl
         ; (Sum.inl (Sum.inr tt)) → refl
         ; (Sum.inr n) → refl })
      (λ { [ → refl ; ] → refl ; + → refl ; · → refl ; ^ → refl
         ; (num n) → refl })

  isSetTok : isSet Tok
  isSetTok =
    isSetRetract (TokRep .fun) (TokRep .inv) (TokRep .ret)
      (Sum.isSet⊎ (Sum.isSet⊎ (Sum.isSet⊎ isSetBool isSetBool) isSetUnit) isSetℕ)

Alphabet : hSet ℓ-zero
Alphabet = Tok , isSetTok

------------------------------------------------------------------------------
-- Concrete syntax
--
-- A one-pass lexer, so the tests below can be written as strings rather
-- than as token lists.  Numerals may have several digits; whitespace and
-- unknown characters are skipped.  It is structurally recursive on the
-- character list, and every character literal reduces during
-- typechecking, so `lex "1 + 2"` is just a token list as far as the
-- parser is concerned.
------------------------------------------------------------------------------

private
  push : Mb.Maybe ℕ → ℕ → ℕ
  push Mb.nothing d = d
  push (Mb.just n) d = (10 Nat.· n) Nat.+ d

  flush : Mb.Maybe ℕ → List Tok → List Tok
  flush Mb.nothing ts = ts
  flush (Mb.just n) ts = num n ∷ ts

  lexGo : Mb.Maybe ℕ → List Char → List Tok
  lexGo acc [] = flush acc []
  lexGo acc ('(' ∷ cs) = flush acc ([ ∷ lexGo Mb.nothing cs)
  lexGo acc (')' ∷ cs) = flush acc (] ∷ lexGo Mb.nothing cs)
  lexGo acc ('[' ∷ cs) = flush acc ([ ∷ lexGo Mb.nothing cs)
  lexGo acc (']' ∷ cs) = flush acc (] ∷ lexGo Mb.nothing cs)
  lexGo acc ('+' ∷ cs) = flush acc (+ ∷ lexGo Mb.nothing cs)
  lexGo acc ('·' ∷ cs) = flush acc (· ∷ lexGo Mb.nothing cs)
  lexGo acc ('^' ∷ cs) = flush acc (^ ∷ lexGo Mb.nothing cs)
  lexGo acc ('0' ∷ cs) = lexGo (Mb.just (push acc 0)) cs
  lexGo acc ('1' ∷ cs) = lexGo (Mb.just (push acc 1)) cs
  lexGo acc ('2' ∷ cs) = lexGo (Mb.just (push acc 2)) cs
  lexGo acc ('3' ∷ cs) = lexGo (Mb.just (push acc 3)) cs
  lexGo acc ('4' ∷ cs) = lexGo (Mb.just (push acc 4)) cs
  lexGo acc ('5' ∷ cs) = lexGo (Mb.just (push acc 5)) cs
  lexGo acc ('6' ∷ cs) = lexGo (Mb.just (push acc 6)) cs
  lexGo acc ('7' ∷ cs) = lexGo (Mb.just (push acc 7)) cs
  lexGo acc ('8' ∷ cs) = lexGo (Mb.just (push acc 8)) cs
  lexGo acc ('9' ∷ cs) = lexGo (Mb.just (push acc 9)) cs
  lexGo acc (_ ∷ cs) = flush acc (lexGo Mb.nothing cs)

lex : Str → List Tok
lex s = lexGo Mb.nothing (primStringToList s)

open import Grammar Alphabet hiding (Δ ; _+)
open import Grammar.Bottom.Initial Alphabet using (isSetGrammar⊥*)
open import Grammar.Maybe.Base Alphabet hiding (μ)
open import Grammar.SemanticAction Alphabet
open import Parser.Base Alphabet hiding (Parser)
open import Parser.RecursiveDescent Alphabet
open import Parser.Precedence Alphabet
open import Term Alphabet

------------------------------------------------------------------------------
-- The pieces shared by both instantiations
------------------------------------------------------------------------------

anyNum : Grammar ℓ-zero
anyNum = ⊕[ n ∈ ℕ ] ＂ num n ＂

isSetGrammarAnyNum : isSetGrammar anyNum
isSetGrammarAnyNum = isSetGrammar⊕ᴰ isSetℕ (λ _ → isSetGrammarLiteral _)

as-num : (c : Tok) → Mb.Maybe (＂ c ＂ ⊢ anyNum)
as-num (num n) = Mb.just (σ n)
as-num _ = Mb.nothing

as-open : (c : Tok) → Mb.Maybe (＂ c ＂ ⊢ ＂ [ ＂)
as-open [ = Mb.just id
as-open _ = Mb.nothing

as-close : (c : Tok) → Mb.Maybe (＂ c ＂ ⊢ ＂ ] ＂)
as-close ] = Mb.just id
as-close _ = Mb.nothing

------------------------------------------------------------------------------
-- Instantiation 1: `·` tighter than `+`, evaluated in the free model
------------------------------------------------------------------------------

freeOp : ℕ → Grammar ℓ-zero
freeOp zero = ＂ · ＂
freeOp (suc zero) = ＂ + ＂
freeOp (suc (suc _)) = ⊥*

isSetGrammarFreeOp : ∀ i → isSetGrammar (freeOp i)
isSetGrammarFreeOp zero = isSetGrammarLiteral _
isSetGrammarFreeOp (suc zero) = isSetGrammarLiteral _
isSetGrammarFreeOp (suc (suc _)) = isSetGrammar⊥*

free-as-op : (c : Tok) (i : ℕ) → Mb.Maybe (＂ c ＂ ⊢ freeOp i)
free-as-op · zero = Mb.just id
free-as-op + (suc zero) = Mb.just id
free-as-op _ _ = Mb.nothing

freeSpec : PrecedenceSpec
freeSpec = record
  { nLevels = 2
  ; opG = freeOp
  ; LeafG = anyNum
  ; OpenG = ＂ [ ＂
  ; CloseG = ＂ ] ＂
  ; PrefixG = ⊥*
  ; isSetGrammarOp = isSetGrammarFreeOp
  ; isSetGrammarLeaf = isSetGrammarAnyNum
  ; isSetGrammarOpen = isSetGrammarLiteral _
  ; isSetGrammarClose = isSetGrammarLiteral _
  ; isSetGrammarPrefix = isSetGrammar⊥*
  ; asOp = free-as-op
  ; asLeaf = as-num
  ; asOpen = as-open
  ; asClose = as-close
  ; asPrefix = λ _ → Mb.nothing
  }

free-leaf : SemanticAction anyNum M
free-leaf = semact-⊕ᴰ' (λ n → semact-pure (var n))

free-op : (i : ℕ) → SemanticAction (freeOp i) (M → M → M)
free-op zero = semact-pure _⊙̇_
free-op (suc zero) = semact-pure _⊹̇_
free-op (suc (suc _)) = semact-⊥*

module Free = Precedence freeSpec
module FreeSem = Free.Semantics M free-leaf semact-⊥* free-op

module runFree = RunIncompleteParser FreeSem.evaluate
module partialFree = RunIncompleteParser FreeSem.partial

------------------------------------------------------------------------------
-- Instantiation 2: three levels, `+` < `·` < `^`, evaluated in ℕ
------------------------------------------------------------------------------

pow : ℕ → ℕ → ℕ
pow m zero = 1
pow m (suc n) = m Nat.· pow m n

arithOp : ℕ → Grammar ℓ-zero
arithOp zero = ＂ ^ ＂
arithOp (suc zero) = ＂ · ＂
arithOp (suc (suc zero)) = ＂ + ＂
arithOp (suc (suc (suc _))) = ⊥*

isSetGrammarArithOp : ∀ i → isSetGrammar (arithOp i)
isSetGrammarArithOp zero = isSetGrammarLiteral _
isSetGrammarArithOp (suc zero) = isSetGrammarLiteral _
isSetGrammarArithOp (suc (suc zero)) = isSetGrammarLiteral _
isSetGrammarArithOp (suc (suc (suc _))) = isSetGrammar⊥*

arith-as-op : (c : Tok) (i : ℕ) → Mb.Maybe (＂ c ＂ ⊢ arithOp i)
arith-as-op ^ zero = Mb.just id
arith-as-op · (suc zero) = Mb.just id
arith-as-op + (suc (suc zero)) = Mb.just id
arith-as-op _ _ = Mb.nothing

arithSpec : PrecedenceSpec
arithSpec = record
  { nLevels = 3
  ; opG = arithOp
  ; LeafG = anyNum
  ; OpenG = ＂ [ ＂
  ; CloseG = ＂ ] ＂
  ; PrefixG = ⊥*
  ; isSetGrammarOp = isSetGrammarArithOp
  ; isSetGrammarLeaf = isSetGrammarAnyNum
  ; isSetGrammarOpen = isSetGrammarLiteral _
  ; isSetGrammarClose = isSetGrammarLiteral _
  ; isSetGrammarPrefix = isSetGrammar⊥*
  ; asOp = arith-as-op
  ; asLeaf = as-num
  ; asOpen = as-open
  ; asClose = as-close
  ; asPrefix = λ _ → Mb.nothing
  }

arith-leaf : SemanticAction anyNum ℕ
arith-leaf = semact-⊕ᴰ' (λ n → semact-pure n)

arith-op : (i : ℕ) → SemanticAction (arithOp i) (ℕ → ℕ → ℕ)
arith-op zero = semact-pure pow
arith-op (suc zero) = semact-pure Nat._·_
arith-op (suc (suc zero)) = semact-pure Nat._+_
arith-op (suc (suc (suc _))) = semact-⊥*

module Arith = Precedence arithSpec
module ArithSem = Arith.Semantics ℕ arith-leaf semact-⊥* arith-op

module runArith = RunIncompleteParser ArithSem.evaluate

------------------------------------------------------------------------------
-- Tests: both parsers compute at `refl`
------------------------------------------------------------------------------

opaque
  unfolding unfoldRecursiveDescentDefs

  -- Free model: successes

  _ : runFree.parse? (lex "1")
  _ = Sum.inl (var 1 , tt) , refl

  _ : runFree.parse? (lex "1 + 2")
  _ = Sum.inl (var 1 ⊹̇ var 2 , tt) , refl

  _ : runFree.parse? (lex "1 · 2")
  _ = Sum.inl (var 1 ⊙̇ var 2 , tt) , refl

  _ : runFree.parse? (lex "10 + 25")
  _ = Sum.inl (var 10 ⊹̇ var 25 , tt) , refl

  -- `·` binds tighter than `+`, on both sides
  _ : runFree.parse? (lex "1 + 2 · 3")
  _ = Sum.inl (var 1 ⊹̇ var 2 ⊙̇ var 3 , tt) , refl

  _ : runFree.parse? (lex "1 · 2 + 3")
  _ = Sum.inl (var 1 ⊙̇ var 2 ⊹̇ var 3 , tt) , refl

  -- brackets override the precedence
  _ : runFree.parse? (lex "(1 + 2) · 3")
  _ = Sum.inl ((var 1 ⊹̇ var 2) ⊙̇ var 3 , tt) , refl

  _ : runFree.parse? (lex "1 · (2 + 3)")
  _ = Sum.inl (var 1 ⊙̇ (var 2 ⊹̇ var 3) , tt) , refl

  -- both operators associate to the right in the syntax
  _ : runFree.parse? (lex "1 + 2 + 3")
  _ = Sum.inl (var 1 ⊹̇ (var 2 ⊹̇ var 3) , tt) , refl

  -- `^` is not an operator of this spec, so it is not accepted
  _ : runFree.parse? (lex "1 ^ 2")
  _ = Sum.inr _ , refl

  -- Free model: failures

  _ : runFree.parse? (lex "")
  _ = Sum.inr _ , refl

  _ : runFree.parse? (lex "+")
  _ = Sum.inr _ , refl

  _ : runFree.parse? (lex ")")
  _ = Sum.inr _ , refl

  _ : runFree.parse? (lex "1 ·")
  _ = Sum.inr _ , refl

  _ : runFree.parse? (lex "(1")
  _ = Sum.inr _ , refl

  -- Free model: partial parses with leftover input

  _ : partialFree.parse? (lex "1 2")
  _ = Sum.inl ((var 1 , lex "2") , tt) , refl

  _ : partialFree.parse? (lex "1 · 2)")
  _ = Sum.inl ((var 1 ⊙̇ var 2 , lex ")") , tt) , refl

  -- Three-level arithmetic: the same construction, a different spec

  _ : runArith.parse? (lex "2 + 3 · 4")
  _ = Sum.inl (14 , tt) , refl

  _ : runArith.parse? (lex "2 · 3 ^ 2")
  _ = Sum.inl (18 , tt) , refl

  _ : runArith.parse? (lex "(2 + 3) · 4")
  _ = Sum.inl (20 , tt) , refl

  _ : runArith.parse? (lex "2 ^ 3 ^ 2")
  _ = Sum.inl (512 , tt) , refl

------------------------------------------------------------------------------
-- What the free model buys over an AST: the theory's equations are paths,
-- so parses that differ syntactically can be proved equal.
------------------------------------------------------------------------------

⊹-comm : ∀ (s t : M) → s ⊹̇ t ≡ t ⊹̇ s
⊹-comm s t = sym (nodeBridge ⊹ _) ∙ eqn ⊹comm ρ ∙ nodeBridge ⊹ _
  where
    ρ : Vars → M
    ρ vx = s
    ρ vy = t
    ρ vz = s

⊹-assoc : ∀ (s t u : M) → (s ⊹̇ t) ⊹̇ u ≡ s ⊹̇ (t ⊹̇ u)
⊹-assoc s t u =
  sym (nodeBridge ⊹ _ ∙ cong (_⊹̇ u) (nodeBridge ⊹ _))
  ∙ eqn ⊹assoc ρ
  ∙ nodeBridge ⊹ _
  ∙ cong (s ⊹̇_) (nodeBridge ⊹ _)
  where
    ρ : Vars → M
    ρ vx = s
    ρ vy = t
    ρ vz = u

⊙-distL : ∀ (s t u : M) → s ⊙̇ (t ⊹̇ u) ≡ (s ⊙̇ t) ⊹̇ (s ⊙̇ u)
⊙-distL s t u =
  sym (nodeBridge ⊙ _ ∙ cong (s ⊙̇_) (nodeBridge ⊹ _))
  ∙ eqn ⊙distL ρ
  ∙ nodeBridge ⊹ _
  ∙ cong₂ _⊹̇_ (nodeBridge ⊙ _) (nodeBridge ⊙ _)
  where
    ρ : Vars → M
    ρ vx = s
    ρ vy = t
    ρ vz = u

-- `1 + 2` and `2 + 1` parse to the same element of the free model.
parses-agree : var 1 ⊹̇ var 2 ≡ var 2 ⊹̇ var 1
parses-agree = ⊹-comm (var 1) (var 2)

-- and so do `1 · (2 + 3)` and `1 · 2 + 1 · 3`.
distributed-parses-agree :
  var 1 ⊙̇ (var 2 ⊹̇ var 3) ≡ (var 1 ⊙̇ var 2) ⊹̇ (var 1 ⊙̇ var 3)
distributed-parses-agree = ⊙-distL (var 1) (var 2) (var 3)
