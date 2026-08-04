{-
  The three basic algebraic effect theories, each with a parser for
  effect programs evaluating into its free model.

    Nondeterminism  `or`             — semilattice: associative,
                                       commutative, idempotent.  The free
                                       model is the free semilattice.

    Probability     `coin`           — the ½-fragment of a convex
                                       (barycentric) algebra: idempotent,
                                       commutative, medial.

    State           `get`, `set0/1`  — Plotkin–Power's theory of a single
                                       boolean cell: a binary `look` and a
                                       unary `put b`, with the four
                                       put/look equations.

  All three are instantiations of `Parser.Effects` over one alphabet, so
  programs are written the way code is:

    or(return 1, return 2)
    do s:=1; s:=0; return 3
    get(do s:=1; return 0, do s:=0; return 1)

  Multi-character keywords — `return`, `do`, `get`, `set0`, `s:=1`,
  `coin` — are single tokens, produced by the lexer below.
-}
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Examples.EffectTheories where

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
import Cubical.Data.Empty as Empty
import Cubical.Data.Sum as Sum
open Sum using (_⊎_)

open import Agda.Builtin.Char using (Char)
open import Agda.Builtin.String using (primStringToList)
  renaming (String to Str)

open import Algebra.Theory

-- Four variables are enough for every equation below.
data Vars : Type where
  v₀ v₁ v₂ v₃ : Vars

------------------------------------------------------------------------------
-- Nondeterminism: the theory of semilattices
------------------------------------------------------------------------------

data NDOp : Type where
  orOp : NDOp

NDSig : AlgTheorySig ℓ-zero ℓ-zero
NDSig = record { ops = NDOp ; arities = λ _ → Bool }

data NDEq : Type where
  ∪assoc ∪comm ∪idem : NDEq

private
  NDTm : Type
  NDTm = Tm NDSig Vars

  infixl 6 _∪t_
  _∪t_ : NDTm → NDTm → NDTm
  s ∪t t = tnode orOp (λ { true → s ; false → t })

  a b c : NDTm
  a = tvar v₀
  b = tvar v₁
  c = tvar v₂

  ndLhs ndRhs : NDEq → NDTm

  ndLhs ∪assoc = (a ∪t b) ∪t c
  ndLhs ∪comm = a ∪t b
  ndLhs ∪idem = a ∪t a

  ndRhs ∪assoc = a ∪t (b ∪t c)
  ndRhs ∪comm = b ∪t a
  ndRhs ∪idem = a

NDEqns : AlgTheoryEqns NDSig ℓ-zero ℓ-zero
NDEqns = record
  { eqns = NDEq ; vars = λ _ → Vars ; lhs = ndLhs ; rhs = ndRhs }

Mᴺ : Type
Mᴺ = FreeModel NDEqns ℕ

infixl 6 _∪̇_
_∪̇_ : Mᴺ → Mᴺ → Mᴺ
s ∪̇ t = node orOp (λ { true → s ; false → t })

∪Bridge : ∀ (g : Bool → Mᴺ) → node orOp g ≡ g true ∪̇ g false
∪Bridge g = cong (node orOp) (funExt (λ { true → refl ; false → refl }))

------------------------------------------------------------------------------
-- Probability: the ½-fragment of a convex algebra
--
-- Idempotent, commutative and medial.  (The full barycentric theory has
-- an operation `+ₚ` for every weight `p`; that version is expressible
-- here too — take `opG 0 = ⊕[ p ∈ W ] ＂ mix p ＂`, which the semantic
-- action can read, exactly as `≔` is read below — but its associativity
-- axiom needs arithmetic on the weights, so we stay with `p = ½`.)
------------------------------------------------------------------------------

data PrOp : Type where
  mixOp : PrOp

PrSig : AlgTheorySig ℓ-zero ℓ-zero
PrSig = record { ops = PrOp ; arities = λ _ → Bool }

data PrEq : Type where
  ⊞idem ⊞comm ⊞medial : PrEq

private
  PrTm : Type
  PrTm = Tm PrSig Vars

  infixl 6 _⊞t_
  _⊞t_ : PrTm → PrTm → PrTm
  s ⊞t t = tnode mixOp (λ { true → s ; false → t })

  p₀ p₁ p₂ p₃ : PrTm
  p₀ = tvar v₀
  p₁ = tvar v₁
  p₂ = tvar v₂
  p₃ = tvar v₃

  prLhs prRhs : PrEq → PrTm

  prLhs ⊞idem = p₀ ⊞t p₀
  prLhs ⊞comm = p₀ ⊞t p₁
  prLhs ⊞medial = (p₀ ⊞t p₁) ⊞t (p₂ ⊞t p₃)

  prRhs ⊞idem = p₀
  prRhs ⊞comm = p₁ ⊞t p₀
  prRhs ⊞medial = (p₀ ⊞t p₂) ⊞t (p₁ ⊞t p₃)

PrEqns : AlgTheoryEqns PrSig ℓ-zero ℓ-zero
PrEqns = record
  { eqns = PrEq ; vars = λ _ → Vars ; lhs = prLhs ; rhs = prRhs }

Mᴾ : Type
Mᴾ = FreeModel PrEqns ℕ

infixl 6 _⊞̇_
_⊞̇_ : Mᴾ → Mᴾ → Mᴾ
s ⊞̇ t = node mixOp (λ { true → s ; false → t })

⊞Bridge : ∀ (g : Bool → Mᴾ) → node mixOp g ≡ g true ⊞̇ g false
⊞Bridge g = cong (node mixOp) (funExt (λ { true → refl ; false → refl }))

------------------------------------------------------------------------------
-- State: Plotkin–Power's theory of a single boolean cell
--
-- `look x₀ x₁` reads the cell and continues with `x_b`; `put b` writes.
-- Note the mixed arities: `look` is binary, `put b` is unary.
------------------------------------------------------------------------------

data StOp : Type where
  lookOp : StOp
  putOp : Bool → StOp

StArity : StOp → Type
StArity lookOp = Bool
StArity (putOp _) = Unit

StSig : AlgTheorySig ℓ-zero ℓ-zero
StSig = record { ops = StOp ; arities = StArity }

data StEq : Type where
  put-put : Bool → Bool → StEq   -- writing twice: the second wins
  put-look : Bool → StEq         -- reading after a write is known
  look-put : StEq                -- writing back what you read is a no-op
  look-look : StEq               -- reading twice: the second is known

private
  StTm : Type
  StTm = Tm StSig Vars

  lookT : StTm → StTm → StTm
  lookT x₀ x₁ = tnode lookOp (λ { false → x₀ ; true → x₁ })

  putT : Bool → StTm → StTm
  putT β t = tnode (putOp β) (λ _ → t)

  w x y z : StTm
  w = tvar v₀
  x = tvar v₁
  y = tvar v₂
  z = tvar v₃

  stLhs stRhs : StEq → StTm

  stLhs (put-put β β') = putT β (putT β' w)
  stLhs (put-look β) = putT β (lookT x y)
  stLhs look-put = lookT (putT false w) (putT true w)
  stLhs look-look = lookT (lookT w x) (lookT y z)

  stRhs (put-put β β') = putT β' w
  stRhs (put-look false) = putT false x
  stRhs (put-look true) = putT true y
  stRhs look-put = w
  stRhs look-look = lookT w z

StEqns : AlgTheoryEqns StSig ℓ-zero ℓ-zero
StEqns = record
  { eqns = StEq ; vars = λ _ → Vars ; lhs = stLhs ; rhs = stRhs }

Mˢ : Type
Mˢ = FreeModel StEqns ℕ

lookM : Mˢ → Mˢ → Mˢ
lookM x₀ x₁ = node lookOp (λ { false → x₀ ; true → x₁ })

putM : Bool → Mˢ → Mˢ
putM β t = node (putOp β) (λ _ → t)

lookBridge : ∀ (g : Bool → Mˢ) → node lookOp g ≡ lookM (g false) (g true)
lookBridge g = cong (node lookOp) (funExt (λ { false → refl ; true → refl }))

------------------------------------------------------------------------------
-- Tokens
--
-- Keywords are single tokens; the lexer below is what turns the
-- characters `r` `e` `t` `u` `r` `n` into `kwReturn`.
------------------------------------------------------------------------------

data OpName : Type where
  getN set0N set1N orN coinN : OpName

data Tok : Type where
  lp rp : Tok               -- ( )
  comma semi : Tok          -- , ;
  kwReturn kwDo : Tok       -- return  do
  opTok : OpName → Tok      -- get  set0  set1  or  coin
  numeral : ℕ → Tok

private
  OpNameRep : Iso OpName ((Bool ⊎ Bool) ⊎ Unit)
  OpNameRep =
    iso
      (λ { getN → Sum.inl (Sum.inl true) ; set0N → Sum.inl (Sum.inl false)
         ; set1N → Sum.inl (Sum.inr true) ; orN → Sum.inl (Sum.inr false)
         ; coinN → Sum.inr tt })
      (λ { (Sum.inl (Sum.inl true)) → getN ; (Sum.inl (Sum.inl false)) → set0N
         ; (Sum.inl (Sum.inr true)) → set1N ; (Sum.inl (Sum.inr false)) → orN
         ; (Sum.inr tt) → coinN })
      (λ { (Sum.inl (Sum.inl true)) → refl ; (Sum.inl (Sum.inl false)) → refl
         ; (Sum.inl (Sum.inr true)) → refl ; (Sum.inl (Sum.inr false)) → refl
         ; (Sum.inr tt) → refl })
      (λ { getN → refl ; set0N → refl ; set1N → refl ; orN → refl
         ; coinN → refl })

  isSetOpName : isSet OpName
  isSetOpName =
    isSetRetract (Iso.fun OpNameRep) (Iso.inv OpNameRep) (Iso.ret OpNameRep)
      (Sum.isSet⊎ (Sum.isSet⊎ isSetBool isSetBool) isSetUnit)

  TokRep : Iso Tok (((Bool ⊎ Bool) ⊎ Bool) ⊎ (OpName ⊎ ℕ))
  TokRep =
    iso
      (λ { lp → Sum.inl (Sum.inl (Sum.inl true))
         ; rp → Sum.inl (Sum.inl (Sum.inl false))
         ; comma → Sum.inl (Sum.inl (Sum.inr true))
         ; semi → Sum.inl (Sum.inl (Sum.inr false))
         ; kwReturn → Sum.inl (Sum.inr true)
         ; kwDo → Sum.inl (Sum.inr false)
         ; (opTok o) → Sum.inr (Sum.inl o)
         ; (numeral n) → Sum.inr (Sum.inr n) })
      (λ { (Sum.inl (Sum.inl (Sum.inl true))) → lp
         ; (Sum.inl (Sum.inl (Sum.inl false))) → rp
         ; (Sum.inl (Sum.inl (Sum.inr true))) → comma
         ; (Sum.inl (Sum.inl (Sum.inr false))) → semi
         ; (Sum.inl (Sum.inr true)) → kwReturn
         ; (Sum.inl (Sum.inr false)) → kwDo
         ; (Sum.inr (Sum.inl o)) → opTok o
         ; (Sum.inr (Sum.inr n)) → numeral n })
      (λ { (Sum.inl (Sum.inl (Sum.inl true))) → refl
         ; (Sum.inl (Sum.inl (Sum.inl false))) → refl
         ; (Sum.inl (Sum.inl (Sum.inr true))) → refl
         ; (Sum.inl (Sum.inl (Sum.inr false))) → refl
         ; (Sum.inl (Sum.inr true)) → refl
         ; (Sum.inl (Sum.inr false)) → refl
         ; (Sum.inr (Sum.inl o)) → refl
         ; (Sum.inr (Sum.inr n)) → refl })
      (λ { lp → refl ; rp → refl ; comma → refl ; semi → refl
         ; kwReturn → refl ; kwDo → refl
         ; (opTok o) → refl ; (numeral n) → refl })

opaque
  isSetTok : isSet Tok
  isSetTok =
    isSetRetract (Iso.fun TokRep) (Iso.inv TokRep) (Iso.ret TokRep)
      (Sum.isSet⊎
        (Sum.isSet⊎ (Sum.isSet⊎ isSetBool isSetBool) isSetBool)
        (Sum.isSet⊎ isSetOpName isSetℕ))

Alphabet : hSet ℓ-zero
Alphabet = Tok , isSetTok

------------------------------------------------------------------------------
-- The lexer
--
-- Keywords are matched as character runs, so `":="` — or any other
-- multi-character symbol — is a single token.  `set0` and `s:=0` are two
-- spellings of the same one.  Numerals may have several digits;
-- whitespace and unrecognised characters are skipped.
------------------------------------------------------------------------------

private
  push : Mb.Maybe ℕ → ℕ → ℕ
  push Mb.nothing d = d
  push (Mb.just n) d = (10 Nat.· n) Nat.+ d

  flush : Mb.Maybe ℕ → List Tok → List Tok
  flush Mb.nothing ts = ts
  flush (Mb.just n) ts = numeral n ∷ ts

  lexGo : Mb.Maybe ℕ → List Char → List Tok
  lexGo acc [] = flush acc []
  lexGo acc ('r' ∷ 'e' ∷ 't' ∷ 'u' ∷ 'r' ∷ 'n' ∷ cs) =
    flush acc (kwReturn ∷ lexGo Mb.nothing cs)
  lexGo acc ('c' ∷ 'o' ∷ 'i' ∷ 'n' ∷ cs) =
    flush acc (opTok coinN ∷ lexGo Mb.nothing cs)
  lexGo acc ('s' ∷ 'e' ∷ 't' ∷ '0' ∷ cs) =
    flush acc (opTok set0N ∷ lexGo Mb.nothing cs)
  lexGo acc ('s' ∷ 'e' ∷ 't' ∷ '1' ∷ cs) =
    flush acc (opTok set1N ∷ lexGo Mb.nothing cs)
  lexGo acc ('s' ∷ ':' ∷ '=' ∷ '0' ∷ cs) =
    flush acc (opTok set0N ∷ lexGo Mb.nothing cs)
  lexGo acc ('s' ∷ ':' ∷ '=' ∷ '1' ∷ cs) =
    flush acc (opTok set1N ∷ lexGo Mb.nothing cs)
  lexGo acc ('g' ∷ 'e' ∷ 't' ∷ cs) =
    flush acc (opTok getN ∷ lexGo Mb.nothing cs)
  lexGo acc ('d' ∷ 'o' ∷ cs) = flush acc (kwDo ∷ lexGo Mb.nothing cs)
  lexGo acc ('o' ∷ 'r' ∷ cs) = flush acc (opTok orN ∷ lexGo Mb.nothing cs)
  lexGo acc ('(' ∷ cs) = flush acc (lp ∷ lexGo Mb.nothing cs)
  lexGo acc (')' ∷ cs) = flush acc (rp ∷ lexGo Mb.nothing cs)
  lexGo acc (',' ∷ cs) = flush acc (comma ∷ lexGo Mb.nothing cs)
  lexGo acc (';' ∷ cs) = flush acc (semi ∷ lexGo Mb.nothing cs)
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

open import Grammar Alphabet hiding (Δ)
open import Grammar.Maybe.Base Alphabet hiding (μ)
open import Grammar.SemanticAction Alphabet
open import Parser.Base Alphabet hiding (Parser)
open import Parser.RecursiveDescent Alphabet
open import Parser.Effects Alphabet
open import Term Alphabet

------------------------------------------------------------------------------
-- The vocabulary shared by all three languages
------------------------------------------------------------------------------

anyNum : Grammar ℓ-zero
anyNum = ⊕[ n ∈ ℕ ] ＂ numeral n ＂

isSetGrammarAnyNum : isSetGrammar anyNum
isSetGrammarAnyNum = isSetGrammar⊕ᴰ isSetℕ (λ _ → isSetGrammarLiteral _)

as-ret : (c : Tok) → Mb.Maybe (＂ c ＂ ⊢ ＂ kwReturn ＂)
as-ret kwReturn = Mb.just id
as-ret _ = Mb.nothing

as-do : (c : Tok) → Mb.Maybe (＂ c ＂ ⊢ ＂ kwDo ＂)
as-do kwDo = Mb.just id
as-do _ = Mb.nothing

as-open : (c : Tok) → Mb.Maybe (＂ c ＂ ⊢ ＂ lp ＂)
as-open lp = Mb.just id
as-open _ = Mb.nothing

as-close : (c : Tok) → Mb.Maybe (＂ c ＂ ⊢ ＂ rp ＂)
as-close rp = Mb.just id
as-close _ = Mb.nothing

as-sep : (c : Tok) → Mb.Maybe (＂ c ＂ ⊢ ＂ comma ＂)
as-sep comma = Mb.just id
as-sep _ = Mb.nothing

as-seq : (c : Tok) → Mb.Maybe (＂ c ＂ ⊢ ＂ semi ＂)
as-seq semi = Mb.just id
as-seq _ = Mb.nothing

as-val : (c : Tok) → Mb.Maybe (＂ c ＂ ⊢ anyNum)
as-val (numeral n) = Mb.just (σ n)
as-val _ = Mb.nothing

------------------------------------------------------------------------------
-- Nondeterminism: `or(M, N)`
------------------------------------------------------------------------------

NDOps : Ar → Type
NDOps ar0 = Empty.⊥
NDOps ar1 = Empty.⊥
NDOps ar2 = Unit

isSetNDOps : ∀ a → isSet (NDOps a)
isSetNDOps ar0 = isProp→isSet Empty.isProp⊥
isSetNDOps ar1 = isProp→isSet Empty.isProp⊥
isSetNDOps ar2 = isSetUnit

ndOpG : (a : Ar) → NDOps a → Grammar ℓ-zero
ndOpG ar0 ()
ndOpG ar1 ()
ndOpG ar2 tt = ＂ opTok orN ＂

isSetGrammarNdOpG : ∀ a (o : NDOps a) → isSetGrammar (ndOpG a o)
isSetGrammarNdOpG ar0 ()
isSetGrammarNdOpG ar1 ()
isSetGrammarNdOpG ar2 tt = isSetGrammarLiteral _

nd-as-op : (c : Tok)
  → Mb.Maybe (Σ[ a ∈ Ar ] Σ[ o ∈ NDOps a ] (＂ c ＂ ⊢ ndOpG a o))
nd-as-op (opTok orN) = Mb.just (ar2 , tt , id)
nd-as-op _ = Mb.nothing

ndSyntax : EffectSyntax
ndSyntax = record
  { Ops = NDOps ; isSetOps = isSetNDOps ; OpG = ndOpG
  ; RetG = ＂ kwReturn ＂ ; DoG = ＂ kwDo ＂
  ; OpenG = ＂ lp ＂ ; CloseG = ＂ rp ＂
  ; SepG = ＂ comma ＂ ; SeqG = ＂ semi ＂ ; ValG = anyNum
  ; isSetGrammarOpG = isSetGrammarNdOpG
  ; isSetGrammarRet = isSetGrammarLiteral _
  ; isSetGrammarDo = isSetGrammarLiteral _
  ; isSetGrammarOpen = isSetGrammarLiteral _
  ; isSetGrammarClose = isSetGrammarLiteral _
  ; isSetGrammarSep = isSetGrammarLiteral _
  ; isSetGrammarSeq = isSetGrammarLiteral _
  ; isSetGrammarVal = isSetGrammarAnyNum
  ; asRet = as-ret ; asDo = as-do ; asOpen = as-open ; asClose = as-close
  ; asSep = as-sep ; asSeq = as-seq ; asVal = as-val ; asOp = nd-as-op
  }

nd-val : SemanticAction anyNum Mᴺ
nd-val = semact-⊕ᴰ' (λ n → semact-pure (var n))

nd-op-sem : (a : Ar) (o : NDOps a) → Args a Mᴺ → Mᴺ
nd-op-sem ar0 ()
nd-op-sem ar1 ()
nd-op-sem ar2 tt (s , t) = s ∪̇ t

module ND = Effects ndSyntax
module NDSem = ND.Semantics Mᴺ nd-val nd-op-sem
module runND = RunIncompleteParser NDSem.evaluate

------------------------------------------------------------------------------
-- Probability: `coin(M, N)`
------------------------------------------------------------------------------

PrOps : Ar → Type
PrOps ar0 = Empty.⊥
PrOps ar1 = Empty.⊥
PrOps ar2 = Unit

isSetPrOps : ∀ a → isSet (PrOps a)
isSetPrOps ar0 = isProp→isSet Empty.isProp⊥
isSetPrOps ar1 = isProp→isSet Empty.isProp⊥
isSetPrOps ar2 = isSetUnit

prOpG : (a : Ar) → PrOps a → Grammar ℓ-zero
prOpG ar0 ()
prOpG ar1 ()
prOpG ar2 tt = ＂ opTok coinN ＂

isSetGrammarPrOpG : ∀ a (o : PrOps a) → isSetGrammar (prOpG a o)
isSetGrammarPrOpG ar0 ()
isSetGrammarPrOpG ar1 ()
isSetGrammarPrOpG ar2 tt = isSetGrammarLiteral _

pr-as-op : (c : Tok)
  → Mb.Maybe (Σ[ a ∈ Ar ] Σ[ o ∈ PrOps a ] (＂ c ＂ ⊢ prOpG a o))
pr-as-op (opTok coinN) = Mb.just (ar2 , tt , id)
pr-as-op _ = Mb.nothing

prSyntax : EffectSyntax
prSyntax = record
  { Ops = PrOps ; isSetOps = isSetPrOps ; OpG = prOpG
  ; RetG = ＂ kwReturn ＂ ; DoG = ＂ kwDo ＂
  ; OpenG = ＂ lp ＂ ; CloseG = ＂ rp ＂
  ; SepG = ＂ comma ＂ ; SeqG = ＂ semi ＂ ; ValG = anyNum
  ; isSetGrammarOpG = isSetGrammarPrOpG
  ; isSetGrammarRet = isSetGrammarLiteral _
  ; isSetGrammarDo = isSetGrammarLiteral _
  ; isSetGrammarOpen = isSetGrammarLiteral _
  ; isSetGrammarClose = isSetGrammarLiteral _
  ; isSetGrammarSep = isSetGrammarLiteral _
  ; isSetGrammarSeq = isSetGrammarLiteral _
  ; isSetGrammarVal = isSetGrammarAnyNum
  ; asRet = as-ret ; asDo = as-do ; asOpen = as-open ; asClose = as-close
  ; asSep = as-sep ; asSeq = as-seq ; asVal = as-val ; asOp = pr-as-op
  }

pr-val : SemanticAction anyNum Mᴾ
pr-val = semact-⊕ᴰ' (λ n → semact-pure (var n))

pr-op-sem : (a : Ar) (o : PrOps a) → Args a Mᴾ → Mᴾ
pr-op-sem ar0 ()
pr-op-sem ar1 ()
pr-op-sem ar2 tt (s , t) = s ⊞̇ t

module Pr = Effects prSyntax
module PrSem = Pr.Semantics Mᴾ pr-val pr-op-sem
module runPr = RunIncompleteParser PrSem.evaluate

------------------------------------------------------------------------------
-- State: `get(M, N)` and `set0` / `set1`
--
-- The writes are a Bool-indexed family of unary operations, so `Ops ar1`
-- is `Bool` and the parser hands the bit straight to the semantics.
------------------------------------------------------------------------------

StOps : Ar → Type
StOps ar0 = Empty.⊥
StOps ar1 = Bool
StOps ar2 = Unit

isSetStOps : ∀ a → isSet (StOps a)
isSetStOps ar0 = isProp→isSet Empty.isProp⊥
isSetStOps ar1 = isSetBool
isSetStOps ar2 = isSetUnit

stOpG : (a : Ar) → StOps a → Grammar ℓ-zero
stOpG ar0 ()
stOpG ar1 false = ＂ opTok set0N ＂
stOpG ar1 true = ＂ opTok set1N ＂
stOpG ar2 tt = ＂ opTok getN ＂

isSetGrammarStOpG : ∀ a (o : StOps a) → isSetGrammar (stOpG a o)
isSetGrammarStOpG ar0 ()
isSetGrammarStOpG ar1 false = isSetGrammarLiteral _
isSetGrammarStOpG ar1 true = isSetGrammarLiteral _
isSetGrammarStOpG ar2 tt = isSetGrammarLiteral _

st-as-op : (c : Tok)
  → Mb.Maybe (Σ[ a ∈ Ar ] Σ[ o ∈ StOps a ] (＂ c ＂ ⊢ stOpG a o))
st-as-op (opTok getN) = Mb.just (ar2 , tt , id)
st-as-op (opTok set0N) = Mb.just (ar1 , false , id)
st-as-op (opTok set1N) = Mb.just (ar1 , true , id)
st-as-op _ = Mb.nothing

stSyntax : EffectSyntax
stSyntax = record
  { Ops = StOps ; isSetOps = isSetStOps ; OpG = stOpG
  ; RetG = ＂ kwReturn ＂ ; DoG = ＂ kwDo ＂
  ; OpenG = ＂ lp ＂ ; CloseG = ＂ rp ＂
  ; SepG = ＂ comma ＂ ; SeqG = ＂ semi ＂ ; ValG = anyNum
  ; isSetGrammarOpG = isSetGrammarStOpG
  ; isSetGrammarRet = isSetGrammarLiteral _
  ; isSetGrammarDo = isSetGrammarLiteral _
  ; isSetGrammarOpen = isSetGrammarLiteral _
  ; isSetGrammarClose = isSetGrammarLiteral _
  ; isSetGrammarSep = isSetGrammarLiteral _
  ; isSetGrammarSeq = isSetGrammarLiteral _
  ; isSetGrammarVal = isSetGrammarAnyNum
  ; asRet = as-ret ; asDo = as-do ; asOpen = as-open ; asClose = as-close
  ; asSep = as-sep ; asSeq = as-seq ; asVal = as-val ; asOp = st-as-op
  }

st-val : SemanticAction anyNum Mˢ
st-val = semact-⊕ᴰ' (λ n → semact-pure (var n))

st-op-sem : (a : Ar) (o : StOps a) → Args a Mˢ → Mˢ
st-op-sem ar0 ()
st-op-sem ar1 β t = putM β t
st-op-sem ar2 tt (t₀ , t₁) = lookM t₀ t₁

module St = Effects stSyntax
module StSem = St.Semantics Mˢ st-val st-op-sem
module runSt = RunIncompleteParser StSem.evaluate

------------------------------------------------------------------------------
-- Tests: the programs compute at `refl`
------------------------------------------------------------------------------

opaque
  unfolding unfoldRecursiveDescentDefs

  -- Nondeterminism

  _ : runND.parse? (lex "return 1")
  _ = Sum.inl (var 1 , tt) , refl

  _ : runND.parse? (lex "or(return 1, return 2)")
  _ = Sum.inl (var 1 ∪̇ var 2 , tt) , refl

  _ : runND.parse? (lex "or(return 1, or(return 2, return 3))")
  _ = Sum.inl (var 1 ∪̇ (var 2 ∪̇ var 3) , tt) , refl

  _ : runND.parse? (lex "or(or(return 10, return 25), return 3)")
  _ = Sum.inl ((var 10 ∪̇ var 25) ∪̇ var 3 , tt) , refl

  _ : runND.parse? (lex "do or(return 1, return 2)")
  _ = Sum.inl (var 1 ∪̇ var 2 , tt) , refl

  _ : runND.parse? (lex "coin(return 1, return 2)")   -- not this signature
  _ = Sum.inr _ , refl

  -- Probability

  _ : runPr.parse? (lex "coin(return 1, return 2)")
  _ = Sum.inl (var 1 ⊞̇ var 2 , tt) , refl

  _ : runPr.parse? (lex "coin(coin(return 1, return 2), coin(return 3, return 4))")
  _ = Sum.inl ((var 1 ⊞̇ var 2) ⊞̇ (var 3 ⊞̇ var 4) , tt) , refl

  -- State

  _ : runSt.parse? (lex "get(return 0, return 1)")
  _ = Sum.inl (lookM (var 0) (var 1) , tt) , refl

  -- a unary operation, in statement form ...
  _ : runSt.parse? (lex "set1; return 5")
  _ = Sum.inl (putM true (var 5) , tt) , refl

  -- ... and in applied form
  _ : runSt.parse? (lex "set1(return 5)")
  _ = Sum.inl (putM true (var 5) , tt) , refl

  -- statements sequence, and `:=` is just another spelling
  _ : runSt.parse? (lex "do s:=1; s:=0; return 3")
  _ = Sum.inl (putM true (putM false (var 3)) , tt) , refl

  -- a block in each branch
  _ : runSt.parse? (lex "get(do s:=1; return 0, do s:=0; return 1)")
  _ = Sum.inl (lookM (putM true (var 0)) (putM false (var 1)) , tt) , refl

  _ : runSt.parse? (lex "(get(return 0, return 1))")
  _ = Sum.inl (lookM (var 0) (var 1) , tt) , refl

  -- Failures

  _ : runSt.parse? (lex "")
  _ = Sum.inr _ , refl

  _ : runSt.parse? (lex "return")           -- no value
  _ = Sum.inr _ , refl

  _ : runSt.parse? (lex "get(return 1)")    -- wrong arity
  _ = Sum.inr _ , refl

  _ : runSt.parse? (lex "get return 1")     -- missing the argument list
  _ = Sum.inr _ , refl

  _ : runSt.parse? (lex "set1 return 5")    -- missing the `;`
  _ = Sum.inr _ , refl

  _ : runSt.parse? (lex "get(return 0, return 1")   -- unclosed
  _ = Sum.inr _ , refl

------------------------------------------------------------------------------
-- The equations, as paths in the free models
------------------------------------------------------------------------------

-- Nondeterminism: `or(x, x)` and `x` are the same program.

∪-idem : ∀ (s : Mᴺ) → s ∪̇ s ≡ s
∪-idem s = sym (∪Bridge _) ∙ eqn ∪idem (λ _ → s)

∪-comm : ∀ (s t : Mᴺ) → s ∪̇ t ≡ t ∪̇ s
∪-comm s t = sym (∪Bridge _) ∙ eqn ∪comm ρ ∙ ∪Bridge _
  where
    ρ : Vars → Mᴺ
    ρ v₀ = s
    ρ v₁ = t
    ρ v₂ = s
    ρ v₃ = s

-- Probability: the fair coin is idempotent and unbiased.

⊞-idem : ∀ (s : Mᴾ) → s ⊞̇ s ≡ s
⊞-idem s = sym (⊞Bridge _) ∙ eqn ⊞idem (λ _ → s)

⊞-comm : ∀ (s t : Mᴾ) → s ⊞̇ t ≡ t ⊞̇ s
⊞-comm s t = sym (⊞Bridge _) ∙ eqn ⊞comm ρ ∙ ⊞Bridge _
  where
    ρ : Vars → Mᴾ
    ρ v₀ = s
    ρ v₁ = t
    ρ v₂ = s
    ρ v₃ = s

-- State: the second write wins, and writing back what you read is a
-- no-op.  `put` is unary, so `Unit`'s η makes the first of these hold
-- without any bridge.

set-set : ∀ (β β' : Bool) (s : Mˢ) → putM β (putM β' s) ≡ putM β' s
set-set β β' s = eqn (put-put β β') (λ _ → s)

get-set : ∀ (s : Mˢ) → lookM (putM false s) (putM true s) ≡ s
get-set s = sym (lookBridge _) ∙ eqn look-put (λ _ → s)

-- `or(return 1, return 1)` and `return 1` are the same program.
nd-programs-agree : var 1 ∪̇ var 1 ≡ var 1
nd-programs-agree = ∪-idem (var 1)

-- `coin(return 1, return 2)` and `coin(return 2, return 1)` are the same
-- distribution.
pr-programs-agree : var 1 ⊞̇ var 2 ≡ var 2 ⊞̇ var 1
pr-programs-agree = ⊞-comm (var 1) (var 2)

-- `do s:=1; s:=0; return 1` and `do s:=0; return 1` are the same
-- stateful program.
st-programs-agree : putM true (putM false (var 1)) ≡ putM false (var 1)
st-programs-agree = set-set true false (var 1)
