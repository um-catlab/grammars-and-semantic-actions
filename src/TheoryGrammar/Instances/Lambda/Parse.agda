{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  AN INTRINSICALLY SCOPED PARSER FOR THE LAMBDA CALCULUS.

  `Lambda.Scoped` indexes a derivation by a SCOPE, but over the carrier
  of raw ASTs: the tree is already built and `Scoped Γ` says it is
  well-scoped.  This file does the same thing one stage earlier, over
  SPANS OF A WORD, so the object being classified is a piece of concrete
  syntax and the thing produced is a PARSE TREE.

  THE IDEA, IN ONE LINE: take the scope to be the NON-TERMINAL.

      Deriv (trm Γ) s   DENOTES  "the span `s` parses as a lambda term
                                  all of whose free names lie in Γ"

  so `Deriv (trm [])` is the grammar of CLOSED terms.  A parse tree
  containing an unbound variable is not rejected by a later pass -- it is
  UNSTATABLE, because the only rule that can produce a variable is

      trm Γ → 'n'      when   n ∈ Γ            (`unitR`, via `TokIn`)

  and at Γ = [] the side condition is `⊥`.  `no-free-var` below is that
  observation as a one-line theorem, and it is a fact about the GRAMMAR:
  it mentions no word and no decision procedure.

  Dually `¬G (Deriv (trm []))` is the grammar of PROOFS that a span has
  no closed reading, and `Decide.derives?` is a term
  `⊤G ⊢ Deriv P ⊕ ¬G (Deriv P)`, so a rejection is a theorem rather than
  a report.  `Lambda.ParseTests` extracts both directions.

  WHERE THE BINDER LIVES.  Everything about scope is in the INDEX of the
  recursive occurrence:

      rApp Γ  :  trm Γ → trm Γ  trm Γ            -- application
      rLam Γ n:  trm Γ → binder n  trm (n ∷ Γ)   -- λn. <body>

  `rLam` is the whole point: the token `binder n` fixes WHICH name is
  bound, and the body's non-terminal is `trm (n ∷ Γ)`.  This is the CYK
  rule set spelled with the same discipline as `Scoped.ScopedF`'s `tLam`
  alternative, and for the same reason -- the binder acts on the index,
  not on a payload.

  THE GRAMMAR IS ALREADY IN CNF, which is what lets it be run by
  `Spans.CYK` with nothing added:

      trm Γ    → trm Γ trm Γ  |  binder n  trm (n ∷ Γ)  |  'n'  (n ∈ Γ)
      binder n → 'λn'

  Concrete syntax is one token per lambda (`λx.` is the single token
  `lx`), and application is juxtaposition, so a term costs no
  punctuation.  That matters: the decision is a `löb` that re-descends
  rather than tabulating (`Spans.Base`), so the inputs must be tiny, and
  every character saved is a factor.

  Ambiguity is deliberate and harmless: `lx vx ly vy` reads both as
  `(λx.x)(λy.y)` and as `λx.(x (λy.y))`.  The decision searches, and
  either reading is a witness of the same grammar.

  Defines the token/name/scope vocabulary, the non-terminals `NT`, the
  rule family `BinR`, the lexical relation `TokIn`, the intrinsic-scoping
  lemmas `no-free-var` / `occursIn`, the demo tape, and the decision
  `derives?` with its observation `derives!`.
-}
module TheoryGrammar.Instances.Lambda.Parse where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Enumerable
open import TheoryGrammar.Instances.Spans.CYK

-- ==================================================================
-- THE CONCRETE SYNTAX.
--
-- Two names, and four tokens: the two variables and the two BINDERS.
-- Writing `λx.` as one token is a lexical decision, not a grammatical
-- one -- `binder n → 'λn'` would be the same rule over three tokens,
-- with three times the chart.
-- ==================================================================

data Nm : Type₀ where
  Nx Ny : Nm

data Tok : Type₀ where
  vx vy lx ly : Tok

-- the variable token of a name, and its binder token
varTok : Nm → Tok
varTok Nx = vx
varTok Ny = vy

lamTok : Nm → Tok
lamTok Nx = lx
lamTok Ny = ly

-- A scope is a LIST, innermost first, exactly as `Lambda.Scoped.Scope`.
-- A list rather than a set so that shadowing is expressible.
Scope : Type₀
Scope = List Nm

-- ==================================================================
-- THE NON-TERMINALS: one per scope, plus one per binder token.
--
-- `NT` is infinite, and nothing needs it not to be: `Spans.CYK` asks for
-- a list of rules AT EACH non-terminal, not a list of non-terminals.
-- The chart `&ᴰ NT (λ P → Dec⟨ Deriv P ⟩)` is a `&ᴰ` and so is happy
-- over an infinite index.
-- ==================================================================

data NT : Type₀ where
  trm    : Scope → NT
  binder : Nm → NT

-- ==================================================================
-- `TokIn t Γ` DENOTES: "the token `t` is a variable bound by `Γ`".
--
-- The same shape as `Lambda.Scoped.In`: `⊥` at the empty scope, a sum at
-- an extension.  It is the ONLY side condition in the grammar, and it is
-- the reason the scope index is not decoration.
-- ==================================================================

TokIn : Tok → Scope → Type₀
TokIn t []      = ⊥
TokIn t (n ∷ Γ) = (t Eq.≡ varTok n) ⊎ TokIn t Γ

-- `TokIn` names its name, and that name really is in the scope.  So a
-- variable leaf of a Γ-derivation is a Γ-BOUND occurrence -- which is
-- the leaf-level content of "the index is the set of names in scope".
occursIn : (t : Tok) (Γ : Scope) → TokIn t Γ → Σ[ n ∈ Nm ] ((t Eq.≡ varTok n) × (n ∈L Γ))
occursIn t (m ∷ Γ) (inl p) = m , p , here
occursIn t (m ∷ Γ) (inr q) = occursIn t Γ q .fst
                           , occursIn t Γ q .snd .fst
                           , there (occursIn t Γ q .snd .snd)

-- ==================================================================
-- THE INPUT.  One tape, read by every test at a different SPAN -- which
-- is what the span theory buys and what a string theory cannot say.
--
--   pos    0    1    2    3    4    5    6    7    8
--   token  λx.  x    λx.  x    y    λx.  x    λy.  y
--
--   (0,2) = λx. x            closed
--   (2,3) = λx. x y          `y` is free
--   (5,4) = (λx.x)(λy.y)     closed, and an application
--   (8,1) = y                free
--   (3,2) = x y              both free
--   (0,1) = λx.              a binder with no body -- not a term at all
-- ==================================================================

tape : ℕ → Tok
tape 0 = lx
tape 1 = vx
tape 2 = lx
tape 3 = vx
tape 4 = vy
tape 5 = lx
tape 6 = vx
tape 7 = ly
tape 8 = vy
tape _ = vy

-- ==================================================================
-- THE GRAMMAR.
-- ==================================================================

-- "P derives the token sitting at position j".  A term derives a single
-- token exactly when that token is a variable IN ITS SCOPE; a binder
-- non-terminal derives its own token.
unitR : NT → ℕ → Type₀
unitR (trm Γ)    j = TokIn (tape j) Γ
unitR (binder n) j = tape j Eq.≡ lamTok n

-- The binary rules, as an INDEXED FAMILY rather than a relation defined
-- by cases.  That is a deliberate choice: `allComplete` then case-splits
-- on the RULE -- three clauses -- instead of on every pair of
-- non-terminals, which for an infinite `NT` is not an option at all.
data BinR : NT → NT → NT → Type₀ where
  -- application, by juxtaposition: both halves live in the same scope
  rApp : (Γ : Scope) → BinR (trm Γ) (trm Γ) (trm Γ)
  -- abstraction: the binder token, then a body IN THE EXTENDED SCOPE.
  -- The index `n ∷ Γ` is the entire content of "λ binds n".
  rLam : (Γ : Scope) (n : Nm) → BinR (trm Γ) (binder n) (trm (n ∷ Γ))

open CYK NT unitR BinR public

-- the grammar of terms scoped by Γ; `Term []` is the closed terms
Term : Scope → SpanG
Term Γ = Deriv (trm Γ)

-- ==================================================================
-- INTRINSIC SCOPING, AS A THEOREM ABOUT THE GRAMMAR.
--
-- No word, no span, no decision procedure: at the empty scope the
-- variable rule is not available, because its side condition is `TokIn t
-- [] = ⊥`.  Everything the parser can ever produce at `trm []` is built
-- from the two binary rules, so it is closed BY TYPING.
-- ==================================================================

no-free-var : (s : Span) → UnitG (trm []) s → ⊥
no-free-var s (j , _ , v) = v

-- ... and at a general scope, the same statement with the witness kept:
-- a variable leaf of a Γ-derivation names one of Γ's own names.
var-is-bound : (Γ : Scope) (s : Span)
             → UnitG (trm Γ) s → Σ[ n ∈ Nm ] (n ∈L Γ)
var-is-bound Γ s (j , _ , v) =
  occursIn (tape j) Γ v .fst , occursIn (tape j) Γ v .snd .snd

-- ==================================================================
-- THE RULES, LISTED.  Four alternatives at a term, one at a binder.
-- ==================================================================

allRules : (P : NT) → List (Rule P)
allRules (trm Γ) = inl tt
                 ∷ inr (trm Γ      , trm Γ        , rApp Γ)
                 ∷ inr (binder Nx  , trm (Nx ∷ Γ) , rLam Γ Nx)
                 ∷ inr (binder Ny  , trm (Ny ∷ Γ) , rLam Γ Ny)
                 ∷ []
allRules (binder n) = inl tt ∷ []

-- ... AND IT MISSES NONE.  Because `BinR` is indexed, splitting on the
-- rule determines both non-terminals, so this is three lines rather than
-- a table over `NT × NT`.
allComplete : (P : NT) (r : Rule P) → r ∈L allRules P
allComplete (trm Γ)    (inl tt)                 = here
allComplete (trm Γ)    (inr (_ , _ , rApp _))   = there here
allComplete (trm Γ)    (inr (_ , _ , rLam _ Nx)) = there (there here)
allComplete (trm Γ)    (inr (_ , _ , rLam _ Ny)) = there (there (there here))
allComplete (binder n) (inl tt)                 = here
allComplete (binder n) (inr (_ , _ , ()))

-- ==================================================================
-- THE LEXICAL TABLE -- the one external residue, exactly as in
-- `Spans.Examples`.  External decidability enters here, once, to BUILD
-- an internal `Probe`; below this line nothing sees a token, a position
-- or a length.
-- ==================================================================

decEqTok : (a b : Tok) → (a Eq.≡ b) ⊎ No (a Eq.≡ b)
decEqTok vx vx = inl Eq.refl
decEqTok vy vy = inl Eq.refl
decEqTok lx lx = inl Eq.refl
decEqTok ly ly = inl Eq.refl
decEqTok vx vy = inr λ ()
decEqTok vx lx = inr λ ()
decEqTok vx ly = inr λ ()
decEqTok vy vx = inr λ ()
decEqTok vy lx = inr λ ()
decEqTok vy ly = inr λ ()
decEqTok lx vx = inr λ ()
decEqTok lx vy = inr λ ()
decEqTok lx ly = inr λ ()
decEqTok ly vx = inr λ ()
decEqTok ly vy = inr λ ()
decEqTok ly lx = inr λ ()

-- scope membership of a TOKEN, decided by induction on the scope
decTokIn : (t : Tok) (Γ : Scope) → TokIn t Γ ⊎ No (TokIn t Γ)
decTokIn t []      = inr λ ()
decTokIn t (n ∷ Γ) with decEqTok t (varTok n)
... | inl p = inl (inl p)
... | inr k with decTokIn t Γ
...   | inl q  = inl (inr q)
...   | inr k' = inr λ { (inl p) → k p ; (inr q) → k' q }

decUnitR : (P : NT) (j : ℕ) → unitR P j ⊎ No (unitR P j)
decUnitR (trm Γ)    j = decTokIn (tape j) Γ
decUnitR (binder n) j = decEqTok (tape j) (lamTok n)

-- PRIMITIVE (phase 1).  The one carrier-destructuring definition: a
-- `UnitG` holds only at spans of width one, so relating it to the tape
-- has to read a length.  Its TYPE is internal, so the decision procedure
-- receives a `⊤G ⊢ Dec⟨ UnitG P ⟩` and never learns there is a tape.
termProbe : (P : NT) → Probe (UnitG P)
termProbe P (i , zero)        _ = dec-no (UnitG P) _ λ { (j , () , _) }
termProbe P (i , suc (suc n)) _ = dec-no (UnitG P) _ λ { (j , () , _) }
termProbe P (i , suc zero)    _ = pick (decUnitR P i)
  where
    pick : unitR P i ⊎ No (unitR P i) → Dec⟨ UnitG P ⟩ (i , 1)
    pick (inl u) = dec-yes (UnitG P) _ (i , Eq.refl , u)
    pick (inr k) = dec-no  (UnitG P) _ λ { (j , Eq.refl , u) → k u }

open Decide allRules allComplete termProbe public

-- ==================================================================
-- THE PARSER, and its observation.
--
-- `derives? P : ⊤G ⊢ Deriv P ⊕ ¬G (Deriv P)` is the term; `parses? Γ`
-- is it at a scope, and `parses! Γ` is the same term composed with the
-- generic observer `okA`.  `run` appears only in `ParseTests`' `refl`
-- lines.
-- ==================================================================

parses? : (Γ : Scope) → Probe (Term Γ)
parses? Γ = derives? (trm Γ)

parses! : (Γ : Scope) → ⊤G ⊢ Δ Bool
parses! Γ = okA (Term Γ) (¬G (Term Γ)) ∘g parses? Γ

-- the binder tokens, decided the same way -- a sanity check that the
-- lexical layer is a non-terminal like any other
binder! : (n : Nm) → ⊤G ⊢ Δ Bool
binder! n = okA (Deriv (binder n)) (¬G (Deriv (binder n))) ∘g derives? (binder n)
