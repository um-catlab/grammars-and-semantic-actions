{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  STAGE 2 OF THE CHAIN: TOKENS -> PARSE TREE.

  This is `TheoryGrammar.Instances.Lambda.Parse` with ONE change, and the
  change is the reason the file exists: the tape is a MODULE PARAMETER
  rather than a fixed nine-position demo.

      module Chain.Parse (tape : ℕ → Tok)

  `Lambda.Parse` is exactly this module at its own hard-coded tape.  A
  chain cannot use that one, because the whole claim under test is that
  the LEXER's output is what the parser reads; so the tape has to be an
  argument, and `Chain.Pipeline` supplies the one that `Chain.Lex`
  produced.

  Everything that does not mention the tape is IMPORTED from
  `Lambda.Parse` rather than copied -- `Nm`, `Tok`, `Scope`, the
  non-terminals `NT`, the rule family `BinR`, the lexical relation
  `TokIn`, and the two decision helpers.  What is redefined here is the
  four definitions that genuinely read a tape (`unitR`, `decUnitR`,
  `termProbe`) plus the two rule tables, which must be restated only
  because they are typed at THIS module's instantiation of `CYK`.

  ------------------------------------------------------------------
  THE SECOND INSTANTIATION OF THE THEORY.

  `Chain.Lex` instantiated `Strings.Base` at Unicode `Char`.  Here the
  ambient alphabet is `Tok`, and the theory instantiated is `spanFib`
  rather than `strFib` -- spans of ONE word rather than words.  That is
  a genuine change of promodel and not merely of alphabet, and it is
  worth being precise about why the chain makes it:

    -- the lexer is a LEFT-TO-RIGHT machine, so the string theory, whose
       `⊗ˢ appop` splits a word into two words, is the right one; the
       scan is a fold over that splitting.

    -- the parser is a CHART, so the span theory, whose `⊗ˢ cat` cuts a
       span into two adjacent spans and whose degree is span LENGTH, is
       the right one; CYK's "fill by increasing length" IS guardedness
       there (`Spans.CYK`'s header).

  Both are `Fibered monoidSig`-style promodels over the same rule set,
  and the DSL is the same on either side.  `Chain.Pipeline`'s `tape`
  is the coercion between them: a `List LTok` read as a function
  `ℕ → Tok`.

  ------------------------------------------------------------------
  WHAT IS INHERITED, AND IT IS THE GOOD PART.

  `Term Γ = Deriv (trm Γ)` is the grammar of spans parsing as a lambda
  term with free names in Γ, and the scope is the NON-TERMINAL.  So
  `no-free-var` (imported, unchanged, and a fact about the RULES rather
  than about any tape) says a `Term []` cannot contain an unbound
  occurrence.  The chain gets intrinsic scope-checking for free, which
  is why the pipeline has no separate scope-check stage: it was absorbed
  into the parser's index.
-}
open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ; zero; suc)

open import TheoryGrammar.Instances.Lambda.Parse using (Tok; vx; vy; lx; ly)

module Chain.Parse (tape : ℕ → Tok) where

open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.List using (List; []; _∷_; length)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Enumerable
open import TheoryGrammar.Instances.Spans.CYK

-- Everything tape-independent, imported.  Note in particular that `NT`,
-- `BinR` and `TokIn` are NOT redefined: the grammar is literally the
-- same grammar, only pointed at a different word.
open import TheoryGrammar.Instances.Lambda.Parse public
  using ( Nm; Nx; Ny; varTok; lamTok; Scope
        ; NT; trm; binder; BinR; rApp; rLam
        ; TokIn; occursIn; decEqTok; decTokIn )

-- ==================================================================
-- §1  THE ONE PLACE THE WORD ENTERS.
--
-- `unitR P j` DENOTES "non-terminal P derives the terminal at position
-- j".  `Spans.CYK`'s header is explicit that this is the only channel:
-- nothing else in the CYK development knows there is a word at all.  So
-- making the tape a parameter is a change to exactly one definition,
-- and the rest of this file follows by typing.
-- ==================================================================

unitR : NT → ℕ → Type₀
unitR (trm Γ)    j = TokIn (tape j) Γ
unitR (binder n) j = tape j Eq.≡ lamTok n

open CYK NT unitR BinR public

-- the grammar of terms scoped by Γ; `Term []` is the closed terms
Term : Scope → SpanG
Term Γ = Deriv (trm Γ)

-- ==================================================================
-- §2  THE RULES, LISTED -- restated only because they are typed at this
-- module's `Rule`, which is `CYK`'s at THIS `unitR`.  The lists
-- themselves are character-for-character `Lambda.Parse`'s, because the
-- rule set does not depend on the input.
-- ==================================================================

allRules : (P : NT) → List (Rule P)
allRules (trm Γ) = inl tt
                 ∷ inr (trm Γ      , trm Γ        , rApp Γ)
                 ∷ inr (binder Nx  , trm (Nx ∷ Γ) , rLam Γ Nx)
                 ∷ inr (binder Ny  , trm (Ny ∷ Γ) , rLam Γ Ny)
                 ∷ []
allRules (binder n) = inl tt ∷ []

allComplete : (P : NT) (r : Rule P) → r ∈L allRules P
allComplete (trm Γ)    (inl tt)                  = here
allComplete (trm Γ)    (inr (_ , _ , rApp _))    = there here
allComplete (trm Γ)    (inr (_ , _ , rLam _ Nx)) = there (there here)
allComplete (trm Γ)    (inr (_ , _ , rLam _ Ny)) = there (there (there here))
allComplete (binder n) (inl tt)                  = here
allComplete (binder n) (inr (_ , _ , ()))

-- ==================================================================
-- §3  THE LEXICAL TABLE, and the terminal probe.
-- ==================================================================

decUnitR : (P : NT) (j : ℕ) → unitR P j ⊎ No (unitR P j)
decUnitR (trm Γ)    j = decTokIn (tape j) Γ
decUnitR (binder n) j = decEqTok (tape j) (lamTok n)

-- PRIMITIVE (phase 1).  A `UnitG` holds only at spans of width one, so
-- relating it to the tape has to read a length.  Its TYPE is internal,
-- so `Decide` receives a `⊤G ⊢ Dec⟨ UnitG P ⟩` and never learns there
-- is a tape.
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
-- §4  THE PARSER.
-- ==================================================================

parses? : (Γ : Scope) → Probe (Term Γ)
parses? Γ = derives? (trm Γ)

parses! : (Γ : Scope) → ⊤G ⊢ Δ Bool
parses! Γ = okA (Term Γ) (¬G (Term Γ)) ∘g parses? Γ
