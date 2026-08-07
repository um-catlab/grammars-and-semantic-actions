{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  CYK AT SPANS, RUN.

  `Spans.CYK` says the chart is a connective: `deg (i , n) = n`, so
  `▷ Dec⟨ Deriv P ⟩` at a span is "decided at every SHORTER span", and
  memoisation by span length is `löb`.  That claim is only worth
  something if the term REDUCES, so this file is the evidence: the
  `refl` lines below are the chart being filled at typecheck time.

  ONE AMBIENT WORD, MANY SPANS.  This is what the span theory buys and
  what `Instances.Strings.CYK` cannot say: `charAt` fixes the word

      a b b b …

  once, and every test below is the SAME decision procedure at a
  different span of it.  In the string theory each of these would be a
  different input; here they are different indices of one grammar, and
  the recursion is shared between them exactly as a CYK chart is.

      span (0,1)  reads  "a"      -- an A, not a B, and not an S
      span (0,2)  reads  "ab"     -- an S, by S → A B
      span (0,5)  reads  "abbbb"  -- an S, by four uses of S → S B
      span (1,4)  reads  "bbbb"   -- refuted: no leading `a`

  The grammar is in CNF:  S → A B | S B,  A → 'a',  B → 'b',  so S
  derives `a bⁿ` for n ≥ 1.  `S → S B` is LEFT-recursive and still
  guarded, because `NEslot` forces both slots non-empty and hence the
  recursive S onto a strictly shorter span.  That is CNF's ban on
  ε-productions doing the work, and it is why the recursion descends on
  the chart rather than stalling at the same span.

  The only external input is `decEqB` -- decidability of the alphabet --
  and it enters exactly once, to BUILD the internal `termProbe`.  That
  is the same discipline as `Strings.Examples.decEqS`.

  MEASURED, AND A CAVEAT.  Elaborating this file -- which runs the
  decision at fourteen spans -- takes about 1.5s.  Pushing the longest
  span out gives

      n =  6   1.5s        n = 10   2.1s
      n =  8   1.6s        n = 12   5.0s

  so the growth is superlinear, and the reason is worth stating: `löb`
  is `WFI.induction`, which RE-DESCENDS at every consultation.  `▷ A` at
  a span really is "A at every shorter span", so the recursion has the
  shape of a chart -- every recursive call is at a strictly shorter
  span, which is what the file demonstrates -- but nothing TABULATES it.
  The connective gives the well-founded structure of CYK; it does not by
  itself give the sharing that makes CYK cubic.  Getting that is a
  separate question (a tabulated fixpoint), and no claim about it is
  made here or in `Spans.CYK`.
-}
module TheoryGrammar.Instances.Spans.Examples where

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
open import TheoryGrammar.SemanticAction using (passes; _↦_; _at_)

open import TheoryGrammar.Instances.Spans.CYK

-- ==================================================================
-- The ambient word, and the grammar.
-- ==================================================================

-- the word `a b b b …`, as a function from POSITION to letter.  It
-- enters the calculus only through `unitR`; nothing else knows it.
charAt : ℕ → Bool
charAt zero    = true      -- 'a'
charAt (suc _) = false     -- 'b'

data NT : Type₀ where ntS ntA ntB : NT

-- "P derives the terminal sitting at position j"
unitR : NT → ℕ → Type₀
unitR ntS j = ⊥
unitR ntA j = charAt j Eq.≡ true
unitR ntB j = charAt j Eq.≡ false

-- S → A B  and  S → S B, so S derives `a bⁿ` for n ≥ 1.  The second
-- rule is LEFT-recursive and is still guarded: `NEslot` requires both
-- slots non-empty, so the S in `S → S B` sits at a strictly shorter
-- span.  That is CNF's ban on ε-productions doing its work, and it is
-- what makes the chart -- rather than a `▷` at the same span -- the
-- thing the recursion descends on.
binR : NT → NT → NT → Type₀
binR ntS ntA ntB = Unit
binR ntS ntS ntB = Unit
binR _   _   _   = ⊥

open CYK NT unitR binR

-- ==================================================================
-- The finite data: the rules, and the lexical table.
-- ==================================================================

allRules : (P : NT) → List (Rule P)
allRules ntS = inl tt ∷ inr (ntA , ntB , tt) ∷ inr (ntS , ntB , tt) ∷ []
allRules ntA = inl tt ∷ []
allRules ntB = inl tt ∷ []

allComplete : (P : NT) (r : Rule P) → r ∈L allRules P
allComplete ntS (inl tt)               = here
allComplete ntS (inr (ntS , ntS , ()))
allComplete ntS (inr (ntS , ntA , ()))
allComplete ntS (inr (ntS , ntB , tt)) = there (there here)
allComplete ntS (inr (ntA , ntS , ()))
allComplete ntS (inr (ntA , ntA , ()))
allComplete ntS (inr (ntA , ntB , tt)) = there here
allComplete ntS (inr (ntB , _   , ()))
allComplete ntA (inl tt)               = here
allComplete ntA (inr (_ , _ , ()))
allComplete ntB (inl tt)               = here
allComplete ntB (inr (_ , _ , ()))

-- External decidability of the ALPHABET.  Used only to build
-- `termProbe` below; the calculus never sees it.


decEqB : (a b : Bool) → (a Eq.≡ b) ⊎ No (a Eq.≡ b)
decEqB true  true  = inl Eq.refl
decEqB false false = inl Eq.refl
decEqB true  false = inr λ ()
decEqB false true  = inr λ ()

-- ... and that primitive, at one position: does P derive the letter
-- sitting at j?  Still external; the internalisation is `termProbe`.
decUnit : (P : NT) (j : ℕ) → unitR P j ⊎ No (unitR P j)
decUnit ntS j = inr λ ()
decUnit ntA j = decEqB (charAt j) true
decUnit ntB j = decEqB (charAt j) false

-- PRIMITIVE (phase 1).  THE LEXICAL TABLE.
--
-- This is the file's one carrier-destructuring definition, and it has
-- to be: `UnitG P` holds at a span exactly when that span is ONE
-- position wide, so relating it to the external word requires reading
-- the span's length.  A `Probe` is the interface between the outside
-- world and the calculus, and building one is exactly where matching a
-- carrier is sanctioned -- the same role `Strings.Examples.decEqS`
-- plays.
--
-- What matters is that it is CONFINED: `termProbe`'s TYPE is internal,
-- so `Spans.CYK` receives a `⊤G ⊢ Dec⟨ UnitG P ⟩` and no part of the
-- decision procedure ever sees a length, a position, or the word.
-- Nothing below this line matches a span either.
termProbe : (P : NT) → Probe (UnitG P)
termProbe P (i , zero)          _ = dec-no (UnitG P) _ λ { (j , () , _) }
termProbe P (i , suc (suc n))   _ = dec-no (UnitG P) _ λ { (j , () , _) }
termProbe P (i , suc zero)      _ = pick (decUnit P i)
  where
    pick : unitR P i ⊎ No (unitR P i) → Dec⟨ UnitG P ⟩ (i , 1)
    pick (inl u) = dec-yes (UnitG P) _ (i , Eq.refl , u)
    pick (inr k) = dec-no  (UnitG P) _ λ { (j , Eq.refl , u) → k u }

open Decide allRules allComplete termProbe

-- ==================================================================
-- ... and the decision, OBSERVED.
--
-- `okA` (TheoryGrammar.SemanticAction) reads a `Result E A` at ANY
-- error grammar, so the same combinator that observes a parser observes
-- this.  The result is a TERM `⊤G ⊢ Δ Bool`; `run` appears only in the
-- `refl` lines.
-- ==================================================================

derives! : (P : NT) → ⊤G ⊢ Δ Bool
derives! P = okA (Deriv P) (¬G Deriv P) ∘g derives? P

-- THE CHART, FILLED.  One term, many spans of one word.  The positive
-- cases at length 3, 4 and 5 are where the recursion actually recurses:
-- deciding `S` at `(0,5)` consults `S` at `(0,4)`, which consults
-- `(0,3)`, and each of those is `▷` at a strictly shorter span.
_ : passes (run (derives! ntS) at
             ( (0 , 1) ↦ false     -- "a"     -- S is not a letter
             ∷ (0 , 2) ↦ true      -- "ab"    -- S → A B
             ∷ (0 , 3) ↦ true      -- "abb"   -- S → S B
             ∷ (0 , 4) ↦ true      -- "abbb"
             ∷ (0 , 5) ↦ true      -- "abbbb"
             ∷ (1 , 2) ↦ false     -- "bb"    -- no leading `a`
             ∷ (1 , 3) ↦ false     -- "bbb"
             ∷ (1 , 4) ↦ false     -- "bbbb"
             ∷ [] ))
_ = refl

-- the leaves, at the spans they sit at.  `deg = length`, so these are
-- the base of the chart and the recursion never reaches below them.
_ : passes (run (derives! ntA) at
             ( (0 , 1) ↦ true ∷ (1 , 1) ↦ false ∷ (0 , 2) ↦ false ∷ [] ))
_ = refl

_ : passes (run (derives! ntB) at
             ( (1 , 1) ↦ true ∷ (2 , 1) ↦ true ∷ (0 , 1) ↦ false ∷ [] ))
_ = refl

-- ==================================================================
-- WHAT A NEGATIVE ANSWER IS.
--
-- `derives?` is a `Result (¬G _) _`, so a `false` is not "the search
-- gave up": it is a REFUTATION, a theorem that no parse tree exists at
-- that span.  `refute` extracts it, uniformly in the error grammar --
-- the same combinator would yield only `tt` from a parser.
-- ==================================================================

noDeriv : (P : NT) (s : Span) → run (derives! P) s ≡ false → (¬G Deriv P) s
noDeriv P = refute (Deriv P) (¬G Deriv P) (derives? P)

-- "bb" is not an S -- a proof, obtained by running the term
no-bb : Deriv ntS (1 , 2) → E.⊥* {ℓ-zero}
no-bb = noDeriv ntS (1 , 2) refl

-- ... and dually, a positive answer hands back the parse tree
ab-tree : Deriv ntS (0 , 2)
ab-tree = witness (Deriv ntS) (¬G Deriv ntS) (derives? ntS) (0 , 2) refl
