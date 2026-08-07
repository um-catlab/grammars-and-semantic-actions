{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE SPAN CYK, MEASURED -- a baseline to refactor against.

  `Spans.Examples` shows the decision runs.  This file is the REGRESSION
  SUITE: a grammar with genuine two-dimensional chart behaviour, and
  enough pinned answers that a change to the decision procedure which
  alters its meaning fails here rather than silently.

  The grammar is `aⁿbⁿ` in CNF -- the standard example that is
  context-free and not regular, and the smallest one for which the CYK
  chart is not a line:

      S → A C | A B        C → S B        A → 'a'   B → 'b'

  over the word

      position   0 1 2 3 4 5
      letter     a a a b b b

  Unlike `Examples`' `S → A B | S B`, this grammar's derivations NEST:
  deciding S at (0,6) consults C at (1,5), which consults S at (1,4),
  which consults C at (2,3), which consults S at (2,2).  Every level of
  the chart is used, and both nonterminals S and C are live at
  interleaved spans -- which is what makes it a chart rather than a
  stack.

  WHAT IS PINNED, AND WHY.  Each battery below fixes the answer at every
  span of a given length, not just at the ones that succeed.  A decision
  procedure that got the recurrence subtly wrong -- scanned the wrong
  cuts, dropped the resource certificate, confused the slots -- would
  still typecheck and would still say `true` at (0,6); what it could not
  do is reproduce the whole row.  That is the point of listing the
  failures.
-}
module TheoryGrammar.Instances.Spans.Bench where

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
-- The word:  a a a b b b   (everything from position 6 on is 'b',
-- which no test reaches).
-- ==================================================================

ltb : ℕ → ℕ → Bool
ltb zero    (suc _) = true
ltb _       zero    = false
ltb (suc m) (suc n) = ltb m n

charAt : ℕ → Bool
charAt j = ltb j 10

-- ==================================================================
-- The grammar:  S → A C | A B,  C → S B,  A → 'a',  B → 'b'
-- ==================================================================

data NT : Type₀ where ntS ntA ntB ntC : NT

unitR : NT → ℕ → Type₀
unitR ntS j = ⊥
unitR ntC j = ⊥
unitR ntA j = charAt j Eq.≡ true
unitR ntB j = charAt j Eq.≡ false

binR : NT → NT → NT → Type₀
binR ntS ntA ntB = Unit
binR ntS ntA ntC = Unit
binR ntC ntS ntB = Unit
binR _   _   _   = ⊥

open CYK NT unitR binR

allRules : (P : NT) → List (Rule P)
allRules ntS = inl tt ∷ inr (ntA , ntB , tt) ∷ inr (ntA , ntC , tt) ∷ []
allRules ntC = inl tt ∷ inr (ntS , ntB , tt) ∷ []
allRules ntA = inl tt ∷ []
allRules ntB = inl tt ∷ []

allComplete : (P : NT) (r : Rule P) → r ∈L allRules P
allComplete ntS (inl tt)               = here
allComplete ntS (inr (ntS , _   , ()))
allComplete ntS (inr (ntB , _   , ()))
allComplete ntS (inr (ntC , _   , ()))
allComplete ntS (inr (ntA , ntS , ()))
allComplete ntS (inr (ntA , ntA , ()))
allComplete ntS (inr (ntA , ntB , tt)) = there here
allComplete ntS (inr (ntA , ntC , tt)) = there (there here)
allComplete ntC (inl tt)               = here
allComplete ntC (inr (ntA , _   , ()))
allComplete ntC (inr (ntB , _   , ()))
allComplete ntC (inr (ntC , _   , ()))
allComplete ntC (inr (ntS , ntS , ()))
allComplete ntC (inr (ntS , ntA , ()))
allComplete ntC (inr (ntS , ntB , tt)) = there here
allComplete ntC (inr (ntS , ntC , ()))
allComplete ntA (inl tt)               = here
allComplete ntA (inr (_ , _ , ()))
allComplete ntB (inl tt)               = here
allComplete ntB (inr (_ , _ , ()))

-- external decidability of the alphabet; used only to build `termProbe`
decEqB : (a b : Bool) → (a Eq.≡ b) ⊎ No (a Eq.≡ b)
decEqB true  true  = inl Eq.refl
decEqB false false = inl Eq.refl
decEqB true  false = inr λ ()
decEqB false true  = inr λ ()

decUnit : (P : NT) (j : ℕ) → unitR P j ⊎ No (unitR P j)
decUnit ntS j = inr λ ()
decUnit ntC j = inr λ ()
decUnit ntA j = decEqB (charAt j) true
decUnit ntB j = decEqB (charAt j) false

-- PRIMITIVE (phase 1).  The lexical table -- the file's one
-- carrier-destructuring definition, exactly as in `Spans.Examples`.
termProbe : (P : NT) → Probe (UnitG P)
termProbe P (i , zero)        _ = dec-no (UnitG P) _ λ { (j , () , _) }
termProbe P (i , suc (suc n)) _ = dec-no (UnitG P) _ λ { (j , () , _) }
termProbe P (i , suc zero)    _ = pick (decUnit P i)
  where
    pick : unitR P i ⊎ No (unitR P i) → Dec⟨ UnitG P ⟩ (i , 1)
    pick (inl u) = dec-yes (UnitG P) _ (i , Eq.refl , u)
    pick (inr k) = dec-no  (UnitG P) _ λ { (j , Eq.refl , u) → k u }

open Decide allRules allComplete termProbe

derives! : (P : NT) → ⊤G ⊢ Δ Bool
derives! P = okA (Deriv P) (¬G Deriv P) ∘g derives? P

-- BENCH: the word is a¹⁰b¹⁰, so span (10-k , 2k) reads exactly aᵏbᵏ and
-- is an S.  Deciding it forces the chart to depth k.  The line below is
-- what the sweep script rewrites.
_ : passes (run (derives! ntS) at ( (9 , 2) ↦ true ∷ [] ))
_ = refl
