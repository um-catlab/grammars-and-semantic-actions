{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  CYK, IN THE THEORY OF SPANS.

  The same description as `Instances.Strings.CYK`, but over `spanFib`
  instead of `strFib`.  Two things change, and both are the point:

  (1) `⊗e cat` really is "this span cuts into two adjacent spans", so
      the tensor of the calculus IS the CYK recurrence.  In the string
      theory `⊗e appop` splits a string into two strings, and the
      ambient word had to be carried by hand.

  (2) `deg (i , n) = n`, so guardedness descends on SPAN LENGTH.  A
      derivation at a span of length n recurses only at strictly shorter
      spans, which is precisely "fill the chart by increasing span
      length".  `▷ Deriv P` at a span IS the filled sub-chart, and it is
      a connective, not a data structure.

  The ambient word enters ONLY through `unitR : V → ℕ → Type₀`, read as
  "nonterminal P derives the terminal at position j".  Nothing else in
  the file knows there is a word.

  CNF's ban on ε-productions appears as `NEslot`: every recursive slot
  is paired with `⌜ NonEmpty ⌝`, and requiring BOTH slots non-empty is
  what makes BOTH proper -- because properness of a slot is non-emptiness
  of its COMPLEMENT (`Spans.Graded.SpanProper`).
-}
module TheoryGrammar.Instances.Spans.CYK where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Unit
open import Cubical.Data.List

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded

open import TheoryGrammar.Instances.Spans.Graded public

module CYK (V : Type₀)
           (unitR : V → ℕ → Type₀)          -- P derives the terminal at j
           (binR  : V → V → V → Type₀) where -- P → Q T

  -- the descriptions are indexed by the CFG's own non-terminals
  module G = Guard spanGraded ℓ-zero V (λ _ → tt)

  -- The terminal alternative, as a grammar: this span is a UNIT span at
  -- some position, and P derives the terminal sitting there.
  UnitG : V → SpanG
  UnitG P = ⊕ᴰ ℕ (λ j → ⌈ (j , 1) ⌉ & (λ _ → unitR P j))

  Rule : V → Type₀
  Rule P = Unit ⊎ (Σ[ Q ∈ V ] Σ[ T ∈ V ] binR P Q T)

  -- A recursive occurrence together with a proof its span is non-empty.
  -- That proof is what makes the SIBLING slot proper, and CNF's ban on
  -- ε-productions is exactly what supplies it.
  NEslot : V → Bool → G.Functor tt
  NEslot Q true  = G.Var Q
  NEslot Q false = G.⌜ NonEmpty ⌝

  NEvar : V → G.Functor tt
  NEvar Q = G.&e Bool (NEslot Q)

  binSlot : V → V → Bool → G.Functor tt
  binSlot Q T true  = NEvar Q
  binSlot Q T false = NEvar T

  ruleF : (P : V) → Rule P → G.Functor tt
  ruleF P (inl _)           = G.⌜ UnitG P ⌝
  ruleF P (inr (Q , T , _)) = G.⊗e cat (binSlot Q T)

  CYKF : (P : V) → G.Functor tt
  CYKF P = G.⊕e (Rule P) (ruleF P)

  -- THE PARSE TREES of a span from P, as a grammar over SPANS.
  Deriv : V → SpanG
  Deriv P s = G.μ CYKF (P , s)

  -- ================================================================
  -- Guardedness -- i.e. the chart is filled by increasing span length.
  --
  -- Identical to `Strings.CYK.cykGuarded` clause for clause; only the
  -- splitting family changed.  That the proof transports unchanged is
  -- the evidence that `Graded` was generic in the theory.
  -- ================================================================

  ≤NEslot : (Q : V) (b : Bool) → G.Guarded≤ (NEslot Q b)
  ≤NEslot Q true  = G.≤Var Q
  ≤NEslot Q false = G.≤⌜⌝ NonEmpty

  ≤binSlot : (Q T : V) (b : Bool) → G.Guarded≤ (binSlot Q T b)
  ≤binSlot Q T true  = G.≤&e Bool (NEslot Q) (≤NEslot Q)
  ≤binSlot Q T false = G.≤&e Bool (NEslot T) (≤NEslot T)

  cykGuarded : (P : V) → G.Guarded (CYKF P)
  cykGuarded P = G.<⊕e (Rule P) (ruleF P) alt
    where
      -- properness of a slot is non-emptiness of its COMPLEMENT, so each
      -- slot's certificate comes from its SIBLING's `NonEmpty` component
      pr : (Q T : V) (s : Span) (c : SpanSplit cat s)
           (sh : (a : Bool) → G.Sh (binSlot Q T a) (SpanParts cat s c a))
           (a : Bool) → G.Pos (binSlot Q T a) _ (sh a) → SpanProper cat s c a
      pr Q T s c sh true  p = lower (sh false false)
      pr Q T s c sh false p = lower (sh true false)

      alt : (r : Rule P) → G.Guarded (ruleF P r)
      alt (inl _)           = G.<⌜⌝ (UnitG P)
      alt (inr (Q , T , _)) =
        G.<⊗e cat (binSlot Q T) (≤binSlot Q T) (pr Q T)
