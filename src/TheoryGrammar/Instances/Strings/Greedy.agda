{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Leftmost-greedy parses.

   `Greedy A` is "a parse of A over some prefix `w`, together with a
   proof that no NONEMPTY extension of `w` also has an A-parse" -- the
   longest match.  It stays a string instance, and correctly so: there
   is no "leftmost" for bags, which is the same reason `Greedy` sits in
   PORTING.md's string-specific bucket.

   What ports for free is the residual it needs.  "A-parse of `w ++ v`,
   as a grammar in `v`" is exactly the DERIVATIVE with the left slot
   pinned to `w` rather than to a single character -- so `Derivʷ` below
   is `TheoryGrammar.Derivative`'s `ActOf` at a different rest-tuple,
   and `actʷ-β` is `refl`.  Nothing new is defined; the `Assembly`
   parameter is what makes one machine serve both.

   Every term here is a `⊢`-combinator composite. -}
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sum using (_⊎_; inl; inr)
import Cubical.Data.Equality as Eq
open import TheoryGrammar.Enumerable using (No)

module TheoryGrammar.Instances.Strings.Greedy
  (Char : Type₀)
  (decChar : (a b : Char) → (a Eq.≡ b) ⊎ No (a Eq.≡ b))
  where

open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.List

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.CanonicalFocus
open import TheoryGrammar.Derivative

open import TheoryGrammar.Instances.Strings.SeqUnambig Char decChar public

-- ==================================================================
-- The derivative at a whole prefix.  Same `Assembly`, different
-- rest-tuple: `Derivᶜ c` pins the left slot to `c ∷ []`, this pins it
-- to `w`.
-- ==================================================================
module Derivʷ (w : String) where
  open ActOf strFib strPoint appop false consAs (λ _ → w) public

actʷ-β : (w v : String) → Derivʷ.act w v ≡ (w ++ v)
actʷ-β w v = refl

-- ==================================================================
-- Greedy parses.
-- ==================================================================

-- (the grammar is `G`, not `A`, only so the pinned implicits below --
-- `⊗ˢ-map`'s own `A`/`B` -- read unambiguously.  Grammar-valued
-- implicits are never inferable here: `⊗'` hides the arity family
-- behind an `if`, so both ends must be given.)
module _ (G : Gr) where

  -- "G over w, and nothing longer": the second factor refutes every
  -- NONEMPTY continuation that would still yield a G-parse.  `⊤G` at
  -- the end lets the refutation range over the rest of the input.
  Tail : String → Gr
  Tail w = ¬G ((Derivʷ.δ w G & NonTrivial) ⊗' ⊤G)

  Greedy : Gr
  Greedy = ⊕ᴰ String λ w → (⌈ w ⌉ & G) ⊗' Tail w

  -- forget the maximality: a greedy parse is in particular a parse
  Greedy→leftmost : Greedy ⊢ (G ⊗' ⊤G)
  Greedy→leftmost = ⊕ᴰ-E λ w →
    ⊗ˢ-map appop {A = λ b → if b then (⌈ w ⌉ & G) else Tail w}
                 {B = λ b → if b then G else ⊤G}
                 λ { true → &-E₂ ; false → ⊤-I }

  GreedyCompl : Gr
  GreedyCompl = ¬G (G ⊗' ⊤G)

  -- ... so a greedy parse and its complement cannot both hold
  disjointGreedy : (Greedy & GreedyCompl) ⊢ ⊥G
  disjointGreedy = ⇒-app ∘g &-I &-E₂ (Greedy→leftmost ∘g &-E₁)
