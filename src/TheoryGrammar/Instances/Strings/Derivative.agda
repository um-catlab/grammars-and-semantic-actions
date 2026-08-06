{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE FIRST STEP OF DERIVATIVE PARSING, INTERNALLY.

  To decide `A ⊗' B` at `w` one must consider every cut of `w`.  The
  enumeration of cuts cannot be written internally -- `TheoryTy` is a
  family over the CARRIER, so there is no grammar indexed by the
  splittings of the current world, and hence no way to iterate them.
  `⊗ˢ` mentions a cut but commits to one; a Π over cuts is negative and
  can only be queried.

  The move that IS internal is to case-split the LEFT FACTOR'S GRAMMAR
  rather than the splitting:

      A ⊗' B  ≅  ((A & ⌈[]⌉) ⊗' B)  ⊕  ((A & NonTrivial) ⊗' B)

  "either the left factor is matched by the empty prefix, or it is not."
  Iterating this generates the cuts one at a time, as a chain of `⊕`s
  rather than as a `List` -- and each iteration peels one character, so
  the recursion descends on `length` and `Graded`'s ℕ-degree suffices.
  No span order is needed.

  Everything below is a combinator except ONE phase-1 rule, `⊗-dist⊕`:
  the sum sits at a SLOT and the conclusion is at the WHOLE, which the
  index-preserving `⊕-E` cannot cross.  That is the same obstruction as
  the single match in `Decidable.Tensor.dec-⊗`, and it is discharged
  here once.  It is unconditionally true -- `Σ` distributes over `⊎` --
  and the only reason it is not generic is that substituting at slot `i`
  needs `Focus`'s `Rest`.

  This is the first customer for `View.viewCase`: `splitLeft` consults a
  view (`charCase`) while a payload (`A`) is in hand, which is exactly
  the case `caseOf` does not cover.
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Strings.Derivative (Char : Type₀) where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.List

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.View

open import TheoryGrammar.Instances.Strings.Decomposition Char public

-- ==================================================================
-- THE ONE PHASE-1 RULE.
--
-- A sum at the left slot becomes a sum at the whole.  One match, on the
-- payload of a slot; the splitting is untouched and simply carried.
-- ==================================================================

⊗-dist⊕ : (A A' B : Gr) → ((A ⊕ A') ⊗' B) ⊢ ((A ⊗' B) ⊕ (A' ⊗' B))
⊗-dist⊕ A A' B w (sp , h) with h true
... | inl a = inl (sp , λ { true → a ; false → h false })
... | inr a' = inr (sp , λ { true → a' ; false → h false })

-- ==================================================================
-- ... and everything else is a combinator.
-- ==================================================================

module _ (A B : Gr) where

  -- Consult `charCase` with `A` still in hand.  `viewCase` is exactly
  -- this: `&-I` puts the view in the context, `dist&r` distributes.
  -- At `B = ⊤G` it would collapse to `caseOf`; here it does not, because
  -- the payload `A` has to survive the analysis.
  atLeft : A ⊢ ((A & ⌈ [] ⌉) ⊕ (A & NonTrivial))
  atLeft = viewCase charCase ⊕-I₁ ⊕-I₂

  private
    lmap : {P P' Q Q' : Gr} → P ⊢ P' → Q ⊢ Q' → (P ⊗' Q) ⊢ (P' ⊗' Q')
    lmap {P} {P'} {Q} {Q'} f g =
      ⊗ˢ-map appop {A = λ b → if b then P else Q}
                   {B = λ b → if b then P' else Q'}
                   λ { true → f ; false → g }

  -- THE SPLIT.  "The left factor either matches the empty prefix or it
  -- does not."  Iterating this is the cut-scan.
  splitLeft : (A ⊗' B) ⊢ (((A & ⌈ [] ⌉) ⊗' B) ⊕ ((A & NonTrivial) ⊗' B))
  splitLeft =
    ⊗-dist⊕ (A & ⌈ [] ⌉) (A & NonTrivial) B ∘g lmap atLeft idg

  -- ... and it is an iso: forgetting the extra conjunct is `&-E₁`.
  joinLeft : (((A & ⌈ [] ⌉) ⊗' B) ⊕ ((A & NonTrivial) ⊗' B)) ⊢ (A ⊗' B)
  joinLeft = ⊕-E (lmap &-E₁ idg) (lmap &-E₁ idg)

  -- So a decision transports across it, with `dec-map` and `dec-⊕`:
  -- deciding the two summands decides the tensor.  The ε-summand is the
  -- nullability case; the NonTrivial summand is where a character is
  -- peeled and the recursion descends.
  decSplitLeft : (Dec⟨ (A & ⌈ [] ⌉) ⊗' B ⟩ & Dec⟨ (A & NonTrivial) ⊗' B ⟩)
               ⊢ Dec⟨ A ⊗' B ⟩
  decSplitLeft =
    dec-map (((A & ⌈ [] ⌉) ⊗' B) ⊕ ((A & NonTrivial) ⊗' B)) (A ⊗' B)
            joinLeft splitLeft
    ∘g dec-⊕ ((A & ⌈ [] ⌉) ⊗' B) ((A & NonTrivial) ⊗' B)

-- ==================================================================
-- The derivative itself: `∂ c A` is `A` with a leading `c` consumed.
-- This is `Strings.Connectives._⟜'_` at a literal, i.e. the residual at
-- the canonical focus -- no new connective.
-- ==================================================================

∂ : Char → Gr → Gr
∂ c A = A ⟜' literal c

-- `⟜-app` read as the derivative's counit: putting the character back
-- recovers the grammar.
∂-app : (c : Char) (A : Gr) → (literal c ⊗' ∂ c A) ⊢ A
∂-app c A = ⟜-app
