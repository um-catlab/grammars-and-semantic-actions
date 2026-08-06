{-
  THE COMBINATOR LAYER over a substrate: intro and elim for EVERY
  connective, in one place, so instances compose rather than re-derive.

  This is the piece that was missing.  `Rules.agda` gives the additives
  over a `Model`; `Substrate.agda` gives `⊗ˢ`/`⊸ᶠ` currying.  Neither was
  usable from an instance, so the bag algorithms grew their own partial
  copies and then leaked into Agda-level functions (`merge : Bag → Bag →
  Bag`, motives like `λ _ → Bag`).  Everything an instance needs is here.

  The discipline this enables, and the reason it matters:

      a program in the calculus is a term  A ⊢ B,
      built ONLY from these combinators and clearly-marked primitives.

  For sorting, that changes the statement.  Instead of an Agda function
  `Bag → Bag` plus a separately-proved permutation lemma, sorting becomes

      merge      :  Sorted ⊗ Sorted  ⊢  Sorted
      mergesort  :  ⊤              ⊢  Sorted

  and permutation-correctness is FREE: `_⊢_` preserves the index and `⊗ˢ`
  splits it, so any term of that type necessarily rearranges rather than
  invents.  The half of correctness that had to be proved by hand
  (`permMerge`) is exactly the half that working internally gives away.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.RulesSub where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥*)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Substrate
open import TheoryGrammar.Rules
open import TheoryGrammar.Result

private variable ℓS ℓ ℓ' ℓX ℓP ℓA ℓB ℓC ℓY : Level

module RulesS {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (Sub : Substrate σ ℓX ℓP) where

  -- the connectives, and the additive rules, inherited
  open SubNotation Sub public
  open Rules ⌊ Sub ⌋ public
    hiding (⊗-I; ⊗-E; ⊗-UP)      -- the Model-level ⊗; superseded below

  private variable s : S

  -- ================================================================
  -- Composition.
  -- ================================================================

  idg : {A : TheoryTy ℓA s} → A ⊢ A
  idg _ x = x

  _∘g_ : {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} {C : TheoryTy ℓC s}
       → B ⊢ C → A ⊢ B → A ⊢ C
  (g ∘g f) m x = g m (f m x)

  infixr 9 _∘g_

  -- ================================================================
  -- ⊗ˢ  --  intro and elim at the SUBSTRATE's splittings.
  -- ================================================================

  module _ (o : σ .ops)
           {A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a)} where

    -- intro: a splitting, plus a payload at every slot
    ⊗ˢ-I : (m : Sub .carrier (σ .resultSort o)) (sp : Sub .Split o m)
         → ((a : σ .arities o) → A a (Sub .parts o m sp a))
         → ⊗ˢ o A m
    ⊗ˢ-I m sp h = sp , h

    ⊗ˢ-E : {B : TheoryTy ℓB (σ .resultSort o)}
         → MultiHomˢ o A B → ⊗ˢ o A ⊢ B
    ⊗ˢ-E {B = B} = uncurryˢ o {A = A} {B = B}

    -- (⊗ˢ-UP, the β/η package, comes from SubNotation already)

    -- functorial action, slotwise
    ⊗ˢ-map : {B : (a : σ .arities o) → TheoryTy ℓB (σ .sortOf o a)}
           → ((a : σ .arities o) → A a ⊢ B a) → ⊗ˢ o A ⊢ ⊗ˢ o B
    ⊗ˢ-map f m (sp , h) = sp , λ a → f a _ (h a)

  -- ================================================================
  -- Derived connectives, so instances never reach for Agda's.
  -- ================================================================

  -- The option type is `Result` at the error grammar `⊤G`, and every
  -- other parser shape is `Result` at a different one -- so it is
  -- DEFINED in `TheoryGrammar.Result` (additively; it never mentioned
  -- the operations) and only re-exported here, where instances look.
  open Res ⌊ Sub ⌋ public
    using (Result; ok; err; caseR; bindR; mapR; mapE; joinR; catchR;
           orElseR; altR; altList; bothR;
           MaybeG; just-I; nothing-I; MaybeG-E;
           orElseM; altM; altListM; runCover; toMaybe)

  -- the empty and singleton branches of a decomposition, as a grammar:
  -- `⊕ᴰ` over the carrier is how you say "for some element".
  Some : (Y : Type ℓY) → (Y → TheoryTy ℓA s) → TheoryTy (ℓ-max ℓY ℓA) s
  Some = ⊕ᴰ

  -- ================================================================
  -- Sanity: the additive rules really are available here.
  -- ================================================================

  private
    _ : {A : TheoryTy ℓA s} → A ⊢ ⊤G
    _ = ⊤-I

    _ : {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} {C : TheoryTy ℓC s}
      → A ⊢ C → B ⊢ C → (A ⊕ B) ⊢ C
    _ = ⊕-E

    _ : {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} {C : TheoryTy ℓC s}
      → A ⊢ B → A ⊢ C → A ⊢ (B & C)
    _ = &-I
