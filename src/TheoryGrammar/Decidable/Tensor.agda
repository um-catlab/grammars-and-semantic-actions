{-
  Decidability through a tensor.  Needs a `Substrate`.

  The internal half has no hypotheses: a term that is not an o-composite
  carries no o-tensor, which is `¬G` along the map that forgets every
  slot (`⊗-miss`).  The other half genuinely needs a side condition --
  deciding `⊗ˢ o A` at `m` means eliminating a sum sitting at a SLOT and
  landing at the WHOLE, which index-preserving `⊕-E` cannot do, and
  combining over slots needs the arity finite.  `DecReadable` is exactly
  that side condition.
-}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Decidable.Tensor where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥*)

open import TheoryGrammar.Base
open import TheoryGrammar.Substrate
open import TheoryGrammar.Rules
open import TheoryGrammar.RulesSub
open import TheoryGrammar.SemanticAction
open import TheoryGrammar.Decidable.Additive

private variable ℓS ℓ ℓ' ℓX ℓP ℓA ℓB ℓC ℓY : Level

module DecSub {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
              (Sub : Substrate σ ℓX ℓP) where

  -- the connectives and the additive rules come from `RulesSub`; only
  -- the decision layer is taken from §1, so nothing is defined twice
  open RulesS Sub public
  -- ... and the semantic actions, which are how a decision gets
  -- OBSERVED: `accepts?` / `runResult` are uniform in the error
  -- grammar, so they read a `Dec⟨_⟩` and a `MaybeG` alike
  open ActSub Sub public
  open DecAdd ⌊ Sub ⌋ public
    using (¬G_; Dec⟨_⟩; dec-yes; dec-no;
           Complement; Decision; decide; exclude;
           ¬G-excludes; largest; toDec; decDefault;
           &-swap; contra; dist&; ¬G-map; deMorgan;
           dec-map; dec-⊕; dec-&; dec-⊤; dec-⊥)

  -- ----------------------------------------------------------------
  -- The internal half, with NO hypotheses: a term that is not an
  -- o-composite at all carries no o-tensor, whatever the slots say.
  -- This is just `¬G` applied to the functorial action that forgets
  -- every slot -- the tensor's own map, from `RulesSub`.
  -- ----------------------------------------------------------------

  module _ (o : σ .ops)
           (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a)) where

    ⊗-miss : ¬G (⊗ˢ o (λ _ → ⊤G)) ⊢ ¬G (⊗ˢ o A)
    ⊗-miss = ¬G-map (⊗ˢ-map o {A = A} {B = λ _ → ⊤G} (λ _ → ⊤-I))

    -- the same, one level up: decided slots still forget to `⊤`
    ⊗-thin : ¬G (⊗ˢ o (λ a → Dec⟨ A a ⟩)) ⊢ ¬G (⊗ˢ o A)
    ⊗-thin = ¬G-map (⊗ˢ-map o {A = A} {B = λ a → Dec⟨ A a ⟩}
                             (λ a → dec-yes (A a)))

  -- ----------------------------------------------------------------
  -- The half that needs a hypothesis, and precisely why.
  --
  -- To decide `⊗ˢ o A` at `m` one must eliminate a sum sitting at a
  -- SLOT (index `parts o m sp a`) and land at the WHOLE (index `m`).
  -- The internal `⊕-E` preserves the index, so it cannot do that on its
  -- own; the connective that moves between a slot and the whole is the
  -- residual `⊸ᶠ`, and even with it the combination over all slots
  -- needs the arity to be finite.  For an infinite arity the statement
  -- is simply false.  So it is a hypothesis on the substrate:
  --
  --   splitProp  -- there is at most one o-splitting of any m
  --   decSplit   -- and it is decidable whether there is one
  --   decSlots   -- and the arity supports combining slotwise decisions
  --
  -- `splitProp` is what makes a refutation at ONE slot refute the whole
  -- tensor (`⊗-refute`), because any competing splitting IS the one you
  -- refuted.  It is unique readability, and for a syntax substrate it
  -- holds by construction.
  -- ----------------------------------------------------------------

  -- derived from uniqueness alone
  module Precise (splitProp : (o : σ .ops) (m : Sub .carrier (σ .resultSort o))
                              (p q : Sub .Split o m) → p ≡ q) where

    ⊗-refute : (o : σ .ops) (i : σ .arities o)
               (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
               (m : Sub .carrier (σ .resultSort o)) (sp : Sub .Split o m)
             → (¬G (A i)) (Sub .parts o m sp i) → (¬G (⊗ˢ o A)) m
    ⊗-refute o i A m sp k x =
      k (subst (λ z → A i (Sub .parts o m z i))
               (splitProp o m (x .fst) sp) (x .snd i))

record DecReadable {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
                   (Sub : Substrate σ ℓX ℓP) ℓA
  : Type (ℓ-max ℓS (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓX (ℓ-max ℓP (ℓ-suc ℓA)))))) where
  open DecSub Sub
  field
    -- at most one splitting: unique readability
    splitProp : (o : σ .ops) (m : Sub .carrier (σ .resultSort o))
                (p q : Sub .Split o m) → p ≡ q
    -- and it is decidable whether there is one, internally
    decSplit  : (o : σ .ops) → ⊤G ⊢ Dec⟨ ⊗ˢ o (λ _ → ⊤G) ⟩
    -- slotwise decisions combine.  This is where finiteness of the
    -- arity is used, and it is why the field cannot be dropped.
    decSlots  : (o : σ .ops)
                (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
                (m : Sub .carrier (σ .resultSort o)) (sp : Sub .Split o m)
              → ((a : σ .arities o) → Dec⟨ A a ⟩ (Sub .parts o m sp a))
              → Dec⟨ ⊗ˢ o A ⟩ m

open DecReadable public

-- ==================================================================
-- Given all that, the tensor rule for decisions.
-- ==================================================================

module DecTensor {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
                 {Sub : Substrate σ ℓX ℓP} (DR : DecReadable Sub ℓA) where

  open DecSub Sub public
  open Precise (DR .splitProp) public

  dec-⊗ : (o : σ .ops)
          (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
          (m : Sub .carrier (σ .resultSort o))
        → ((sp : Sub .Split o m) (a : σ .arities o)
           → Dec⟨ A a ⟩ (Sub .parts o m sp a))
        → Dec⟨ ⊗ˢ o A ⟩ m
  -- THE ONE PLACE the generic layer consumes a decision at a FIXED
  -- index rather than by `⊕-E`.  `⊕-E` eliminates uniformly in the
  -- index, and `d` supplies decisions only for splittings of THIS `m`,
  -- so no uniform motive exists -- not even the constant one, since its
  -- branches still quantify over the index.  The connective that moves
  -- between a slot and the whole is the residual `⊸ᶠ`, and the deciders
  -- being available only at the parts is what `▷` (TheoryGrammar.Graded)
  -- internalises; rebuilding this on `Guard.löb` is what would remove
  -- the match.  Confined to these three lines, once, for all instances.
  dec-⊗ o A m d with DR .decSplit o m tt
  ... | inl x = DR .decSlots o A m (x .fst) (d (x .fst))
  ... | inr k = dec-no (⊗ˢ o A) m (⊗-miss o A m k)
