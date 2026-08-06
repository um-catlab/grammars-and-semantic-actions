{-
  Decidability through a tensor, the OTHER way.

  `Decidable.Tensor` decides `⊗ˢ o A` from `splitProp` -- at most one
  splitting.  That is unique readability: true for a free signature, and
  FALSE for the monoid (`w` has `length w + 1` cuts) and for bags (`2ⁿ`
  interleavings).  So neither of those instances can use it.

  The complementary hypothesis is that the splittings are finitely
  ENUMERABLE.  Then a refutation is "none of the listed splittings
  works", and completeness of the enumeration turns that into a
  refutation of the tensor.  `splitProp` is the degenerate case where
  the list is a singleton.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Decidable.Enumerated where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.List
open import Cubical.Data.Empty using (⊥*)

open import TheoryGrammar.Base
open import TheoryGrammar.Substrate
open import TheoryGrammar.Rules
open import TheoryGrammar.RulesSub
open import TheoryGrammar.Decidable.Additive
open import TheoryGrammar.Decidable.Tensor

private variable ℓS ℓ ℓ' ℓX ℓP ℓA ℓM : Level

data _∈L_ {X : Type ℓM} (x : X) : List X → Type ℓM where
  here  : {xs : List X} → x ∈L (x ∷ xs)
  there : {y : X} {xs : List X} → x ∈L xs → x ∈L (y ∷ xs)

module DecEnum {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
               (Sub : Substrate σ ℓX ℓP) where

  open DecSub Sub public

  -- the tensor restricted to ONE splitting.  `⊗ˢ o A m` is `Σ` of this
  -- over the splittings, definitionally.
  ⊗at : (o : σ .ops) (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
        (m : Sub .carrier (σ .resultSort o)) → Sub .Split o m → Type (ℓ-max ℓ' ℓA)
  ⊗at o A m sp = (a : σ .arities o) → A a (Sub .parts o m sp a)

  Refutes : (o : σ .ops) (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
            (m : Sub .carrier (σ .resultSort o)) → Sub .Split o m → Type (ℓ-max ℓ' ℓA)
  Refutes o A m sp = ⊗at o A m sp → ⊥* {ℓ-zero}

  -- every splitting in a list is refuted
  AllNo : (o : σ .ops) (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
          (m : Sub .carrier (σ .resultSort o))
        → List (Sub .Split o m) → Type (ℓ-max ℓ' ℓA)
  AllNo o A m []         = Unit*
  AllNo o A m (sp ∷ sps) = Refutes o A m sp × AllNo o A m sps

  -- ... so any splitting IN the list is refuted
  lookupNo : (o : σ .ops) (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
             (m : Sub .carrier (σ .resultSort o))
             (sps : List (Sub .Split o m)) (sp : Sub .Split o m)
           → sp ∈L sps → AllNo o A m sps → Refutes o A m sp
  lookupNo o A m (sp ∷ sps) .sp here      (k , _) = k
  lookupNo o A m (_  ∷ sps) sp  (there p) (_ , r) = lookupNo o A m sps sp p r

-- ==================================================================
-- The hypothesis.
-- ==================================================================

record DecEnumerable {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
                     (Sub : Substrate σ ℓX ℓP) ℓA
  : Type (ℓ-max ℓS (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓX (ℓ-max ℓP (ℓ-suc ℓA)))))) where
  open DecEnum Sub
  field
    -- the splittings of any `m` are finitely many ...
    enumSplit    : (o : σ .ops) (m : Sub .carrier (σ .resultSort o))
                 → List (Sub .Split o m)
    -- ... and the list misses none.  THIS is what turns "no listed
    -- splitting works" into a refutation of the tensor.
    enumComplete : (o : σ .ops) (m : Sub .carrier (σ .resultSort o))
                   (sp : Sub .Split o m) → sp ∈L enumSplit o m
    -- and slotwise decisions combine AT one splitting.  A plain `⊎`,
    -- because the index is fixed -- the same concession `dec-⊗` makes,
    -- and for the same reason: `⊕-E` eliminates uniformly in the index.
    decAt        : (o : σ .ops)
                   (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
                   (m : Sub .carrier (σ .resultSort o)) (sp : Sub .Split o m)
                 → ((a : σ .arities o) → Dec⟨ A a ⟩ (Sub .parts o m sp a))
                 → ⊗at o A m sp ⊎ Refutes o A m sp

open DecEnumerable public

-- ==================================================================
-- The tensor rule.
-- ==================================================================

module DecTensorEnum {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
                     {Sub : Substrate σ ℓX ℓP} (DE : DecEnumerable Sub ℓA) where

  open DecEnum Sub public

  module _ (o : σ .ops)
           (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
           (m : Sub .carrier (σ .resultSort o))
           (d : (sp : Sub .Split o m) (a : σ .arities o)
              → Dec⟨ A a ⟩ (Sub .parts o m sp a)) where

    private
      -- walk the enumeration: a witness, or a refutation of every entry
      search : (sps : List (Sub .Split o m))
             → (Σ[ sp ∈ Sub .Split o m ] ⊗at o A m sp) ⊎ AllNo o A m sps
      search []         = inr tt*
      search (sp ∷ sps) = step (DE .decAt o A m sp (d sp))
        where
          step : ⊗at o A m sp ⊎ Refutes o A m sp
               → (Σ[ q ∈ Sub .Split o m ] ⊗at o A m q) ⊎ AllNo o A m (sp ∷ sps)
          step (inl h) = inl (sp , h)
          step (inr k) = more (search sps)
            where more : (Σ[ q ∈ Sub .Split o m ] ⊗at o A m q) ⊎ AllNo o A m sps
                       → (Σ[ q ∈ Sub .Split o m ] ⊗at o A m q)
                         ⊎ AllNo o A m (sp ∷ sps)
                  more (inl y) = inl y
                  more (inr r) = inr (k , r)

      finish : (Σ[ sp ∈ Sub .Split o m ] ⊗at o A m sp)
               ⊎ AllNo o A m (DE .enumSplit o m)
             → Dec⟨ ⊗ˢ o A ⟩ m
      finish (inl (sp , h)) = dec-yes (⊗ˢ o A) m (sp , h)
      finish (inr all)      = dec-no  (⊗ˢ o A) m
        λ x → lookupNo o A m (DE .enumSplit o m) (x .fst)
                       (DE .enumComplete o m (x .fst)) all (x .snd)

    dec-⊗-enum : Dec⟨ ⊗ˢ o A ⟩ m
    dec-⊗-enum = finish (search (DE .enumSplit o m))
