{-
  RELEVANT CONTEXTS: the free commutative IDEMPOTENT monoid.  `Split` is
  interleaving WITH SHARING.

  DENOTES: `Ilv3 u v Γ` is "Γ is u and v shuffled, allowing a name to
  go to BOTH".  That one extra constructor, `both`, IS contraction:
  `A ⊢ A ⊗ A` becomes a splitting rather than a rule, so the grammar
  over this promodel is unchanged.  Nothing is ever dropped, so
  weakening is still absent -- which is exactly relevant logic.

    Ilv3      `Bags.Base`'s `Ilv` plus `both`
    ilv3App   every concatenation splits (the point's totality)
    ilv3NilJ  only `nil` lands at the empty context
    decTen    PRIMITIVE (1 of 1): one recursive call per constructor
    dec       those packaged as `DecSplittings`
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Modes.Overlap where

open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.List using (List; []; _∷_; _++_)
open import Cubical.Data.Unit
open import Cubical.Foundations.Prelude

open import TheoryGrammar.Decidable
open import TheoryGrammar.Decidable.Splittings
open import TheoryGrammar.Instances.Lambda.Modes.Ctx
open import TheoryGrammar.Instances.Lambda.Modes.Substrate

module Overlap (Name : Type₀) where

  -- `Ilv` + `both`: the ONE difference between linear and relevant
  data Ilv3 : List Name → List Name → List Name → Type₀ where
    nil   : Ilv3 [] [] []
    left  : ∀ {x u v w} → Ilv3 u v w → Ilv3 (x ∷ u) v (x ∷ w)
    right : ∀ {x u v w} → Ilv3 u v w → Ilv3 u (x ∷ v) (x ∷ w)
    both  : ∀ {x u v w} → Ilv3 u v w → Ilv3 (x ∷ u) (x ∷ v) (x ∷ w)

  ilv3App : (u v : List Name) → Ilv3 u v (u ++ v)
  ilv3App []      []      = nil
  ilv3App []      (x ∷ v) = right (ilv3App [] v)
  ilv3App (x ∷ u) v       = left (ilv3App u v)

  -- only `nil` lands at the empty context
  ilv3NilJ : ∀ {ℓ} (M : (u v : List Name) → Ilv3 u v [] → Type ℓ)
           → M [] [] nil → (u v : List Name) (r : Ilv3 u v []) → M u v r
  ilv3NilJ M m .[] .[] nil = m

  open Substrate Name Ilv3 nil ilv3App ilv3NilJ public

  -- PRIMITIVE (1 of 1 for this promodel).  Three `chain`s, one per
  -- constructor -- left, right, shared -- and only the innermost
  -- branch, where all three were refuted, enumerates them again.
  decTen : (A : Fam) (Γ : Ctx)
         → ((sp : CSplit mul Γ) (b : CtxAr mul) → Dec⟨ A b ⟩ (CParts mul Γ sp b))
         → Dec⟨ ⊗ˢ mul A ⟩ Γ
  decTen A []      d = decNil A d
  decTen A (x ∷ Γ) d =
    L.chain
      (λ kL → R.chain
        (λ kR → B.chain
          (λ kB → dec-no Ten (x ∷ Γ)
                    λ { ((_ , _ , left r)  , h) → kL (L.into _ _ r h)
                      ; ((_ , _ , right r) , h) → kR (R.into _ _ r h)
                      ; ((_ , _ , both r)  , h) → kB (B.into _ _ r h) })
          (decTen B.fam Γ (B.down d)))
        (decTen R.fam Γ (R.down d)))
      (decTen L.fam Γ (L.down d))
    where
    Ten : TheoryTy ℓ-zero tt
    Ten = ⊗ˢ mul A

    module L = Step x Γ A (λ Δ → x ∷ Δ) (λ Δ → Δ)     (λ r → left r)
    module R = Step x Γ A (λ Δ → Δ)     (λ Δ → x ∷ Δ) (λ r → right r)
    module B = Step x Γ A (λ Δ → x ∷ Δ) (λ Δ → x ∷ Δ) (λ r → both r)

  dec : DecSplittings fib ℓ-zero
  dec .dec-⊗ˢ mul = decTen
