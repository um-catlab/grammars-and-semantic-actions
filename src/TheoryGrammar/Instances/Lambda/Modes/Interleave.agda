{-
  LINEAR (and AFFINE) CONTEXTS: the free COMMUTATIVE monoid.  `Split` is
  interleaving -- exchange, but no weakening and no contraction.

  DENOTES: `Ilv u v Γ` is "Γ is u and v shuffled", so a context of
  length n splits in 2ⁿ ways.  `Bags.Base` supplies the relation
  unchanged and `Modes.Substrate` everything not specific to it --

    ilvNilJ  only `nil` lands at the empty context
    decTen   PRIMITIVE (1 of 1): the tensor, by induction on Γ, one
             recursive call per constructor of `Ilv`
    dec      those two, packaged as `DecSplittings`

  Affine reuses this promodel untouched -- it differs only in the leaf.
  Splittings are NOT unique, so `Precise` (hence `⊗-refute` and
  `decSlots¹/²`) does not apply: refuting needs the whole enumeration.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Modes.Interleave where

open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Unit
open import Cubical.Foundations.Prelude

open import TheoryGrammar.Decidable
open import TheoryGrammar.Decidable.Splittings
open import TheoryGrammar.Instances.Lambda.Modes.Ctx
open import TheoryGrammar.Instances.Lambda.Modes.Substrate

import TheoryGrammar.Instances.Bags.Base as Bg

module Interleave (Name : Type₀) where

  -- the splittings of the free commutative monoid, imported verbatim
  open Bg Name using (Ilv; nil; left; right; ilvApp)

  -- only `nil` lands at the empty context
  ilvNilJ : ∀ {ℓ} (M : (u v : List Name) → Ilv u v [] → Type ℓ)
          → M [] [] nil → (u v : List Name) (r : Ilv u v []) → M u v r
  ilvNilJ M m .[] .[] nil = m

  open Substrate Name Ilv nil ilvApp ilvNilJ public

  -- PRIMITIVE (1 of 1 for this promodel).  Each name of Γ goes left or
  -- right; the two `chain`s are the two constructors of `Ilv`, and only
  -- the innermost branch -- where both were refuted -- enumerates them
  -- again.
  decTen : (A : Fam) (Γ : Ctx)
         → ((sp : CSplit mul Γ) (b : CtxAr mul) → Dec⟨ A b ⟩ (CParts mul Γ sp b))
         → Dec⟨ ⊗ˢ mul A ⟩ Γ
  decTen A []      d = decNil A d
  decTen A (x ∷ Γ) d =
    L.chain
      (λ kL → R.chain
        (λ kR → dec-no Ten (x ∷ Γ)
                  λ { ((_ , _ , left r)  , h) → kL (L.into _ _ r h)
                    ; ((_ , _ , right r) , h) → kR (R.into _ _ r h) })
        (decTen R.fam Γ (R.down d)))
      (decTen L.fam Γ (L.down d))
    where
    Ten : TheoryTy ℓ-zero tt
    Ten = ⊗ˢ mul A

    module L = Step x Γ A (λ Δ → x ∷ Δ) (λ Δ → Δ) (λ r → left r)
    module R = Step x Γ A (λ Δ → Δ) (λ Δ → x ∷ Δ) (λ r → right r)

  dec : DecSplittings fib ℓ-zero
  dec .dec-⊗ˢ mul = decTen
