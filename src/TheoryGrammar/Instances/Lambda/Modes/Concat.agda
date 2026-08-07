{-
  ORDERED CONTEXTS: the free monoid.  `Split` is concatenation.

  DENOTES: `Split3 u v Γ` is "Γ is u followed by v", so a context of
  length n splits in exactly n+1 ways -- the cuts.  `Strings.Base`
  supplies the relation unchanged and `Modes.Substrate` everything not
  specific to it, leaving three things here --

    splitNilJ  only `nil` lands at the empty context
    decTen     PRIMITIVE (1 of 1): the tensor, by induction on Γ.  `nil`
               is available at EVERY context, so the cut before the head
               is a case of its own and the recursion follows `cons`.
    dec        those two, packaged as `DecSplittings`

  Splittings are NOT unique, so `DecReadable`, `dec-⊗` and `Precise`'s
  `⊗-refute` are out of reach: refuting one cut refutes nothing.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Modes.Concat where

open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Unit
open import Cubical.Foundations.Prelude

open import TheoryGrammar.Decidable
open import TheoryGrammar.Decidable.Splittings
open import TheoryGrammar.Instances.Lambda.Modes.Ctx
open import TheoryGrammar.Instances.Lambda.Modes.Substrate

import TheoryGrammar.Instances.Strings.Base as Str

module Concat (Name : Type₀) where

  -- the splittings of the free monoid, imported verbatim
  open Str Name using (Split3; nil; cons; splitAll)

  -- only `nil` lands at the empty context
  splitNilJ : ∀ {ℓ} (M : (u v : List Name) → Split3 u v [] → Type ℓ)
            → M [] [] nil → (u v : List Name) (r : Split3 u v []) → M u v r
  splitNilJ M m .[] .[] nil = m

  open Substrate Name Split3 nil splitAll splitNilJ public

  -- PRIMITIVE (1 of 1 for this promodel).  The cuts of a list are
  -- enumerable: `nil` is the cut before the head, `cons` recurses.  The
  -- recursive call is forced only once the nil cut has been refuted,
  -- which is what keeps that cut a short circuit.
  decTen : (A : Fam) (Γ : Ctx)
         → ((sp : CSplit mul Γ) (b : CtxAr mul) → Dec⟨ A b ⟩ (CParts mul Γ sp b))
         → Dec⟨ ⊗ˢ mul A ⟩ Γ
  decTen A []      d = decNil A d
  decTen A (x ∷ Γ) d = decSp A (x ∷ Γ) cut hit miss (d cut true) (d cut false)
    where
    Ten : TheoryTy ℓ-zero tt
    Ten = ⊗ˢ mul A

    -- the cut before the head: the one splitting the recursion misses
    cut : CSplit mul (x ∷ Γ)
    cut = [] , x ∷ Γ , nil

    module C = Step x Γ A (λ Δ → x ∷ Δ) (λ Δ → Δ) (λ r → cons r)

    hit : Slots A (x ∷ Γ) cut → Dec⟨ Ten ⟩ (x ∷ Γ)
    hit h = dec-yes Ten (x ∷ Γ) (cut , h)

    -- the nil cut is refuted, so try `cons`; if that fails too, every
    -- splitting has been named and the refutation is complete
    miss : (Slots A (x ∷ Γ) cut → ⊥G {tt} (x ∷ Γ)) → Dec⟨ Ten ⟩ (x ∷ Γ)
    miss kn =
      C.chain (λ k → dec-no Ten (x ∷ Γ)
                       λ { ((_ , _ , nil)    , h) → kn h
                         ; ((_ , _ , cons r) , h) → k (C.into _ _ r h) })
              (decTen C.fam Γ (C.down d))

  dec : DecSplittings fib ℓ-zero
  dec .dec-⊗ˢ mul = decTen
