{-
  ORDERED CONTEXTS: the free monoid.  `Split` is concatenation.

  The substrate is `Instances.Strings.Base` re-presented over `ctxSig`:
  the splitting relation, `Split3`, is imported unchanged.  An ordered
  context splits in |Γ|+1 ways -- the cuts -- and the tensor is decidable
  by induction on Γ, which is the whole content of this file.

  Splittings here are NOT unique (there are |Γ|+1 of them), so
  `DecReadable` does not apply and `Decidable.Tensor.dec-⊗` is unavailable.
  `DecSplittings` is the interface that survives.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Modes.Concat where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.List using (List; []; _∷_; _++_)

open import TheoryGrammar.Base
open import TheoryGrammar.Substrate
open import TheoryGrammar.Decidable
open import TheoryGrammar.Decidable.Splittings
open import TheoryGrammar.Instances.Lambda.Modes.Ctx

import TheoryGrammar.Instances.Strings.Base as Str

module Concat (Name : Type₀) where

  -- the splittings of the free monoid, imported verbatim
  open Str Name using (Split3; nil; cons; splitAll)

  Ctx : Type₀
  Ctx = List Name

  CSplit : (o : CtxOp) → Ctx → Type₀
  CSplit mul Γ = Σ[ u ∈ Ctx ] Σ[ v ∈ Ctx ] Split3 u v Γ

  CParts : (o : CtxOp) (Γ : Ctx) → CSplit o Γ → CtxAr o → Ctx
  CParts mul Γ (u , v , _) b = if b then u else v

  sub : Substrate ctxSig ℓ-zero ℓ-zero
  sub .carrier _         = Ctx
  sub .op mul f          = f true ++ f false
  sub .Split             = CSplit
  sub .parts             = CParts
  sub .split mul f       = f true , f false , splitAll (f true) (f false)
  sub .parts-split mul f = funExt λ { true → refl ; false → refl }

  open DecSub sub

  -- PRIMITIVE (1 of 1 for this substrate).  The cuts of a list are
  -- enumerable: `nil` is the cut before the head, `cons` recurses.
  decTen : (A : CtxAr mul → TheoryTy ℓ-zero tt) (Γ : Ctx)
         → ((sp : CSplit mul Γ) (b : CtxAr mul) → Dec⟨ A b ⟩ (CParts mul Γ sp b))
         → Dec⟨ ⊗ˢ mul A ⟩ Γ
  decTen A [] d with d ([] , [] , nil) true | d ([] , [] , nil) false
  ... | inl p | inl q = dec-yes (⊗ˢ mul A) []
                          (([] , [] , nil) , λ { true → p ; false → q })
  ... | inr k | _     = dec-no (⊗ˢ mul A) []
                          λ { ((_ , _ , nil) , h) → k (h true) }
  ... | inl _ | inr k = dec-no (⊗ˢ mul A) []
                          λ { ((_ , _ , nil) , h) → k (h false) }
  decTen A (x ∷ Γ) d = go (d nilSp true) (d nilSp false) rest
    where
    Ten : TheoryTy ℓ-zero tt
    Ten = ⊗ˢ mul A

    nilSp : CSplit mul (x ∷ Γ)
    nilSp = [] , x ∷ Γ , nil

    A' : CtxAr mul → TheoryTy ℓ-zero tt
    A' b = if b then (λ Δ → A true (x ∷ Δ)) else A false

    rest : Dec⟨ ⊗ˢ mul A' ⟩ Γ
    rest = decTen A' Γ
             λ { (u , v , r) true  → d (x ∷ u , v , cons r) true
               ; (u , v , r) false → d (x ∷ u , v , cons r) false }

    fromRest : ⊗ˢ mul A' Γ → Ten (x ∷ Γ)
    fromRest ((u , v , r) , h) =
      (x ∷ u , v , cons r) , λ { true → h true ; false → h false }

    toRest : (u v : Ctx) (r : Split3 u v Γ)
           → ((b : CtxAr mul) → A b (CParts mul (x ∷ Γ) (x ∷ u , v , cons r) b))
           → ⊗ˢ mul A' Γ
    toRest u v r h = (u , v , r) , λ { true → h true ; false → h false }

    go : Dec⟨ A true ⟩ [] → Dec⟨ A false ⟩ (x ∷ Γ) → Dec⟨ ⊗ˢ mul A' ⟩ Γ
       → Dec⟨ Ten ⟩ (x ∷ Γ)
    go (inl p) (inl q) _ =
      dec-yes Ten (x ∷ Γ) (nilSp , λ { true → p ; false → q })
    go (inl _) (inr _) (inl w) = dec-yes Ten (x ∷ Γ) (fromRest w)
    go (inr _) _       (inl w) = dec-yes Ten (x ∷ Γ) (fromRest w)
    go (inl _) (inr k) (inr k') = dec-no Ten (x ∷ Γ)
      λ { ((_ , _ , nil)    , h) → k (h false)
        ; ((_ , _ , cons r) , h) → k' (toRest _ _ r h) }
    go (inr k) _       (inr k') = dec-no Ten (x ∷ Γ)
      λ { ((_ , _ , nil)    , h) → k (h true)
        ; ((_ , _ , cons r) , h) → k' (toRest _ _ r h) }

  dec : DecSplittings sub ℓ-zero
  dec .dec-⊗ˢ mul = decTen
