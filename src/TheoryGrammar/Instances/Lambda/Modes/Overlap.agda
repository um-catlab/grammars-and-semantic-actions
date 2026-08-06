{-
  RELEVANT CONTEXTS: the free commutative IDEMPOTENT monoid.  `Split` is
  interleaving WITH SHARING.

  `Ilv3` is `Bags.Base`'s `Ilv` plus one constructor, `both`, which sends
  a name to BOTH slots.  That single constructor is contraction: `A ⊢ A ⊗ A`
  becomes a splitting rather than a rule, so the grammar over this
  substrate is unchanged.  Nothing is ever dropped, so weakening is still
  absent -- which is exactly relevant logic.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Modes.Overlap where

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

module Overlap (Name : Type₀) where

  Ctx : Type₀
  Ctx = List Name

  -- `Ilv` + `both`: the ONE difference between linear and relevant
  data Ilv3 : Ctx → Ctx → Ctx → Type₀ where
    nil   : Ilv3 [] [] []
    left  : ∀ {x u v w} → Ilv3 u v w → Ilv3 (x ∷ u) v (x ∷ w)
    right : ∀ {x u v w} → Ilv3 u v w → Ilv3 u (x ∷ v) (x ∷ w)
    both  : ∀ {x u v w} → Ilv3 u v w → Ilv3 (x ∷ u) (x ∷ v) (x ∷ w)

  ilv3App : (u v : Ctx) → Ilv3 u v (u ++ v)
  ilv3App []      []      = nil
  ilv3App []      (x ∷ v) = right (ilv3App [] v)
  ilv3App (x ∷ u) v       = left (ilv3App u v)

  CSplit : (o : CtxOp) → Ctx → Type₀
  CSplit mul Γ = Σ[ u ∈ Ctx ] Σ[ v ∈ Ctx ] Ilv3 u v Γ

  CParts : (o : CtxOp) (Γ : Ctx) → CSplit o Γ → CtxAr o → Ctx
  CParts mul Γ (u , v , _) b = if b then u else v

  sub : Substrate ctxSig ℓ-zero ℓ-zero
  sub .carrier _         = Ctx
  sub .op mul f          = f true ++ f false
  sub .Split             = CSplit
  sub .parts             = CParts
  sub .split mul f       = f true , f false , ilv3App (f true) (f false)
  sub .parts-split mul f = funExt λ { true → refl ; false → refl }

  open DecSub sub

  -- PRIMITIVE (1 of 1 for this substrate).  Three recursive calls, one
  -- per constructor: left, right, shared.
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
  decTen A (x ∷ Γ) d = go decL decR decB
    where
    Ten : TheoryTy ℓ-zero tt
    Ten = ⊗ˢ mul A

    AL AR AB : CtxAr mul → TheoryTy ℓ-zero tt
    AL b = if b then (λ Δ → A true (x ∷ Δ)) else A false
    AR b = if b then A true else (λ Δ → A false (x ∷ Δ))
    AB b = λ Δ → A b (x ∷ Δ)

    decL : Dec⟨ ⊗ˢ mul AL ⟩ Γ
    decL = decTen AL Γ
             λ { (u , v , r) true  → d (x ∷ u , v , left r) true
               ; (u , v , r) false → d (x ∷ u , v , left r) false }

    decR : Dec⟨ ⊗ˢ mul AR ⟩ Γ
    decR = decTen AR Γ
             λ { (u , v , r) true  → d (u , x ∷ v , right r) true
               ; (u , v , r) false → d (u , x ∷ v , right r) false }

    decB : Dec⟨ ⊗ˢ mul AB ⟩ Γ
    decB = decTen AB Γ
             λ { (u , v , r) true  → d (x ∷ u , x ∷ v , both r) true
               ; (u , v , r) false → d (x ∷ u , x ∷ v , both r) false }

    fromL : ⊗ˢ mul AL Γ → Ten (x ∷ Γ)
    fromL ((u , v , r) , h) =
      (x ∷ u , v , left r) , λ { true → h true ; false → h false }

    fromR : ⊗ˢ mul AR Γ → Ten (x ∷ Γ)
    fromR ((u , v , r) , h) =
      (u , x ∷ v , right r) , λ { true → h true ; false → h false }

    fromB : ⊗ˢ mul AB Γ → Ten (x ∷ Γ)
    fromB ((u , v , r) , h) =
      (x ∷ u , x ∷ v , both r) , λ { true → h true ; false → h false }

    toL : (u v : Ctx) (r : Ilv3 u v Γ)
        → ((b : CtxAr mul) → A b (CParts mul (x ∷ Γ) (x ∷ u , v , left r) b))
        → ⊗ˢ mul AL Γ
    toL u v r h = (u , v , r) , λ { true → h true ; false → h false }

    toR : (u v : Ctx) (r : Ilv3 u v Γ)
        → ((b : CtxAr mul) → A b (CParts mul (x ∷ Γ) (u , x ∷ v , right r) b))
        → ⊗ˢ mul AR Γ
    toR u v r h = (u , v , r) , λ { true → h true ; false → h false }

    toB : (u v : Ctx) (r : Ilv3 u v Γ)
        → ((b : CtxAr mul) → A b (CParts mul (x ∷ Γ) (x ∷ u , x ∷ v , both r) b))
        → ⊗ˢ mul AB Γ
    toB u v r h = (u , v , r) , λ { true → h true ; false → h false }

    go : Dec⟨ ⊗ˢ mul AL ⟩ Γ → Dec⟨ ⊗ˢ mul AR ⟩ Γ → Dec⟨ ⊗ˢ mul AB ⟩ Γ
       → Dec⟨ Ten ⟩ (x ∷ Γ)
    go (inl w)  _        _       = dec-yes Ten (x ∷ Γ) (fromL w)
    go (inr _) (inl w)   _       = dec-yes Ten (x ∷ Γ) (fromR w)
    go (inr _) (inr _)  (inl w)  = dec-yes Ten (x ∷ Γ) (fromB w)
    go (inr kL) (inr kR) (inr kB) = dec-no Ten (x ∷ Γ)
      λ { ((_ , _ , left r)  , h) → kL (toL _ _ r h)
        ; ((_ , _ , right r) , h) → kR (toR _ _ r h)
        ; ((_ , _ , both r)  , h) → kB (toB _ _ r h) }

  dec : DecSplittings sub ℓ-zero
  dec .dec-⊗ˢ mul = decTen
