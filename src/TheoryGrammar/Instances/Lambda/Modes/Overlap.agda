{-
  RELEVANT CONTEXTS: the free commutative IDEMPOTENT monoid.  `Split` is
  interleaving WITH SHARING.

  `Ilv3` is `Bags.Base`'s `Ilv` plus one constructor, `both`, which sends
  a name to BOTH slots.  That single constructor is contraction: `A ⊢ A ⊗ A`
  becomes a splitting rather than a rule, so the grammar over this
  promodel is unchanged.  Nothing is ever dropped, so weakening is still
  absent -- which is exactly relevant logic.

  Splittings here are NOT unique, so `Precise` (hence `⊗-refute` and
  `decSlots¹`/`decSlots²`) does not apply: a refutation has to walk the
  whole enumeration.  What the instance does NOT do is match a sum --
  every decision is consumed by the framework's `dec-elim`.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Modes.Overlap where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.List using (List; []; _∷_; _++_)

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
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

  fib : Fibered ctxSig ℓ-zero ℓ-zero
  fib .carrier _         = Ctx
  fib .Split             = CSplit
  fib .parts             = CParts

  -- The total point, separately.  As for `Interleave` the containment is
  -- strict (`both` shares a name between the slots), and the
  -- multiplicative layer below never consults it.
  point : LaxPoint fib
  point .op mul f          = f true ++ f false
  point .split mul f       = f true , f false , ilv3App (f true) (f false)
  point .parts-split mul f = funExt λ { true → refl ; false → refl }

  open DecFib fib

  -- PRIMITIVE (1 of 1 for this promodel).  Three recursive calls, one
  -- per constructor: left, right, shared.
  decTen : (A : CtxAr mul → TheoryTy ℓ-zero tt) (Γ : Ctx)
         → ((sp : CSplit mul Γ) (b : CtxAr mul) → Dec⟨ A b ⟩ (CParts mul Γ sp b))
         → Dec⟨ ⊗ˢ mul A ⟩ Γ
  decTen A [] d =
    dec-elim (A true) []
      (λ p → dec-elim (A false) []
               (λ q → dec-yes (⊗ˢ mul A) []
                        (([] , [] , nil) , λ { true → p ; false → q }))
               (λ k → dec-no (⊗ˢ mul A) []
                        λ { ((_ , _ , nil) , h) → k (h false) })
               (d ([] , [] , nil) false))
      (λ k → dec-no (⊗ˢ mul A) []
               λ { ((_ , _ , nil) , h) → k (h true) })
      (d ([] , [] , nil) true)
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

    -- one `dec-elim` per constructor of `Ilv3`; only the last branch,
    -- where every alternative was refuted, enumerates them again
    go : Dec⟨ ⊗ˢ mul AL ⟩ Γ → Dec⟨ ⊗ˢ mul AR ⟩ Γ → Dec⟨ ⊗ˢ mul AB ⟩ Γ
       → Dec⟨ Ten ⟩ (x ∷ Γ)
    go dL dR dB =
      dec-elim (⊗ˢ mul AL) Γ
        (λ w → dec-yes Ten (x ∷ Γ) (fromL w))
        (λ kL → dec-elim (⊗ˢ mul AR) Γ
          (λ w → dec-yes Ten (x ∷ Γ) (fromR w))
          (λ kR → dec-elim (⊗ˢ mul AB) Γ
            (λ w → dec-yes Ten (x ∷ Γ) (fromB w))
            (λ kB → dec-no Ten (x ∷ Γ)
                      λ { ((_ , _ , left r)  , h) → kL (toL _ _ r h)
                        ; ((_ , _ , right r) , h) → kR (toR _ _ r h)
                        ; ((_ , _ , both r)  , h) → kB (toB _ _ r h) })
            dB)
          dR)
        dL

  dec : DecSplittings fib ℓ-zero
  dec .dec-⊗ˢ mul = decTen
