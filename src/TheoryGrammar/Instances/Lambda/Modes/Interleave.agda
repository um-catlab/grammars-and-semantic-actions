{-
  LINEAR (and AFFINE) CONTEXTS: the free COMMUTATIVE monoid.  `Split` is
  interleaving -- exchange, but no weakening and no contraction.

  The promodel is `Instances.Bags.Base` re-presented over `ctxSig`: the
  splitting relation, `Ilv`, is imported unchanged.  A context of length n
  interleaves in 2ⁿ ways; the tensor is still decidable, by induction on Γ
  with one recursive call per constructor of `Ilv`.

  Affine reuses this promodel untouched -- it differs only in the leaf.

  Splittings here are NOT unique, so `Precise` (hence `⊗-refute` and
  `decSlots¹`/`decSlots²`) does not apply: a refutation has to walk the
  whole enumeration.  What the instance does NOT do is match a sum --
  every decision is consumed by the framework's `dec-elim`.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Modes.Interleave where

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

import TheoryGrammar.Instances.Bags.Base as Bg

module Interleave (Name : Type₀) where

  -- the splittings of the free commutative monoid, imported verbatim
  open Bg Name using (Ilv; nil; left; right; ilvApp)

  Ctx : Type₀
  Ctx = List Name

  CSplit : (o : CtxOp) → Ctx → Type₀
  CSplit mul Γ = Σ[ u ∈ Ctx ] Σ[ v ∈ Ctx ] Ilv u v Γ

  CParts : (o : CtxOp) (Γ : Ctx) → CSplit o Γ → CtxAr o → Ctx
  CParts mul Γ (u , v , _) b = if b then u else v

  fib : Fibered ctxSig ℓ-zero ℓ-zero
  fib .carrier _         = Ctx
  fib .Split             = CSplit
  fib .parts             = CParts

  -- The total point, separately.  Note the containment is STRICT here:
  -- `Ilv u v w` does not imply `u ++ v ≡ w`, so this really is a lax
  -- point, and the multiplicative layer below never consults it.
  point : LaxPoint fib
  point .op mul f          = f true ++ f false
  point .split mul f       = f true , f false , ilvApp (f true) (f false)
  point .parts-split mul f = funExt λ { true → refl ; false → refl }

  open DecFib fib

  -- PRIMITIVE (1 of 1 for this promodel).  Each name of Γ goes left or
  -- right; the two recursive calls are the two constructors of `Ilv`.
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
  decTen A (x ∷ Γ) d = go decL decR
    where
    Ten : TheoryTy ℓ-zero tt
    Ten = ⊗ˢ mul A

    AL AR : CtxAr mul → TheoryTy ℓ-zero tt
    AL b = if b then (λ Δ → A true (x ∷ Δ)) else A false
    AR b = if b then A true else (λ Δ → A false (x ∷ Δ))

    decL : Dec⟨ ⊗ˢ mul AL ⟩ Γ
    decL = decTen AL Γ
             λ { (u , v , r) true  → d (x ∷ u , v , left r) true
               ; (u , v , r) false → d (x ∷ u , v , left r) false }

    decR : Dec⟨ ⊗ˢ mul AR ⟩ Γ
    decR = decTen AR Γ
             λ { (u , v , r) true  → d (u , x ∷ v , right r) true
               ; (u , v , r) false → d (u , x ∷ v , right r) false }

    fromL : ⊗ˢ mul AL Γ → Ten (x ∷ Γ)
    fromL ((u , v , r) , h) =
      (x ∷ u , v , left r) , λ { true → h true ; false → h false }

    fromR : ⊗ˢ mul AR Γ → Ten (x ∷ Γ)
    fromR ((u , v , r) , h) =
      (u , x ∷ v , right r) , λ { true → h true ; false → h false }

    toL : (u v : Ctx) (r : Ilv u v Γ)
        → ((b : CtxAr mul) → A b (CParts mul (x ∷ Γ) (x ∷ u , v , left r) b))
        → ⊗ˢ mul AL Γ
    toL u v r h = (u , v , r) , λ { true → h true ; false → h false }

    toR : (u v : Ctx) (r : Ilv u v Γ)
        → ((b : CtxAr mul) → A b (CParts mul (x ∷ Γ) (u , x ∷ v , right r) b))
        → ⊗ˢ mul AR Γ
    toR u v r h = (u , v , r) , λ { true → h true ; false → h false }

    -- one `dec-elim` per constructor of `Ilv`; only the last branch,
    -- where every alternative was refuted, enumerates them again
    go : Dec⟨ ⊗ˢ mul AL ⟩ Γ → Dec⟨ ⊗ˢ mul AR ⟩ Γ → Dec⟨ Ten ⟩ (x ∷ Γ)
    go dL dR =
      dec-elim (⊗ˢ mul AL) Γ
        (λ w → dec-yes Ten (x ∷ Γ) (fromL w))
        (λ kL → dec-elim (⊗ˢ mul AR) Γ
                  (λ w → dec-yes Ten (x ∷ Γ) (fromR w))
                  (λ kR → dec-no Ten (x ∷ Γ)
                            λ { ((_ , _ , left r)  , h) → kL (toL _ _ r h)
                              ; ((_ , _ , right r) , h) → kR (toR _ _ r h) })
                  dR)
        dL

  dec : DecSplittings fib ℓ-zero
  dec .dec-⊗ˢ mul = decTen
