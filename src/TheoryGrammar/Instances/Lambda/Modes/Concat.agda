{-
  ORDERED CONTEXTS: the free monoid.  `Split` is concatenation.

  The promodel is `Instances.Strings.Base` re-presented over `ctxSig`:
  the splitting relation, `Split3`, is imported unchanged.  An ordered
  context splits in |Γ|+1 ways -- the cuts -- and the tensor is decidable
  by induction on Γ, which is the whole content of this file.

  Splittings here are NOT unique (there are |Γ|+1 of them), so
  `DecReadable` does not apply and `Decidable.Tensor.dec-⊗` is unavailable.
  `DecSplittings` is the interface that survives.  For the same reason
  `Precise`'s `⊗-refute` -- and so `decSlots¹`/`decSlots²` -- is out of
  reach: refuting one cut refutes nothing.  What the instance does NOT
  do is match a sum -- every decision is consumed by `dec-elim`.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Modes.Concat where

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

  fib : Fibered ctxSig ℓ-zero ℓ-zero
  fib .carrier _         = Ctx
  fib .Split             = CSplit
  fib .parts             = CParts

  -- The total point, separately: concatenation IS total here, so nothing
  -- is lost by the split.  What it buys is that the multiplicative layer
  -- below (`DecFib fib`, `⊗ˢ`) never consults it.
  point : LaxPoint fib
  point .op mul f          = f true ++ f false
  point .split mul f       = f true , f false , splitAll (f true) (f false)
  point .parts-split mul f = funExt λ { true → refl ; false → refl }

  open DecFib fib

  -- PRIMITIVE (1 of 1 for this promodel).  The cuts of a list are
  -- enumerable: `nil` is the cut before the head, `cons` recurses.
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
  decTen A (x ∷ Γ) d = go (d nilSp true) (d nilSp false)
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

    -- the slots of the nil cut -- the one cut `rest` does not range over
    NilSlots : Type ℓ-zero
    NilSlots = (b : CtxAr mul) → A b (CParts mul (x ∷ Γ) nilSp b)

    -- All other cuts are `rest`'s, so a caller that has already refuted
    -- the nil cut finishes here.  `rest` is forced only on this path,
    -- which is what keeps the nil cut a short circuit.
    onRest : (NilSlots → ⊥G {tt} (x ∷ Γ)) → Dec⟨ Ten ⟩ (x ∷ Γ)
    onRest kn =
      dec-elim (⊗ˢ mul A') Γ
        (λ w → dec-yes Ten (x ∷ Γ) (fromRest w))
        (λ k' → dec-no Ten (x ∷ Γ)
                  λ { ((_ , _ , nil)    , h) → kn h
                    ; ((_ , _ , cons r) , h) → k' (toRest _ _ r h) })
        rest

    go : Dec⟨ A true ⟩ [] → Dec⟨ A false ⟩ (x ∷ Γ) → Dec⟨ Ten ⟩ (x ∷ Γ)
    go dt df =
      dec-elim (A true) []
        (λ p → dec-elim (A false) (x ∷ Γ)
                 (λ q → dec-yes Ten (x ∷ Γ)
                          (nilSp , λ { true → p ; false → q }))
                 (λ k → onRest (λ h → k (h false)))
                 df)
        (λ k → onRest (λ h → k (h true)))
        dt

  dec : DecSplittings fib ℓ-zero
  dec .dec-⊗ˢ mul = decTen
