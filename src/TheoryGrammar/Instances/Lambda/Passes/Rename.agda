{-
  THE FREE CASE, and how small it is.

  `CarrierMap.Transport` says: a carrier map preserving every splitting
  transports every inductive grammar, the only obligations being one
  per CONSTANT of the description.  So the honest question is which
  passes are split-preserving, and the answer here is sharp:

    * renaming is (`renPres`, all `Eq.refl`);

    * and NOTHING ELSE is -- `presVar`/`presApp`/`presLam` show that
      split preservation forces the three homomorphism equations, so a
      split-preserving carrier map is determined by its action on
      names, i.e. is a renaming.

  Instantiating the free transport at `Scoped` then exposes the price:
  `mapμ` keeps the nonterminal (the scope) fixed while moving the
  carrier, so the binder's representable `⌈ n ⌉` has to transport too,
  and `nmTr→id` shows that obligation forces `ρ ≡ id`.

  That is the real shape of the result.  Scope preservation is free for
  a pass exactly when the pass is the identity; every genuine pass
  fails split preservation somewhere, and `CarrierMap` localises where.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Passes.Rename where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (true; false)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.List using ([]; _∷_)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Inductive
open import TheoryGrammar.CarrierMap
open import TheoryGrammar.Instances.Lambda.Signature
open import TheoryGrammar.Instances.Lambda.Fibered
open import TheoryGrammar.Instances.Lambda.Base
open import TheoryGrammar.Instances.Lambda.Scoped

module Rename (Name : Type₀) where

  open LamBase Name
  open Wellscoped Name

  -- PRIMITIVE (carrier map): renaming, binders included.
  rename : (Name → Name) → Raw → Raw
  rename ρ (var m)   = var (ρ m)
  rename ρ (app u v) = app (rename ρ u) (rename ρ v)
  rename ρ (lam m t) = lam (ρ m) (rename ρ t)

  renCM : (Name → Name) → CarrierMap λFib
  renCM ρ .hom nm = ρ
  renCM ρ .hom tm = rename ρ

  -- PRIMITIVE: renaming preserves every splitting, everywhere `refl`.
  renPres : (ρ : Name → Name) (o : LOp) → SplitPresAt (renCM ρ) o
  renPres ρ varOp .homSplit _ (mkVar m)   = mkVar (ρ m)
  renPres ρ varOp .homParts _ (mkVar m) _ = Eq.refl
  renPres ρ appOp .homSplit _ (mkApp u v) = mkApp (rename ρ u) (rename ρ v)
  renPres ρ appOp .homParts _ (mkApp u v) true  = Eq.refl
  renPres ρ appOp .homParts _ (mkApp u v) false = Eq.refl
  renPres ρ lamOp .homSplit _ (mkLam m t) = mkLam (ρ m) (rename ρ t)
  renPres ρ lamOp .homParts _ (mkLam m t) true  = Eq.refl
  renPres ρ lamOp .homParts _ (mkLam m t) false = Eq.refl

  -- ================================================================
  -- ... and conversely: split preservation IS the homomorphism law.
  -- ================================================================

  module _ (h : CarrierMap λFib) where

    private
      vLem : (k : Name) (w : Raw) (sp : IsVar w)
           → LParts varOp w sp tt Eq.≡ h .hom nm k → w ≡ var (h .hom nm k)
      vLem k .(var j) (mkVar j) e = cong var (Eq.eqToPath e)

      aLem : (u v w : Raw) (sp : IsApp w)
           → LParts appOp w sp true  Eq.≡ h .hom tm u
           → LParts appOp w sp false Eq.≡ h .hom tm v
           → w ≡ app (h .hom tm u) (h .hom tm v)
      aLem u v .(app p q) (mkApp p q) e₁ e₂ =
        cong₂ app (Eq.eqToPath e₁) (Eq.eqToPath e₂)

      lLem : (k : Name) (t w : Raw) (sp : IsLam w)
           → LParts lamOp w sp true  Eq.≡ h .hom nm k
           → LParts lamOp w sp false Eq.≡ h .hom tm t
           → w ≡ lam (h .hom nm k) (h .hom tm t)
      lLem k t .(lam j b) (mkLam j b) e₁ e₂ =
        cong₂ lam (Eq.eqToPath e₁) (Eq.eqToPath e₂)

    presVar : SplitPresAt h varOp
            → (k : Name) → h .hom tm (var k) ≡ var (h .hom nm k)
    presVar P k =
      vLem k (h .hom tm (var k)) (P .homSplit (var k) (mkVar k))
             (P .homParts (var k) (mkVar k) tt)

    presApp : SplitPresAt h appOp
            → (u v : Raw)
            → h .hom tm (app u v) ≡ app (h .hom tm u) (h .hom tm v)
    presApp P u v =
      aLem u v (h .hom tm (app u v)) (P .homSplit (app u v) (mkApp u v))
               (P .homParts (app u v) (mkApp u v) true)
               (P .homParts (app u v) (mkApp u v) false)

    presLam : SplitPresAt h lamOp
            → (k : Name) (t : Raw)
            → h .hom tm (lam k t) ≡ lam (h .hom nm k) (h .hom tm t)
    presLam P k t =
      lLem k t (h .hom tm (lam k t)) (P .homSplit (lam k t) (mkLam k t))
               (P .homParts (lam k t) (mkLam k t) true)
               (P .homParts (lam k t) (mkLam k t) false)

    -- PRIMITIVE (induction on `Raw`).  The three equations say a
    -- split-preserving carrier map is determined by its action on
    -- names -- i.e. IS a renaming -- so one that fixes names is the
    -- identity.  With `nmTr→id` below this is the whole negative
    -- result: the only pass whose scope preservation is free is `id`.
    homId : SplitPresAt h varOp → SplitPresAt h appOp → SplitPresAt h lamOp
          → ((k : Name) → h .hom nm k ≡ k)
          → (t : Raw) → h .hom tm t ≡ t
    homId Pv Pa Pl e (var k)   = presVar Pv k ∙ cong var (e k)
    homId Pv Pa Pl e (app u v) =
      presApp Pa u v ∙ cong₂ app (homId Pv Pa Pl e u) (homId Pv Pa Pl e v)
    homId Pv Pa Pl e (lam k t) =
      presLam Pl k t ∙ cong₂ lam (e k) (homId Pv Pa Pl e t)

  -- ================================================================
  -- The free transport, instantiated at `Scoped`.
  -- ================================================================

  module _ (ρ : Name → Name) where

    module A = Along (renCM ρ)
    module T = A.Transport (renPres ρ) ℓ-zero Scope (λ _ → tm)

    -- The obligations `mapμ` leaves are exactly the CONSTANTS of
    -- `ScopedF`: the scope membership grammar, and the binder's
    -- representable.  Nothing structural is owed.
    scopedTr : ((Δ : Scope) → In Δ ⊢ A.pull (In Δ))
             → ((n : Name) → ⌈_⌉ {s = nm} n ⊢ A.pull ⌈ n ⌉)
             → (Γ : Scope) → T.Tr (ScopedF Γ)
    scopedTr inTr nmTr Γ tVar _        = lift (inTr Γ)
    scopedTr inTr nmTr Γ tApp _        = tt*
    scopedTr inTr nmTr Γ tLam n true   = lift (nmTr n)
    scopedTr inTr nmTr Γ tLam n false  = tt*

    scopedRename : ((Δ : Scope) → In Δ ⊢ A.pull (In Δ))
                 → ((n : Name) → ⌈_⌉ {s = nm} n ⊢ A.pull ⌈ n ⌉)
                 → (Γ : Scope) → Scoped Γ ⊢ A.pull (Scoped Γ)
    scopedRename inTr nmTr Γ = T.mapμ ScopedF (scopedTr inTr nmTr) Γ

    -- THE PRICE.  The binder obligation says `m Eq.≡ n → ρ m Eq.≡ n`,
    -- and at `m = n` that is `ρ n ≡ n`.  So the only renaming under
    -- which `Scoped` transports freely is the identity.
    nmTr→id : ((n : Name) → ⌈_⌉ {s = nm} n ⊢ A.pull ⌈ n ⌉)
            → (n : Name) → ρ n ≡ n
    nmTr→id nmTr n = Eq.eqToPath (nmTr n n Eq.refl)

  -- the identity renaming, with its obligations discharged
  idInTr : (Δ : Scope) → In Δ ⊢ Along.pull (renCM (λ n → n)) (In Δ)
  idInTr []      = ⊥-E
  idInTr (m ∷ Δ) = ⊕-E ⊕-I₁ (⊕-I₂ ∘g idInTr Δ)

  idNmTr : (n : Name) → ⌈_⌉ {s = nm} n ⊢ Along.pull (renCM (λ k → k)) ⌈ n ⌉
  idNmTr n _ e = e

  renId : (Γ : Scope) → Scoped Γ ⊢ Along.pull (renCM (λ n → n)) (Scoped Γ)
  renId = scopedRename (λ n → n) idInTr idNmTr
