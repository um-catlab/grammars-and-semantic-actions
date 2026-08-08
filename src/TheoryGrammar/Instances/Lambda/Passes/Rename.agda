{- THE FREE CASE, and how small it is. `CarrierMap.Transport`: a carrier
   map preserving every splitting transports every inductive grammar, owing
   one obligation per CONSTANT of the description. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Passes.Rename where

open import Cubical.Data.Bool using (true; false)
open import Cubical.Data.List using ([]; _∷_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Foundations.Prelude
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.CarrierMap
open import TheoryGrammar.Inductive
open import TheoryGrammar.Instances.Lambda.Base
open import TheoryGrammar.Instances.Lambda.Fibered
open import TheoryGrammar.Instances.Lambda.Scoped
open import TheoryGrammar.Instances.Lambda.Signature

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

  -- ... and conversely: split preservation IS the homomorphism law.

  module _ (h : CarrierMap λFib) where

    -- INVERSION.  A splitting witness at `w` pins `w`'s shape, and only
    -- once it is pinned do `LParts`' equations reduce.  Each says: `w`
    -- is the node its splitting claims, built from `h`'s images.

    shape-var : (k : Name) (w : Raw) (sp : IsVar w)
              → LParts varOp w sp tt Eq.≡ h .hom nm k → w ≡ var (h .hom nm k)
    shape-var k .(var j) (mkVar j) e = cong var (Eq.eqToPath e)

    shape-app : (u v w : Raw) (sp : IsApp w)
              → LParts appOp w sp true  Eq.≡ h .hom tm u
              → LParts appOp w sp false Eq.≡ h .hom tm v
              → w ≡ app (h .hom tm u) (h .hom tm v)
    shape-app u v .(app p q) (mkApp p q) e₁ e₂ =
      cong₂ app (Eq.eqToPath e₁) (Eq.eqToPath e₂)

    shape-lam : (k : Name) (t w : Raw) (sp : IsLam w)
              → LParts lamOp w sp true  Eq.≡ h .hom nm k
              → LParts lamOp w sp false Eq.≡ h .hom tm t
              → w ≡ lam (h .hom nm k) (h .hom tm t)
    shape-lam k t .(lam j b) (mkLam j b) e₁ e₂ =
      cong₂ lam (Eq.eqToPath e₁) (Eq.eqToPath e₂)

    -- THE HOMOMORPHISM EQUATIONS, one per operation, each derived from
    -- split preservation at that operation alone.

    hom-var : SplitPresAt h varOp
            → (k : Name) → h .hom tm (var k) ≡ var (h .hom nm k)
    hom-var P k =
      shape-var k (h .hom tm (var k)) (P .homSplit (var k) (mkVar k))
                  (P .homParts (var k) (mkVar k) tt)

    hom-app : SplitPresAt h appOp
            → (u v : Raw)
            → h .hom tm (app u v) ≡ app (h .hom tm u) (h .hom tm v)
    hom-app P u v =
      shape-app u v (h .hom tm (app u v)) (P .homSplit (app u v) (mkApp u v))
                    (P .homParts (app u v) (mkApp u v) true)
                    (P .homParts (app u v) (mkApp u v) false)

    hom-lam : SplitPresAt h lamOp
            → (k : Name) (t : Raw)
            → h .hom tm (lam k t) ≡ lam (h .hom nm k) (h .hom tm t)
    hom-lam P k t =
      shape-lam k t (h .hom tm (lam k t)) (P .homSplit (lam k t) (mkLam k t))
                    (P .homParts (lam k t) (mkLam k t) true)
                    (P .homParts (lam k t) (mkLam k t) false)

    -- PRIMITIVE (induction on `Raw`). The three equations say a split-
    -- preserving carrier map is determined by its action on names -- i.e.
    homId : SplitPresAt h varOp → SplitPresAt h appOp → SplitPresAt h lamOp
          → ((k : Name) → h .hom nm k ≡ k)
          → (t : Raw) → h .hom tm t ≡ t
    homId Pv Pa Pl e (var k)   = hom-var Pv k ∙ cong var (e k)
    homId Pv Pa Pl e (app u v) =
      hom-app Pa u v ∙ cong₂ app (homId Pv Pa Pl e u) (homId Pv Pa Pl e v)
    homId Pv Pa Pl e (lam k t) =
      hom-lam Pl k t ∙ cong₂ lam (e k) (homId Pv Pa Pl e t)

  -- The free transport, instantiated at `Scoped`.

  module _ (ρ : Name → Name) where

    module A = Along (renCM ρ)
    module T = Transport (renCM ρ) (renPres ρ) ℓ-zero Scope (λ _ → tm)

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
    nmTr→ρ≡id : ((n : Name) → ⌈_⌉ {s = nm} n ⊢ A.pull ⌈ n ⌉)
              → (n : Name) → ρ n ≡ n
    nmTr→ρ≡id nmTr n = Eq.eqToPath (nmTr n n Eq.refl)

  -- the identity renaming, with its obligations discharged
  idInTr : (Δ : Scope) → In Δ ⊢ Along.pull (renCM (λ n → n)) (In Δ)
  idInTr []      = ⊥-E
  idInTr (m ∷ Δ) = ⊕-E ⊕-I₁ (⊕-I₂ ∘g idInTr Δ)

  idNmTr : (n : Name) → ⌈_⌉ {s = nm} n ⊢ Along.pull (renCM (λ k → k)) ⌈ n ⌉
  idNmTr n _ e = e

  renId : (Γ : Scope) → Scoped Γ ⊢ Along.pull (renCM (λ n → n)) (Scoped Γ)
  renId = scopedRename (λ n → n) idInTr idNmTr
