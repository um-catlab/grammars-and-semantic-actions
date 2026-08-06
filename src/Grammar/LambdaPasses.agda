{-
  Compiler passes in the lambda theory.

  Everything here is a transformer OUT of `Scoped`.  The point is that
  each pass is total and unconditional: it cannot fail, because the
  property it relies on is in the index of its input rather than a
  side condition it has to re-establish.

  Two passes:
    * Scoped → de Bruijn        (a fold; total by construction)
    * a linearity judgment      (context splitting -- the SAME Split
                                 machinery, now at the CONTEXT substrate
                                 rather than the term substrate)
-}
module Grammar.LambdaPasses where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List
open import Cubical.Data.Sum
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Nat
open import Cubical.Relation.Nullary.Base

module Passes (Name : Type₀) (_≟_ : Discrete Name) where

  data Raw : Type₀ where
    var : Name → Raw
    app : Raw → Raw → Raw
    lam : Name → Raw → Raw

  Scope : Type₀
  Scope = List Name

  _∈_ : Name → Scope → Type₀
  n ∈ []      = ⊥
  n ∈ (m ∷ Γ) = (n ≡ m) ⊎ (n ∈ Γ)

  data Scoped (Γ : Scope) : Raw → Type₀ where
    var : ∀ {n}   → n ∈ Γ                    → Scoped Γ (var n)
    app : ∀ {u v} → Scoped Γ u → Scoped Γ v  → Scoped Γ (app u v)
    lam : ∀ {n t} → Scoped (n ∷ Γ) t         → Scoped Γ (lam n t)

  -- ================================================================
  -- PASS 1.  Scoped → de Bruijn.
  --
  -- Note the type: no Maybe, no error case.  Elaboration to de Bruijn
  -- is TOTAL, because "every variable is bound" lives in the index of
  -- the input rather than being a precondition to re-check.
  -- ================================================================

  data Idx : ℕ → Type₀ where
    zero : ∀ {n} → Idx (suc n)
    suc  : ∀ {n} → Idx n → Idx (suc n)

  data DB : ℕ → Type₀ where
    dvar : ∀ {n} → Idx n → DB n
    dapp : ∀ {n} → DB n → DB n → DB n
    dlam : ∀ {n} → DB (suc n) → DB n

  ix : ∀ {n Γ} → n ∈ Γ → Idx (length Γ)
  ix {Γ = m ∷ Γ} (inl _) = zero
  ix {Γ = m ∷ Γ} (inr i) = suc (ix i)

  toDB : ∀ {Γ t} → Scoped Γ t → DB (length Γ)
  toDB (var i)   = dvar (ix i)
  toDB (app a b) = dapp (toDB a) (toDB b)
  toDB (lam a)   = dlam (toDB a)

  -- the pass we actually want, on closed terms
  compile : ∀ {t} → Scoped [] t → DB 0
  compile = toDB

  -- ================================================================
  -- PASS 2.  Linearity.
  --
  -- `Merge Γ Δ Θ` is the context-splitting relation -- literally the
  -- same shape as `Split` for strings, at the substrate of CONTEXTS
  -- rather than of terms.  So the app rule is a ⊗-elimination.
  -- ================================================================

  data Merge : Scope → Scope → Scope → Type₀ where
    nil   : Merge [] [] []
    left  : ∀ {n Γ Δ Θ} → Merge Γ Δ Θ → Merge (n ∷ Γ) Δ (n ∷ Θ)
    right : ∀ {n Γ Δ Θ} → Merge Γ Δ Θ → Merge Γ (n ∷ Δ) (n ∷ Θ)

  data Lin : Scope → Raw → Type₀ where
    var : ∀ {n} → Lin (n ∷ []) (var n)
    app : ∀ {Γ Δ Θ u v} → Merge Γ Δ Θ → Lin Γ u → Lin Δ v → Lin Θ (app u v)
    lam : ∀ {Γ n t} → Lin (n ∷ Γ) t → Lin Γ (lam n t)

  -- linear terms are scoped: the merge is absorbed into the ambient scope
  merge-∈ˡ : ∀ {n Γ Δ Θ} → Merge Γ Δ Θ → n ∈ Γ → n ∈ Θ
  merge-∈ˡ (left  m) (inl p) = inl p
  merge-∈ˡ (left  m) (inr i) = inr (merge-∈ˡ m i)
  merge-∈ˡ (right m) i       = inr (merge-∈ˡ m i)

  merge-∈ʳ : ∀ {n Γ Δ Θ} → Merge Γ Δ Θ → n ∈ Δ → n ∈ Θ
  merge-∈ʳ (left  m) i       = inr (merge-∈ʳ m i)
  merge-∈ʳ (right m) (inl p) = inl p
  merge-∈ʳ (right m) (inr i) = inr (merge-∈ʳ m i)

  weaken : ∀ {Γ Θ t} → (∀ {n} → n ∈ Γ → n ∈ Θ) → Scoped Γ t → Scoped Θ t
  weaken w (var i)   = var (w i)
  weaken w (app a b) = app (weaken w a) (weaken w b)
  weaken w (lam a)   = lam (weaken (λ { (inl p) → inl p ; (inr i) → inr (w i) }) a)

  -- THEOREM: linear ⟹ scoped.  A soundness result relating the two
  -- judgments, i.e. the substructural pass refines the structural one.
  lin→scoped : ∀ {Γ t} → Lin Γ t → Scoped Γ t
  lin→scoped var           = var (inl refl)
  lin→scoped (app m a b)   =
    app (weaken (merge-∈ˡ m) (lin→scoped a)) (weaken (merge-∈ʳ m) (lin→scoped b))
  lin→scoped (lam a)       = lam (lin→scoped a)
