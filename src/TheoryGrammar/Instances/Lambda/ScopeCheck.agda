{- The scope checker `check`, a map of the calculus at `DecScoped`: ⊤ ⊢ &ᴰ
   Scope (λ Δ → Scoped Δ ⊕ ¬G (Scoped Δ)) "for every term and every scope,
   a scoping derivation or a refutation". -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.ScopeCheck where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.List using ([]; _∷_)
open import Cubical.Data.Nat.Order using (_<_)
open import Cubical.Data.Unit
open import Cubical.Relation.Nullary.Base using (Discrete)

open import TheoryGrammar.Fibered
open import TheoryGrammar.Decidable
open import TheoryGrammar.View
open import TheoryGrammar.Instances.Lambda.Signature
open import TheoryGrammar.Instances.Lambda.Base
open import TheoryGrammar.Instances.Lambda.Grading
open import TheoryGrammar.Instances.Lambda.Readable
open import TheoryGrammar.Instances.Lambda.Binder
open import TheoryGrammar.Instances.Lambda.Scoped

module ScopeCheck (Name : Type₀) (_≟_ : Discrete Name) where

  open LamBase Name
  open Grading Name
  open Readable Name
  open Binder Name
  open Wellscoped Name
  open Views λFib

  -- The ONE place `Discrete Name` is used -- and it is used to BUILD an
  -- internal map, never to case-split on one.
  private module R = DecRep (λFib .carrier)

  dec-⌈⌉ : (m : Name) → ⊤G ⊢ Dec⟨ ⌈_⌉ {s = nm} m ⟩
  dec-⌈⌉ = R.dec-⌈⌉ {s = nm} _≟_

  -- Membership is decidable by induction on the scope, using nothing but
  -- `⊥`'s rule and the generic `dec-⊕`.
  dec-In : (Γ : Scope) → Probe (In Γ)
  dec-In []      = dec-⊥
  dec-In (m ∷ Γ) = probe-⊕ ⌈ m ⌉ (In Γ) (dec-⌈⌉ m) (dec-In Γ)

  -- `DecScoped t` DENOTES: "for EVERY scope, a scoping derivation of
  -- `t` or a refutation".  Quantifying over all scopes is what makes it
  -- an invariant of a recursion in which the scope grows.
  DecScoped : TmG
  DecScoped = &ᴰ Scope (λ Δ → Dec⟨ Scoped Δ ⟩)

  check : ⊤G ⊢ DecScoped
  check t _ = recSize {M = DecScoped} step t
    where
    step : (t : Raw)
         → ((s : Raw) → size s < size t → DecScoped s) → DecScoped t
    step t rec Δ =
      dec-map (Step Scoped Δ) (Scoped Δ) (sc-roll Δ) (sc-unroll Δ) t dStep
      where
      Vr Ap Lm : TmG
      Vr = VarG (In Δ)
      Ap = AppG (Scoped Δ) (Scoped Δ)
      Lm = ⊕ᴰ Name (λ n → LamG ⌈ n ⌉ (Scoped (n ∷ Δ)))

      -- the recursive call, with `&ᴰ` eliminated at the scope we need
      rec' : (s : Raw) → size s < size t → (Δ' : Scope) → Dec⟨ Scoped Δ' ⟩ s
      rec' s p Δ' = &ᴰ-E Scope {B = λ Δ'' → Dec⟨ Scoped Δ'' ⟩} Δ' s (rec s p)

      dVar : Dec⟨ Vr ⟩ t
      dVar = dec-⊗ varOp (λ _ → In Δ) t λ sp a →
               dec-In Δ (LParts varOp t sp a) tt

      dApp : Dec⟨ Ap ⟩ t
      dApp = dec-⊗ appOp (λ b → if b then Scoped Δ else Scoped Δ) t λ sp →
               λ { true  → rec' _ (proper appOp t sp true)  Δ
                 ; false → rec' _ (proper appOp t sp false) Δ }

      dLam : Dec⟨ Lm ⟩ t
      dLam = dec-map (LamGᵈ (λ n → Scoped (n ∷ Δ))) Lm
                     lam-collapse⁻ lam-collapse t
               (dec-lamᵈ (λ n → Scoped (n ∷ Δ)) t λ sp →
                  rec' _ (proper lamOp t sp false) (LParts lamOp t sp true ∷ Δ))

      dStep : Dec⟨ Step Scoped Δ ⟩ t
      dStep = dec-⊕ Vr (Ap ⊕ Lm) t (dVar , dec-⊕ Ap Lm t (dApp , dLam))

  closed? : ⊤G ⊢ Dec⟨ Scoped [] ⟩
  closed? = &ᴰ-E Scope [] ∘g check
