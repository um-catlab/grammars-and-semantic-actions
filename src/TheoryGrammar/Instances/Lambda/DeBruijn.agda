{-
  Elaboration to de Bruijn, as the generic `fold`.

  Motive `(Γ , t) ↦ DB (length Γ)`.  There is no `Maybe`:
  scope-correctness sits in the INDEX, so elaboration is total.  The
  algebra is `⟦Sc⟧` followed by the elimination rules, one per
  alternative; no clause looks at a term or at a shape.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.DeBruijn where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.List using ([]; _∷_; length)
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.FinData.Base using (Fin) renaming (zero to fzero; suc to fsuc)

open import TheoryGrammar.Base
open import TheoryGrammar.Instances.Lambda.Signature
open import TheoryGrammar.Instances.Lambda.Base
open import TheoryGrammar.Instances.Lambda.Scoped

module DeBruijn (Name : Type₀) where

  open LamBase Name
  open Wellscoped Name

  data DB : ℕ → Type₀ where
    dvar : ∀ {k} → Fin k → DB k
    dapp : ∀ {k} → DB k → DB k → DB k
    dlam : ∀ {k} → DB (suc k) → DB k

  -- a constant grammar is a constant: the unique map into `λ _ → X`
  constG : {s : LSort} {A : TheoryTy ℓ-zero s} {X : Type₀}
         → X → A ⊢ (λ _ → X)
  constG x _ _ = x

  -- Reading a de Bruijn index off a scope membership.  The hit branch
  -- DISCARDS the representable rather than eliminating it with `⌈⌉-E`:
  -- `⌈⌉-E` matches `Eq.refl`, and a witness built from `Discrete Name`
  -- via `pathToEq` does not reduce to `Eq.refl` in cubical.  The index
  -- is fixed by the POSITION in the scope, not by the proof, so nothing
  -- is lost -- and this is the difference between the tests computing
  -- and not.
  toIx : (Γ : Scope) → In Γ ⊢ (λ _ → Fin (length Γ))
  toIx []      = ⊥-E
  toIx (m ∷ Γ) = ⊕-E (constG fzero ∘g ⊤-I) ((λ _ → fsuc) ∘g toIx Γ)

  Mot : Ix → Type₀
  Mot (Γ , _) = DB (length Γ)

  dbStep : (Γ : Scope) → Step (λ Δ _ → DB (length Δ)) Γ ⊢ (λ _ → DB (length Γ))
  dbStep Γ = ⊕-E (var-elim λ n i → dvar (toIx Γ n i))
            (⊕-E (app-elim λ _ _ a b → dapp a b)
                 (⊕ᴰ-E λ _ → lam-elim λ _ _ _ d → dlam d))

  toDB : (Γ : Scope) → Scoped Γ ⊢ (λ _ → DB (length Γ))
  toDB Γ t d = fold Mot alg (Γ , t) d
    where
    alg : (Γ' : Scope) (t' : Raw) (sh : Sh (ScopedF Γ') t')
        → ((p : Pos (ScopedF Γ') t' sh) → Mot (nx (ScopedF Γ') t' sh p))
        → Mot (Γ' , t')
    alg Γ' t' sh rc = dbStep Γ' t' (⟦Sc⟧ {M = Mot} Γ' t' (sh , rc))
