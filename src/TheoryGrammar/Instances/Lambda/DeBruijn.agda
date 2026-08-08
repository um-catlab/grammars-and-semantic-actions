{- Elaboration to de Bruijn (`DB`), as the generic `fold`. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.DeBruijn where

open import Cubical.Foundations.Prelude
open import Cubical.Data.FinData.Base using (Fin) renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.List using ([]; _∷_; length)
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Sigma

open import TheoryGrammar.Instances.Lambda.Signature
open import TheoryGrammar.Instances.Lambda.Base
open import TheoryGrammar.Instances.Lambda.Scoped

module DeBruijn (Name : Type₀) where

  open LamBase Name
  open Wellscoped Name

  -- `DB k` DENOTES: a lambda term with `k` free indices -- the target
  -- of elaboration, and the only nameless representation here.
  data DB : ℕ → Type₀ where
    dvar : ∀ {k} → Fin k → DB k
    dapp : ∀ {k} → DB k → DB k → DB k
    dlam : ∀ {k} → DB (suc k) → DB k

  -- `toIxA Γ` DENOTES: "a proof that `n` occurs in `Γ` YIELDS the position
  -- at which it occurs".
  toIxA : (Γ : Scope) → Action (In Γ) (Fin (length Γ))
  toIxA []      = ⊥A
  toIxA (m ∷ Γ) = caseA (pureA (Fin (length (m ∷ Γ))) fzero)
                        (mapA fsuc (toIxA Γ))

  -- the fold's motive: at nonterminal `(Γ , t)`, a de Bruijn term with
  -- as many indices as `Γ` has names
  Mot : Ix → Type₀
  Mot i = Δ (DB (length (i .fst))) (i .snd)

  -- One action per alternative. Every branch is a composite of the generic
  -- `Δ`-combinators (`Δ-map`, `Δ-pair`, `Δ-at`) with this instance's own
  -- tensor eliminators; no constant grammar, no `Maybe`, and nothing built
  -- by hand.
  module _ (Γ : Scope) where
    private k = length Γ

    dbStepA : Step (λ Δ' x → Mot (Δ' , x)) Γ ⊢ Δ (DB k)
    dbStepA =
      ⊕-E (var-elim λ n i → Δ-map dvar (var n) (toIxA Γ n i))
     (⊕-E (app-elim λ u v a b →
             Δ-map (λ p → dapp (p .fst) (p .snd)) (app u v)
                   (Δ-pair (app u v) (Δ-at u (app u v) a , Δ-at v (app u v) b)))
          (⊕ᴰ-E λ _ → lam-elim λ n t _ d →
                        Δ-map dlam (lam n t) (Δ-at t (lam n t) d)))

  toDB : (Γ : Scope) → Action (Scoped Γ) (DB (length Γ))
  toDB Γ t d = fold Mot alg (Γ , t) d
    where
    alg : (Γ' : Scope) (t' : Raw) (sh : Sh (ScopedF Γ') t')
        → ((p : Pos (ScopedF Γ') t' sh) → Mot (nx (ScopedF Γ') t' sh p))
        → Mot (Γ' , t')
    alg Γ' t' sh rc = dbStepA Γ' t' (⟦Sc⟧ {M = Mot} Γ' t' (sh , rc))
