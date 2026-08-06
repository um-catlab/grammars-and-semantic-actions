{-
  PASS 2.  Dead-binding elimination:  (λn. b) a  ↦  b,  n unused in b.

  `idAlg` with the `app` alternative replaced.

  This is the pass that wants WEAKENING.  Discarding the argument `a`
  is, in the tensor, the projection `A ⊗ B ⊢ A` -- and that is not a
  term of this calculus, because `_⊢_` preserves the index while the
  projection changes it.  Here the discard is invisible only because
  `Out Γ` is constant in the index: the existential form is affine by
  construction, having already forgotten what the index was.

  `Passes.Affine` states the same step in the `pull` form, where the
  discard has to be paid for, and shows exactly what it costs.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Passes.Dead where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.List using ([]; _∷_)
open import Cubical.Relation.Nullary.Base using (Discrete)

open import TheoryGrammar.Base
open import TheoryGrammar.Instances.Lambda.Signature
open import TheoryGrammar.Instances.Lambda.Base
open import TheoryGrammar.Instances.Lambda.Scoped
open import TheoryGrammar.Instances.Lambda.Passes.Framework
open import TheoryGrammar.Instances.Lambda.Passes.Decide

module Dead (Name : Type₀) (_≟_ : Discrete Name) where

  open LamBase Name
  open Wellscoped Name
  open PassKit Name
  open Decide Name _≟_

  private

    keepDead : (Γ : Scope) (u v : Raw)
             → Scoped Γ u → Scoped Γ v → Out Γ u
    keepDead Γ u v du dv =
      emit Γ (app u v) (sc-app Γ (app u v) (app-mk du dv))

    -- the function part is `lam n b`; drop the binder if `b` already
    -- lives at Γ.  The argument `v` is discarded here.
    dropBinder : (Γ : Scope) (n : Name) (b u v : Raw)
               → Scoped (n ∷ Γ) b → Scoped Γ u → Scoped Γ v → Out Γ u
    dropBinder Γ n b u v db du dv =
      ⊕-E {A = Scoped Γ} {C = Out Γ} {B = ¬G (Scoped Γ)}
          (emit Γ)
          (λ _ _ → keepDead Γ u v du dv)
          b (scoped? Γ b tt)

  -- the rewritten alternative: unfold the function part one step
  deadApp : (Γ : Scope) (u v : Raw)
          → Scoped Γ u → Scoped Γ v → Out Γ u
  deadApp Γ u v du dv =
    ⊕-E {A = VarG (In Γ)} {C = Out Γ}
        {B = AppG (Scoped Γ) (Scoped Γ)
             ⊕ ⊕ᴰ Name (λ n → LamG ⌈ n ⌉ (Scoped (n ∷ Γ)))}
        (λ _ _ → keepDead Γ u v du dv)
        (⊕-E {A = AppG (Scoped Γ) (Scoped Γ)} {C = Out Γ}
             {B = ⊕ᴰ Name (λ n → LamG ⌈ n ⌉ (Scoped (n ∷ Γ)))}
             (λ _ _ → keepDead Γ u v du dv)
             (⊕ᴰ-E λ n → lam-elim λ _ b _ db → dropBinder Γ n b u v db du dv))
        u (sc-unroll Γ u du)

  deadAlg : PassAlg
  deadAlg Γ =
    ⊕-E (outVar Γ)
        (⊕-E (app-elim λ _ _ ou ov →
                deadApp Γ (ou .fst) (ov .fst) (ou .snd) (ov .snd))
             (outLamG Γ))

  deadPass : (Γ : Scope) → Scoped Γ ⊢ Out Γ
  deadPass = runPass deadAlg
