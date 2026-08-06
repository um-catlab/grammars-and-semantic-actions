{-
  The passes compute.

  Each `refl` needs the scope checker, the generic `μ`/`fold`, and the
  pass's own `⊕-E` branches all to reduce.  The pipeline is stated
  internally throughout: a pass is observed by `term`, a decision by
  `⊕-E` into a constant grammar -- never by matching a `Dec`.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Passes.Tests where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit
open import Cubical.Data.List using ([])
open import Cubical.Data.Nat using (ℕ; discreteℕ)
open import Cubical.Data.FinData.Base renaming (zero to fzero; suc to fsuc)

open import TheoryGrammar.CarrierMap
open import TheoryGrammar.Instances.Lambda
open import TheoryGrammar.Instances.Lambda.Passes.Framework
open import TheoryGrammar.Instances.Lambda.Passes.Decide
open import TheoryGrammar.Instances.Lambda.Passes.Eta
open import TheoryGrammar.Instances.Lambda.Passes.Dead
open import TheoryGrammar.Instances.Lambda.Passes.Rename

open Lambda ℕ discreteℕ
open PassKit ℕ
open Decide  ℕ discreteℕ
open Eta     ℕ discreteℕ
open Dead    ℕ discreteℕ
open Rename  ℕ

-- ==================================================================
-- Observing a pass, internally.
-- ==================================================================

RawG : TmG
RawG _ = Raw

some : (t : Raw) → Raw → (RawG ⊕ ⊤G) t
some = ⊕-I₁ {A = RawG} {B = ⊤G}

none : (t : Raw) → (RawG ⊕ ⊤G) t
none t = ⊕-I₂ {B = ⊤G} {A = RawG} t tt

runClosed : ((Γ : Scope) → Scoped Γ ⊢ Out Γ) → ⊤G ⊢ (RawG ⊕ ⊤G)
runClosed p = ⊕-E (⊕-I₁ ∘g (term [] ∘g p [])) (⊕-I₂ ∘g ⊤-I) ∘g closed?

runId runEta runDead : ⊤G ⊢ (RawG ⊕ ⊤G)
runId   = runClosed idPass
runEta  = runClosed etaPass
runDead = runClosed deadPass

-- ==================================================================
-- The identity pass really is the identity.
-- ==================================================================

bigger : Raw
bigger = app (lam 0 (var 0)) (lam 1 (lam 2 (var 1)))

_ : runId bigger tt ≡ some bigger bigger
_ = refl

_ : runId (lam 0 (var 1)) tt ≡ none (lam 0 (var 1))
_ = refl

-- ==================================================================
-- η-contraction.
-- ==================================================================

e1 e2 e3 : Raw
e1 = lam 0 (lam 1 (app (var 0) (var 1)))   -- contracts: 0 is free for it
e2 = lam 0 (lam 1 (app (var 0) (var 0)))   -- argument is not the binder
e3 = lam 0 (lam 1 (app (var 1) (var 1)))   -- function still uses the binder

_ : runEta e1 tt ≡ some e1 (lam 0 (var 0))
_ = refl

_ : runEta e2 tt ≡ some e2 e2
_ = refl

_ : runEta e3 tt ≡ some e3 e3
_ = refl

-- ==================================================================
-- Dead-binding elimination.
-- ==================================================================

d1 d2 d3 : Raw
d1 = lam 1 (app (lam 0 (var 1)) (lam 2 (var 2)))   -- binder 0 unused
d2 = lam 1 (app (lam 0 (var 0)) (lam 2 (var 2)))   -- binder 0 used
d3 = app (lam 0 (var 0)) (lam 1 (var 1))           -- binder 0 used

_ : runDead d1 tt ≡ some d1 (lam 1 (var 1))
_ = refl

_ : runDead d2 tt ≡ some d2 d2
_ = refl

_ : runDead d3 tt ≡ some d3 d3
_ = refl

-- ==================================================================
-- Free transport along a split-preserving carrier map: the generic
-- `mapμ` computes, and the transported derivation still elaborates.
-- ==================================================================

renDB : ⊤G ⊢ ((λ _ → DB 0) ⊕ ⊤G)
renDB =
  ⊕-E (⊕-I₁ ∘g (Along.pullTerm (renCM (λ n → n)) (toDB []) ∘g renId []))
      (⊕-I₂ ∘g ⊤-I)
  ∘g closed?

someDB : (t : Raw) → DB 0 → ((λ _ → DB 0) ⊕ ⊤G) t
someDB = ⊕-I₁ {A = λ _ → DB 0} {B = ⊤G}

_ : renDB (lam 0 (var 0)) tt ≡ someDB (lam 0 (var 0)) (dlam (dvar fzero))
_ = refl

_ : renDB bigger tt
      ≡ someDB bigger (dapp (dlam (dvar fzero))
                            (dlam (dlam (dvar (fsuc fzero)))))
_ = refl
