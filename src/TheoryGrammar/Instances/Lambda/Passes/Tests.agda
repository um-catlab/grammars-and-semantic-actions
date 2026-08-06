{-
  The passes compute.

  Each `refl` needs the scope checker, the generic `μ`/`fold`, and the
  pass's own `⊕-E` branches all to reduce.  Every name below is a TERM
  (`⊤G ⊢ Δ Bool`, `⊤G ⊢ Result _ (Δ Raw)`); `run` / `runΔ` appear only in
  the `refl` lines -- externalising is the observation, not part of the
  pipeline.  This file defines no reader and no constant grammar.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Passes.Tests where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.List using ([]; _∷_)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.List using ([])
open import Cubical.Data.Nat using (ℕ; discreteℕ)
open import Cubical.Data.FinData.Base renaming (zero to fzero; suc to fsuc)

open import TheoryGrammar.SemanticAction using (passes; _↦_; _at_)
open import TheoryGrammar.CarrierMap
open import TheoryGrammar.Instances.Lambda
open import TheoryGrammar.Instances.Lambda.Passes.Framework
open import TheoryGrammar.Instances.Lambda.Passes.Decide
open import TheoryGrammar.Instances.Lambda.Passes.Eta
open import TheoryGrammar.Instances.Lambda.Passes.Dead
open import TheoryGrammar.Instances.Lambda.Passes.Rename
open import TheoryGrammar.Instances.Lambda.Passes.Inline

open Lambda ℕ discreteℕ
open PassKit ℕ
open Decide  ℕ discreteℕ
open Eta     ℕ discreteℕ
open Dead    ℕ discreteℕ
open Rename  ℕ

-- ==================================================================
-- Observing a pass.  `runClosed` is the GENERIC `runResult`: `closed?`
-- is a decision (a `Result (¬G _) _`) and a pass composed with `term`
-- is an `Action (Scoped Γ) Raw`.  The `RawG` / `some` / `none` triple
-- this replaces was `Result ⊤G` and `Maybe` written out by hand.
-- ==================================================================

DecCl : TmG
DecCl = ¬G (Scoped [])

runClosed : ((Γ : Scope) → Scoped Γ ⊢ Out Γ) → ⊤G ⊢ Result DecCl (Δ Raw)
runClosed p = mapR DecCl (Δ Raw) (term [] ∘g p []) ∘g closed?

runId runEta runDead : ⊤G ⊢ Result DecCl (Δ Raw)
runId   = runClosed idPass
runEta  = runClosed etaPass
runDead = runClosed deadPass

-- ==================================================================
-- The passes compute.  Cases are batched: one `refl` per suite.
-- ==================================================================

bigger : Raw
bigger = app (lam 0 (var 0)) (lam 1 (lam 2 (var 1)))

-- the identity pass really is the identity, and rejects the unscoped
_ : passes (runΔ Raw DecCl runId at
             (bigger ↦ just bigger ∷ (lam 0 (var 1)) ↦ nothing ∷ []))
_ = refl

-- η-contraction: `e1` contracts (0 is free for it), the others do not
e1 e2 e3 : Raw
e1 = lam 0 (lam 1 (app (var 0) (var 1)))   -- contracts
e2 = lam 0 (lam 1 (app (var 0) (var 0)))   -- argument is not the binder
e3 = lam 0 (lam 1 (app (var 1) (var 1)))   -- function still uses the binder

_ : passes (runΔ Raw DecCl runEta at
             ( e1 ↦ just (lam 0 (var 0))
             ∷ e2 ↦ just e2
             ∷ e3 ↦ just e3
             ∷ [] ))
_ = refl

-- dead-binding elimination: only `d1`'s binder 0 is unused
d1 d2 d3 : Raw
d1 = lam 1 (app (lam 0 (var 1)) (lam 2 (var 2)))   -- binder 0 unused
d2 = lam 1 (app (lam 0 (var 0)) (lam 2 (var 2)))   -- binder 0 used
d3 = app (lam 0 (var 0)) (lam 1 (var 1))           -- binder 0 used

_ : passes (runΔ Raw DecCl runDead at
             ( d1 ↦ just (lam 1 (var 1))
             ∷ d2 ↦ just d2
             ∷ d3 ↦ just d3
             ∷ [] ))
_ = refl

-- ==================================================================
-- Free transport along a split-preserving carrier map: the generic
-- `mapμ` computes, and the transported derivation still elaborates.
-- ==================================================================

renDB : ⊤G ⊢ Result DecCl (Δ (DB 0))
renDB = mapR DecCl (Δ (DB 0))
             (Along.pullTerm (renCM (λ n → n)) (toDB []) ∘g renId [])
        ∘g closed?

_ : passes (runΔ (DB 0) DecCl renDB at
             ( (lam 0 (var 0)) ↦ just (dlam (dvar fzero))
             ∷ bigger          ↦ just (dapp (dlam (dvar fzero))
                                            (dlam (dlam (dvar (fsuc fzero)))))
             ∷ [] ))
_ = refl

-- ==================================================================
-- `subScoped?` : the scope checker TRANSPORTED along substitution, by
-- `CarrierMap.Along.pullTerm`.  It is still a map out of `⊤`, only at a
-- reindexed world -- so the generic `accepts?` reads it unchanged, and
-- what the test says is that transporting a decision commutes with
-- deciding the transported thing.
-- ==================================================================

module Inl = Inline ℕ discreteℕ

subScoped! : (n : ℕ) (u : Raw) (Γ : Scope) → ⊤G ⊢ Δ Bool
subScoped! n u Γ =
  okA (S.pull (Scoped Γ)) (S.pull (¬G (Scoped Γ)))
  ∘g Inl.subScoped? n u Γ
  where module S = Along (Inl.subCM n u)

-- `t[y := x]`: `var 0` is not scoped in `[]`, but substituting a scoped
-- term for it makes it so -- and substitution rescues nothing else.
_ : passes (run (subScoped! 0 (var 1) []) at ((var 0) ↦ false ∷ []))
_ = refl

_ : passes (run (subScoped! 0 (var 1) (1 ∷ [])) at
             ( (var 0)          ↦ true
             ∷ (var 2)          ↦ false
             ∷ (lam 2 (var 0))  ↦ true
             ∷ [] ))
_ = refl

-- ==================================================================
-- The pass rejections, as theorems: an unscoped term has NO closing
-- derivation, so the pass is not merely undefined on it.
-- ==================================================================

noClosed : (t : Raw) → run (okA (Scoped []) DecCl ∘g closed?) t ≡ false
         → (¬G (Scoped [])) t
noClosed = refute (Scoped []) DecCl closed?

no-closed-open : (¬G (Scoped [])) (lam 0 (var 1))
no-closed-open = noClosed (lam 0 (var 1)) refl

-- substitution, negatively: no substitution instance of `var 2` is
-- scoped in `1 ∷ []`, which is a fact about the TRANSPORTED decision
module SP = Along (Inl.subCM 0 (var 1))

no-sub : (SP.pull (¬G (Scoped (1 ∷ [])))) (var 2)
no-sub = refute (SP.pull (Scoped (1 ∷ []))) (SP.pull (¬G (Scoped (1 ∷ []))))
                (Inl.subScoped? 0 (var 1) (1 ∷ [])) (var 2) refl
