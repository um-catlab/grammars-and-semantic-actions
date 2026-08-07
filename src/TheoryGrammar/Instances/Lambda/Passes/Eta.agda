{-
  PASS 1.  η-contraction:  λn. f (var n)  ↦  f.

  `idAlg` with the `lam` alternative replaced (`etaLam`; `etaAlg`,
  `etaPass`).  One node is all this file justifies, at two decisions
  taken in `etaApp` and eliminated with `⊕-E` -- no `Dec`, no `with`:

    * `isVar?`  the argument IS the bound variable.  The SEMANTIC side,
      which the calculus tracks not at all: `Out Γ` accepts any output
      term, so `etaApp` DISCARDS this evidence.  That is the one place
      a pass here validates rather than parses, and `Framework`'s
      constancy is exactly why it must.

    * `scoped?` the function part survives at the smaller scope.  The
      SCOPING side, which `Out Γ` will not let through; it enters as
      `Framework.tryEmit`, which CARRIES what it produces.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Passes.Eta where

open import Cubical.Data.List using (_∷_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt)
open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary.Base using (Discrete)

open import TheoryGrammar.Base
open import TheoryGrammar.Instances.Lambda.Base
open import TheoryGrammar.Instances.Lambda.Passes.Decide
open import TheoryGrammar.Instances.Lambda.Passes.Framework
open import TheoryGrammar.Instances.Lambda.Scoped
open import TheoryGrammar.Instances.Lambda.Signature

module Eta (Name : Type₀) (_≟_ : Discrete Name) where

  open LamBase Name
  open Wellscoped Name
  open PassKit Name
  open Decide Name _≟_

  -- no contraction: put the binder back
  keepEta : (Γ : Scope) (n : Name) (f v : Raw)
          → Scoped (n ∷ Γ) f → Scoped (n ∷ Γ) v → Out Γ v
  keepEta Γ n f v df dv =
    outLam Γ n (app f v) (sc-app (n ∷ Γ) (app f v) (app-mk df dv))

  -- the argument IS the bound variable; now the scope side condition.
  -- `df` is a derivation at the LARGER scope and is therefore useless
  -- for the emit -- `Scoped Γ f` is strictly stronger -- so the decision
  -- is genuinely doing work, not re-checking something already known.
  tryStrengthen : (Γ : Scope) (n : Name) (f v : Raw)
                → Scoped (n ∷ Γ) f → Scoped (n ∷ Γ) v → Out Γ v
  tryStrengthen Γ n f v df dv =
    tryEmit Γ (scoped? Γ) f (keepEta Γ n f v df dv)

  -- the whole `lam`-of-`app` case.  Both branches ignore the `isVar?`
  -- payload: the calculus does not track "the argument was the binder".
  etaApp : (Γ : Scope) (n : Name) (f v : Raw)
         → Scoped (n ∷ Γ) f → Scoped (n ∷ Γ) v → Out Γ v
  etaApp Γ n f v df dv =
    ⊕-E {A = VarG ⌈ n ⌉} {C = Out Γ} {B = ¬G (VarG ⌈ n ⌉)}
        (λ _ _ → tryStrengthen Γ n f v df dv)
        (λ _ _ → keepEta Γ n f v df dv)
        v (isVar? n v tt)

  -- the rewritten alternative: unfold the body one step and branch
  etaLam : (Γ : Scope) (n : Name) → Scoped (n ∷ Γ) ⊢ Out Γ
  etaLam Γ n =
    ⊕-E (outLam Γ n ∘g sc-var (n ∷ Γ))
        (⊕-E (app-elim λ f v df dv → etaApp Γ n f v df dv)
             (outLam Γ n ∘g (sc-roll (n ∷ Γ) ∘g (⊕-I₂ ∘g ⊕-I₂))))
    ∘g sc-unroll (n ∷ Γ)

  etaAlg : PassAlg
  etaAlg Γ =
    ⊕-E (outVar Γ)
        (⊕-E (outApp Γ)
             (⊕ᴰ-E λ n → lam-elim λ _ _ _ o → etaLam Γ n (o .fst) (o .snd)))

  etaPass : (Γ : Scope) → Scoped Γ ⊢ Out Γ
  etaPass = runPass etaAlg
