{-
  PASS 1.  η-contraction:  λn. f (var n)  ↦  f.

  `idAlg` with the `lam` alternative replaced.  Everything else -- the
  recursion, and the `var` and `app` alternatives -- is inherited, so
  the only thing this file has to justify is one node.

  What that node costs, exactly:

    * `isVar?`  to see that the argument is the bound variable.  This
      is the SEMANTIC side of the pass, and the calculus tracks none
      of it: `Out Γ` would accept any output term.

    * `scoped?` to see that the function part survives at the smaller
      scope.  This is the SCOPING side, and it is what a strengthening
      lemma would otherwise have to prove.  The calculus refuses to let
      the contraction through without it -- `Out Γ` demands a `Scoped Γ`
      derivation and the recursive result only gives `Scoped (n ∷ Γ)`.

  Both are eliminated with `⊕-E`; no `Dec`, no `yes`/`no`, no `with`.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Passes.Eta where

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

module Eta (Name : Type₀) (_≟_ : Discrete Name) where

  open LamBase Name
  open Wellscoped Name
  open PassKit Name
  open Decide Name _≟_

  private

    -- no contraction: put the binder back
    keepEta : (Γ : Scope) (n : Name) (f v : Raw)
            → Scoped (n ∷ Γ) f → Scoped (n ∷ Γ) v → Out Γ v
    keepEta Γ n f v df dv =
      outLam Γ n (app f v) (sc-app (n ∷ Γ) (app f v) (app-mk df dv))

    -- the argument IS the bound variable; now the scope side condition
    tryStrengthen : (Γ : Scope) (n : Name) (f v : Raw)
                  → Scoped (n ∷ Γ) f → Scoped (n ∷ Γ) v → Out Γ v
    tryStrengthen Γ n f v df dv =
      ⊕-E {A = Scoped Γ} {C = Out Γ} {B = ¬G (Scoped Γ)}
          (emit Γ)
          (λ _ _ → keepEta Γ n f v df dv)
          f (scoped? Γ f tt)

    -- the whole `lam`-of-`app` case
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
