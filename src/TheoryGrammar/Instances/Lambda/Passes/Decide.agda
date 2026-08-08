{- The two internal decisions every rewriting pass needs. scoped? Γ DENOTES
   "is this term scoped in Γ?". -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Passes.Decide where

open import Cubical.Data.Unit
open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary.Base using (Discrete)

open import TheoryGrammar.Base
open import TheoryGrammar.Instances.Lambda.Base
open import TheoryGrammar.Instances.Lambda.Fibered
open import TheoryGrammar.Instances.Lambda.Readable
open import TheoryGrammar.Instances.Lambda.ScopeCheck
open import TheoryGrammar.Instances.Lambda.Scoped
open import TheoryGrammar.Instances.Lambda.Signature

module Decide (Name : Type₀) (_≟_ : Discrete Name) where

  open LamBase Name
  open Readable Name
  open Wellscoped Name
  open ScopeCheck Name _≟_

  -- "is this term scoped in Γ?"
  scoped? : (Γ : Scope) → ⊤G ⊢ Dec⟨ Scoped Γ ⟩
  scoped? Γ = &ᴰ-E Scope Γ ∘g check

  -- "is this term the variable n?"
  isVar? : (n : Name) → ⊤G ⊢ Dec⟨ VarG ⌈ n ⌉ ⟩
  isVar? n t _ =
    dec-⊗ varOp (λ _ → ⌈ n ⌉) t λ sp a → dec-⌈⌉ n (LParts varOp t sp a) tt
