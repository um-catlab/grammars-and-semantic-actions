{- What this instance owes `TheoryGrammar.Decidable`: a `DecReadable`. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Readable where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Empty as E using ()
open import Cubical.Data.Nat using (ℕ; snotz; znots; injSuc)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Decidable
open import TheoryGrammar.View
open import TheoryGrammar.Instances.Lambda.Signature
open import TheoryGrammar.Instances.Lambda.Base

module Readable (Name : Type₀) where

  open LamBase Name
  open Views λFib
    using (Cover; Complete; total; exclusive; completeCase; certifies;
           fromUnique; decBranch)

  -- PRIMITIVE.  At most one splitting: unique readability.
  Split-isProp : (o : LOp) (t : Raw) (p q : LSplit o t) → p ≡ q
  Split-isProp varOp _ (mkVar _)   (mkVar _)   = refl
  Split-isProp appOp _ (mkApp _ _) (mkApp _ _) = refl
  Split-isProp lamOp _ (mkLam _ _) (mkLam _ _) = refl

  -- `⊗-refute` -- refuting one slot at its own part refutes the whole
  -- tensor -- follows generically from uniqueness alone.  The module is
  -- `UniqueSplit`: its hypothesis is unique readability, not precision.
  open UniqueSplit Split-isProp public

  -- PRIMITIVE. `opCover` DENOTES: "every raw term is an o-composite for
  -- SOME `o`" -- and it is this instance's one look at a term.
  opCover : Cover (⊕ᴰ LOp (λ o → ⊗ˢ o (λ _ → ⊤G)))
  opCover (var n)   _ = varOp , (mkVar n   , λ _ → tt)
  opCover (app u v) _ = appOp , (mkApp u v , λ _ → tt)
  opCover (lam n t) _ = lamOp , (mkLam n t , λ _ → tt)

  -- DERIVED. `opOf t` DENOTES: "the operation `t` is built by".
  opOf : Raw → LOp
  opOf t = opCover t tt .fst

  -- It takes the SPLITTING, not the existential `⊗ˢ o ⊤G t` that
  -- quantifies over splittings: a caller that has one should say so,
  -- and the one caller below does (`py .fst`).
  opOf-split : (o : LOp) (t : Raw) → LSplit o t → o ≡ opOf t
  opOf-split varOp .(var _)   (mkVar _)   = refl
  opOf-split appOp .(app _ _) (mkApp _ _) = refl
  opOf-split lamOp .(lam _ _) (mkLam _ _) = refl

  -- THE OPERATIONS PARTITION THE TERMS: every raw term is an o-composite
  -- for EXACTLY ONE `o`.
  opCase : Complete LOp (λ o → ⊗ˢ o (λ _ → ⊤G))
  opCase = fromUnique opCover
             (λ y z t py pz →
                opOf-split y t (py .fst) ∙ sym (opOf-split z t (pz .fst)))

  -- The operations are pairwise distinct, and one numeral apiece is the
  -- whole proof.
  opTag : LOp → ℕ
  opTag varOp = 0
  opTag appOp = 1
  opTag lamOp = 2

  -- `opTag-≢` DENOTES: "operations with different numbers are different
  -- operations" -- injectivity of `opTag`, contrapositively.
  opTag-≢ : {y z : LOp} → (opTag y ≡ opTag z → E.⊥) → y ≡ z → E.⊥
  opTag-≢ k p = k (cong opTag p)

  -- The comparison `decBranch` asks for.  On the diagonal it is `idg` --
  -- no transport, which is what keeps the derived `⊗-decSplit`
  -- computing; off it, `opTag-≢` separates the two operations.
  cmpLOp : (y z : LOp) → (⊗ˢ z (λ _ → ⊤G) ⊢ ⊗ˢ y (λ _ → ⊤G)) ⊎ (y ≡ z → E.⊥)
  cmpLOp varOp varOp = inl idg
  cmpLOp appOp appOp = inl idg
  cmpLOp lamOp lamOp = inl idg
  cmpLOp varOp appOp = inr (opTag-≢ znots)
  cmpLOp varOp lamOp = inr (opTag-≢ znots)
  cmpLOp appOp varOp = inr (opTag-≢ snotz)
  cmpLOp appOp lamOp = inr (opTag-≢ λ p → znots (injSuc p))
  cmpLOp lamOp varOp = inr (opTag-≢ snotz)
  cmpLOp lamOp appOp = inr (opTag-≢ λ p → snotz (injSuc p))

  -- DERIVED, not primitive. `opCase` says the operations PARTITION the
  -- terms; `View.decBranch` decides each branch of a partition.
  ⊗-decSplit : (o : LOp) → ⊤G ⊢ Dec⟨ ⊗ˢ o (λ _ → ⊤G) ⟩
  ⊗-decSplit = decBranch cmpLOp opCase

  -- Slotwise decisions combine. Matches on the OPERATION, never on a term
  -- and never on a sum: each alternative just names its slots and hands
  -- them to `UniqueSplit`'s `decSlots¹`/`decSlots²`.
  λ-decSlots : (o : LOp) (A : (a : LAr o) → TheoryTy ℓ-zero (LSortOf o a))
               (t : Raw) (sp : LSplit o t)
             → ((a : LAr o) → Dec⟨ A a ⟩ (LParts o t sp a))
             → Dec⟨ ⊗ˢ o A ⟩ t
  λ-decSlots varOp A t sp h =
    decSlots¹ varOp A t sp tt (λ x _ → x) (h tt)
  λ-decSlots appOp A t sp h =
    decSlots² appOp A t sp true false decSlotsBool (h true) (h false)
  λ-decSlots lamOp A t sp h =
    decSlots² lamOp A t sp true false decSlotsBool (h true) (h false)

  λDR : DecReadable λFib ℓ-zero
  λDR .splitProp = Split-isProp
  λDR .decSplit  = ⊗-decSplit
  λDR .decSlots  = λ-decSlots

  open DecTensor λDR public using (dec-⊗)
