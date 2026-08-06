{-
  What this instance owes `TheoryGrammar.Decidable`: a `DecReadable`.

  Three promodel facts -- at most one splitting, decidably so, and
  slotwise decisions combine -- and the generic `dec-⊗` follows.  Nothing
  about decisions is defined here; it is all in `Decidable`.

  `λ-decSlots` eliminates a decision sitting at a SLOT and lands at the
  WHOLE; the index-preserving `⊕-E` cannot, so it goes through the
  framework's pointwise elimination `dec-elim`.  The instance never
  matches `inl`/`inr` itself.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Readable where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
import Cubical.Data.Bool.Properties as B
open import Cubical.Data.Unit
open import Cubical.Data.Nat using (ℕ; snotz; znots; injSuc)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty as E using () renaming (rec to ⊥rec)

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Decidable
open import TheoryGrammar.View
open import TheoryGrammar.Instances.Lambda.Signature
open import TheoryGrammar.Instances.Lambda.Base

module Readable (Name : Type₀) where

  open LamBase Name
  open Views λFib using (Cover; Complete; total; exclusive; completeCase; certifies; fromUnique; decBranch)

  -- PRIMITIVE.  At most one splitting: unique readability.
  Split-isProp : (o : LOp) (t : Raw) (p q : LSplit o t) → p ≡ q
  Split-isProp varOp _ (mkVar _)   (mkVar _)   = refl
  Split-isProp appOp _ (mkApp _ _) (mkApp _ _) = refl
  Split-isProp lamOp _ (mkLam _ _) (mkLam _ _) = refl

  -- `⊗-refute` -- refuting one slot at its own part refutes the whole
  -- tensor -- follows generically from uniqueness alone
  open Precise Split-isProp public

  -- PRIMITIVE.  And it is decidable whether there is one, internally.
  -- The operation a term is built by, as a function of the term.  The
  -- SPLIT CONSTRUCTOR pins the term, so each clause is `refl`.
  opOf : Raw → LOp
  opOf (var _)   = varOp
  opOf (app _ _) = appOp
  opOf (lam _ _) = lamOp

  opOf-split : (o : LOp) (t : Raw) → ⊗ˢ o (λ _ → ⊤G) t → o ≡ opOf t
  opOf-split varOp .(var _)   (mkVar _   , _) = refl
  opOf-split appOp .(app _ _) (mkApp _ _ , _) = refl
  opOf-split lamOp .(lam _ _) (mkLam _ _ , _) = refl

  opCase : Complete LOp (λ o → ⊗ˢ o (λ _ → ⊤G))
  opCase = fromUnique discrim
             (λ y z t py pz → opOf-split y t py ∙ sym (opOf-split z t pz))
    where
      discrim : Cover (⊕ᴰ LOp (λ o → ⊗ˢ o (λ _ → ⊤G)))
      discrim (var n)   _ = varOp , (mkVar n   , λ _ → tt)
      discrim (app u v) _ = appOp , (mkApp u v , λ _ → tt)
      discrim (lam n t) _ = lamOp , (mkLam n t , λ _ → tt)

  private
    opTag : LOp → ℕ
    opTag varOp = 0
    opTag appOp = 1
    opTag lamOp = 2

  -- The comparison `decBranch` asks for.  On the diagonal it is `idg` --
  -- no transport, which is what keeps the derived `⊗-decSplit`
  -- computing; off it, the operations are distinct.
  cmpLOp : (y z : LOp) → (⊗ˢ z (λ _ → ⊤G) ⊢ ⊗ˢ y (λ _ → ⊤G)) ⊎ (y ≡ z → E.⊥)
  cmpLOp varOp varOp = inl idg
  cmpLOp appOp appOp = inl idg
  cmpLOp lamOp lamOp = inl idg
  cmpLOp varOp appOp = inr λ p → znots (cong opTag p)
  cmpLOp varOp lamOp = inr λ p → znots (cong opTag p)
  cmpLOp appOp varOp = inr λ p → snotz (cong opTag p)
  cmpLOp appOp lamOp = inr λ p → znots (injSuc (cong opTag p))
  cmpLOp lamOp varOp = inr λ p → snotz (cong opTag p)
  cmpLOp lamOp appOp = inr λ p → snotz (injSuc (cong opTag p))

  -- DERIVED, not primitive.  `opCase` says the operations PARTITION the
  -- terms; `View.decBranch` decides each branch of a partition.  So the
  -- nine clauses this used to have -- one per (operation, shape) pair,
  -- six of them absurd, each building its own witness or refutation --
  -- were nine consequences of one fact, written out.
  --
  -- The dependency now runs the right way: the positive statement is
  -- primitive and the negative ones follow.  It still COMPUTES, which
  -- is why `decBranch` takes `cmpLOp` rather than `Discrete LOp` -- see
  -- the note there.
  ⊗-decSplit : (o : LOp) → ⊤G ⊢ Dec⟨ ⊗ˢ o (λ _ → ⊤G) ⟩
  ⊗-decSplit = decBranch cmpLOp opCase

  -- `Bool`'s own dependent eliminator, under the name it earns here:
  -- assemble a two-slot family from its two slots.  Not a decision.
  private
    mkSlots : {P : Bool → Type₀} → P true → P false → (b : Bool) → P b
    mkSlots = B.elim

  -- Slotwise decisions combine.  Matches on the OPERATION, never on a
  -- term and never on a sum: each alternative just names its slots and
  -- hands them to `Precise`'s `decSlots¹`/`decSlots²`.  This is where
  -- finiteness of the arity is used, and for an infinite arity the
  -- statement is false.
  λ-decSlots : (o : LOp) (A : (a : LAr o) → TheoryTy ℓ-zero (LSortOf o a))
               (t : Raw) (sp : LSplit o t)
             → ((a : LAr o) → Dec⟨ A a ⟩ (LParts o t sp a))
             → Dec⟨ ⊗ˢ o A ⟩ t
  λ-decSlots varOp A t sp h =
    decSlots¹ varOp A t sp tt (λ x _ → x) (h tt)
  λ-decSlots appOp A t sp h =
    decSlots² appOp A t sp true false mkSlots (h true) (h false)
  λ-decSlots lamOp A t sp h =
    decSlots² lamOp A t sp true false mkSlots (h true) (h false)

  λDR : DecReadable λFib ℓ-zero
  λDR .splitProp = Split-isProp
  λDR .decSplit  = ⊗-decSplit
  λDR .decSlots  = λ-decSlots

  open DecTensor λDR public using (dec-⊗)

  -- ================================================================
  -- THE OPERATIONS PARTITION THE TERMS.
  --
  -- `⊗-decSplit o` decides each operation separately, at the complement
  -- `¬G (⊗ˢ o ⊤)`.  That is already complete; what it does not say is
  -- that the three rejections are the SAME fact -- a term that is not an
  -- application is a variable or a lambda, positively.
  --
  -- `opCase` says exactly that: every raw term is an o-composite for
  -- EXACTLY ONE `o`.  Totality is the `discrim` match (this instance's
  -- one look at a term, and the same one `⊗-decSplit` already makes);
  -- exclusivity is by the emptiness of the other operations' splittings,
  -- which is unique readability in its positive form.
  -- ================================================================
