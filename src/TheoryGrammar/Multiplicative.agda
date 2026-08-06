{-
  Residuals for the lifted n-ary operations, and their adjointness.

  Two tiers, because they cost different hypotheses.

  TIER 1 (no hypotheses at all, arbitrary arity including infinite):
  the CURRYING isomorphism

      (⊗[ o ] A  ⊢  B)   ≅   MultiHom o A B

  where MultiHom is the n-ary hom -- literally the hom-set of the
  multicategory the theory presents.  So ⊗[ o ] is exactly the
  internalisation of the multi-ary hom, which is the Melliès–Zeilberger
  reading.  Both directions are transport-free: matching `Eq.refl` on the
  convolution's equation applies the solution rule because the index is a
  variable.

  TIER 2 (needs `Discrete (arities o)`): the genuine RESIDUALS, one per
  (operation, slot), with

      (⊗[ o ] A  ⊢  B)   ≅   (A i  ⊢  ⊸[ o , i ] A B).

  At a binary operation this recovers ⊸ and ⟜ of LambekD, one for each
  of the two slots.  Note the asymmetry in cost: the ELIMINATION
  direction (⊗ ⊢ B from a residual map, i.e. `⊸-app`) is free, and only
  the INTRODUCTION direction needs to decide which slot it is looking at.
-}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Multiplicative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥*) renaming (rec to ⊥*rec)
open import Cubical.Relation.Nullary.Base using (Discrete; yes; no; ¬_)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base

private variable ℓS ℓ ℓ' ℓX ℓA ℓB : Level

module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (M : Model σ ℓX) where

  open Notation M

  -- ================================================================
  -- TIER 1.  The n-ary hom, and currying.
  -- ================================================================

  MultiHom : (o : σ .ops)
           → ((a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
           → TheoryTy ℓB (σ .resultSort o)
           → Type (ℓ-max ℓX (ℓ-max ℓ' (ℓ-max ℓA ℓB)))
  MultiHom o A B =
    (m⃗ : (a : σ .arities o) → M .carrier (σ .sortOf o a))
    → ((a : σ .arities o) → A a (m⃗ a))
    → B (M .op o m⃗)

  module _ (o : σ .ops)
           {A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a)}
           {B : TheoryTy ℓB (σ .resultSort o)} where

    curry⊗ : (⊗[ o ] A ⊢ B) → MultiHom o A B
    curry⊗ f m⃗ h = f (M .op o m⃗) (m⃗ , Eq.refl , h)

    -- transport-free: `Eq.refl` unifies the index variable away
    uncurry⊗ : MultiHom o A B → (⊗[ o ] A ⊢ B)
    uncurry⊗ g .(M .op o m⃗) (m⃗ , Eq.refl , h) = g m⃗ h

    -- THEOREM (Tier 1).  ⊗[ o ] internalises the n-ary hom.
    ⊗-currying : Iso (⊗[ o ] A ⊢ B) (MultiHom o A B)
    ⊗-currying .Iso.fun = curry⊗
    ⊗-currying .Iso.inv = uncurry⊗
    ⊗-currying .Iso.sec g = refl
    ⊗-currying .Iso.ret f = funExt λ m → funExt λ { (m⃗ , Eq.refl , h) → refl }

  -- ================================================================
  -- TIER 2.  Slot residuals.
  -- ================================================================

  module _ (o : σ .ops) (i : σ .arities o) where

    -- The residual at slot i: given the OTHER arguments, and evidence
    -- that slot i holds the element we are indexed by, produce a B.
    ⊸[_] : ((a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
         → TheoryTy ℓB (σ .resultSort o)
         → TheoryTy (ℓ-max ℓX (ℓ-max ℓ' (ℓ-max ℓA ℓB))) (σ .sortOf o i)
    ⊸[ A ] B x =
      (m⃗ : (a : σ .arities o) → M .carrier (σ .sortOf o a))
      → (m⃗ i Eq.≡ x)
      → ((a : σ .arities o) → ¬ (a ≡ i) → A a (m⃗ a))
      → B (M .op o m⃗)

    module _ {A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a)}
             {B : TheoryTy ℓB (σ .resultSort o)} where

      -- ELIMINATION is free -- no Discrete, no transport.  This is the
      -- generic `⟜-app` / `⊸-app`.
      ⊸-app : (A i ⊢ ⊸[ A ] B) → (⊗[ o ] A ⊢ B)
      ⊸-app g .(M .op o m⃗) (m⃗ , Eq.refl , h) =
        g (m⃗ i) (h i) m⃗ Eq.refl (λ a _ → h a)

      -- INTRODUCTION needs to decide, for each slot, whether it is slot i.
      module _ (dec : Discrete (σ .arities o)) where

        private
          plugSlot : (m⃗ : (a : σ .arities o) → M .carrier (σ .sortOf o a))
               → A i (m⃗ i)
               → ((a : σ .arities o) → ¬ (a ≡ i) → A a (m⃗ a))
               → (a : σ .arities o) → A a (m⃗ a)
          plugSlot m⃗ ai ctx a with dec a i
          ... | yes p = subst (λ b → A b (m⃗ b)) (sym p) ai
          ... | no ¬p = ctx a ¬p

        ⊸-lam : (⊗[ o ] A ⊢ B) → (A i ⊢ ⊸[ A ] B)
        ⊸-lam f x ai m⃗ e ctx =
          f (M .op o m⃗) (m⃗ , Eq.refl , plugSlot m⃗ (Eq.transport (A i) (Eq.sym e) ai) ctx)
