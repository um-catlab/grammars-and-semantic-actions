{-
  PASS 3.  Inlining, i.e. substitution -- the predicted NEGATIVE result.

  Substitution is a carrier map, so the additive fragment transports
  definitionally (`pull-Dec`, `subScoped?` below): every additively
  stated property of terms is a property of substituted terms, free.

  Multiplicatively it splits into a positive and a negative half, and
  the split is EXACTLY by operation:

      appOp   preserved   `sub n u (app x y) = app (sub n u x) (sub n u y)`
      lamOp   preserved   `sub n u (lam m t) = lam m (sub n u t)`
      varOp   FAILS       `sub n u (var n) = u`, which need not be a var

  So the failure is localised at the one operation the pass rewrites,
  and it is a failure of BOTH directions: `¬subSplitPres` refutes
  preservation at `varOp`, `¬subReflects` refutes reflection (the
  discrete Conduché condition of `ChangeOfTheory`) at `appOp` -- if
  `t = var n` and `σ n = app a b` then `σ t` splits and `t` does not.

  The restricted positive case is in `Passes.Rename`: substituting a
  VARIABLE, with binders renamed too, is a renaming, and renamings are
  exactly the split-preserving maps.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Passes.Inline where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (true; false; if_then_else_)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as E using (⊥)
open import Cubical.Relation.Nullary.Base using (Discrete; yes; no)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.CarrierMap
open import TheoryGrammar.Instances.Lambda.Signature
open import TheoryGrammar.Instances.Lambda.Substrate
open import TheoryGrammar.Instances.Lambda.Base
open import TheoryGrammar.Instances.Lambda.Scoped
open import TheoryGrammar.Instances.Lambda.Passes.Decide

module Inline (Name : Type₀) (_≟_ : Discrete Name) where

  open LamBase Name
  open Wellscoped Name
  open Decide Name _≟_

  -- PRIMITIVE (carrier map): single substitution.
  sub : Name → Raw → Raw → Raw
  sub n u (var m) with m ≟ n
  ... | yes _ = u
  ... | no  _ = var m
  sub n u (app x y) = app (sub n u x) (sub n u y)
  sub n u (lam m t) = lam m (sub n u t)

  subCM : Name → Raw → CarrierMap λSub
  subCM n u .hom nm m = m
  subCM n u .hom tm   = sub n u

  -- the defining equation at the substituted variable
  subHit : (n : Name) (u : Raw) → sub n u (var n) ≡ u
  subHit n u with n ≟ n
  ... | yes _ = refl
  ... | no ¬p = E.rec (¬p refl)

  -- ================================================================
  -- POSITIVE, additively: no hypothesis at all.
  -- ================================================================

  module _ (n : Name) (u : Raw) where

    private module S = Along (subCM n u)

    -- decidability transports definitionally
    pull-Dec : (Γ : Scope) → S.pull Dec⟨ Scoped Γ ⟩ ≡ Dec⟨ S.pull (Scoped Γ) ⟩
    pull-Dec Γ = refl

    -- and with it the whole scope checker, by `pullTerm`
    subScoped? : (Γ : Scope) → ⊤G ⊢ S.pull Dec⟨ Scoped Γ ⟩
    subScoped? Γ = S.pullTerm (scoped? Γ)

  -- ================================================================
  -- POSITIVE, multiplicatively, AWAY FROM `varOp`.
  -- ================================================================

    subPres-app : SplitPresAt (subCM n u) appOp
    subPres-app .homSplit _ (mkApp x y) = mkApp (sub n u x) (sub n u y)
    subPres-app .homParts _ (mkApp x y) true  = Eq.refl
    subPres-app .homParts _ (mkApp x y) false = Eq.refl

    subPres-lam : SplitPresAt (subCM n u) lamOp
    subPres-lam .homSplit _ (mkLam m t) = mkLam m (sub n u t)
    subPres-lam .homParts _ (mkLam m t) true  = Eq.refl
    subPres-lam .homParts _ (mkLam m t) false = Eq.refl

    -- so the multiplicative fragment DOES transport at those two
    pushˢ-app : {Q : (c : LAr appOp) → TheoryTy ℓ-zero (LSortOf appOp c)}
              → ⊗ˢ appOp (λ c → S.pull (Q c)) ⊢ S.pull (⊗ˢ appOp Q)
    pushˢ-app {Q} = S.push⊗ appOp subPres-app {B = Q}

    pushˢ-lam : {Q : (c : LAr lamOp) → TheoryTy ℓ-zero (LSortOf lamOp c)}
              → ⊗ˢ lamOp (λ c → S.pull (Q c)) ⊢ S.pull (⊗ˢ lamOp Q)
    pushˢ-lam {Q} = S.push⊗ lamOp subPres-lam {B = Q}

    -- and, spelled with the instance's own connective
    pushApp : {A B : TmG} → AppG (S.pull A) (S.pull B) ⊢ S.pull (AppG A B)
    pushApp {A} {B} =
      pushˢ-app {Q = λ b → if b then A else B}
      ∘g ⊗ˢ-map appOp {A = λ b → if b then S.pull A else S.pull B}
                      {B = λ b → S.pull (if b then A else B)}
                      (λ { true → idg ; false → idg })

  -- ================================================================
  -- NEGATIVE, at `varOp` -- and it is the whole story.
  -- ================================================================

  module _ (n : Name) (a b : Raw) where

    private module S = Along (subCM n (app a b))

    private
      noVar : IsVar (app a b) → ⊥
      noVar ()

      noApp : IsApp (var n) → ⊥
      noApp ()

    -- preservation fails: `var n` is a `varOp`-composite, its image
    -- `app a b` is not.
    ¬subSplitPres : SplitPresAt (subCM n (app a b)) varOp → ⊥
    ¬subSplitPres P =
      noVar (subst IsVar (subHit n (app a b)) (P .homSplit (var n) (mkVar n)))

    -- reflection fails: the image `app a b` splits at `appOp`, the
    -- source `var n` does not.  This is exactly the failure predicted
    -- by `ChangeOfTheory.ReflectsSplit`.
    ¬subReflects : S.ReflectsSplitAt appOp → ⊥
    ¬subReflects R =
      noApp (R (var n) (subst IsApp (sym (subHit n (app a b))) (mkApp a b)) .fst)
