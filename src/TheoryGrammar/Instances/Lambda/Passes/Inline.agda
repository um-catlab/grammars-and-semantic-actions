{-
  PASS 3.  Inlining, i.e. substitution -- a NEGATIVE result, localised
  to a single operation.  `sub n u t` DENOTES "t with u put for n".

  ADDITIVELY it is a carrier map, so the whole fragment transports
  definitionally: `pull-Dec` is `refl`, `subScoped?` the scope checker
  itself transported by `pullTerm`.  MULTIPLICATIVELY the split is
  exactly by operation --

      appOp  preserved  (`subPres-app`, `pushˢ-app`, `pushApp`)
      lamOp  preserved  (`subPres-lam`, `pushˢ-lam`)
      varOp  FAILS      sub n u (var n) = u, which need not be a var
  -- and at `varOp` it fails BOTH ways: `¬subSplitPres` refutes
  preservation, `¬subReflects` reflection (`ChangeOfTheory`'s discrete
  Conduché condition) at `appOp`.  The surviving positive case is
  `Passes.Rename`: substituting a VARIABLE is a renaming.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Passes.Inline where

open import Cubical.Data.Bool using (true; false; if_then_else_)
open import Cubical.Data.Empty as E using (⊥)
open import Cubical.Data.Sigma
open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary.Base using (Discrete; yes; decRec)
open import Cubical.Relation.Nullary.Properties using (isPropDec; Discrete→isSet)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.CarrierMap
open import TheoryGrammar.Instances.Lambda.Base
open import TheoryGrammar.Instances.Lambda.Fibered
open import TheoryGrammar.Instances.Lambda.Passes.Decide
open import TheoryGrammar.Instances.Lambda.Scoped
open import TheoryGrammar.Instances.Lambda.Signature

module Inline (Name : Type₀) (_≟_ : Discrete Name) where

  open LamBase Name
  open Wellscoped Name
  open Decide Name _≟_

  -- PRIMITIVE (carrier map): single substitution, `t` with `u` put for
  -- `n`.  The metalanguage `Dec` is consumed by its OWN elimination
  -- rule, `decRec`, exactly as an internal `Dec⟨_⟩` is consumed by
  -- `dec-elim`: no `with`, no `yes`/`no` pattern.
  sub : Name → Raw → Raw → Raw
  sub n u (var m)   = decRec (λ _ → u) (λ _ → var m) (m ≟ n)
  sub n u (app x y) = app (sub n u x) (sub n u y)
  sub n u (lam m t) = lam m (sub n u t)

  -- ... as a map of carriers: identity on names, `sub n u` on terms
  subCM : Name → Raw → CarrierMap λFib
  subCM n u .hom nm m = m
  subCM n u .hom tm   = sub n u

  -- the defining equation at the substituted variable.  `n ≟ n` IS
  -- `yes refl`, because a `Dec` of a proposition is itself one -- so
  -- this too is a `cong`, not a match.
  subHit : (n : Name) (u : Raw) → sub n u (var n) ≡ u
  subHit n u =
    cong (decRec (λ _ → u) (λ _ → var n))
         (isPropDec (Discrete→isSet _≟_ n n) (n ≟ n) (yes refl))

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
  --
  -- `homSplit` forces the image of a splitting; `homParts` forces its
  -- slots to be the images of the source's.  Both are `Eq.refl` here,
  -- which is what "substitution commutes with the node" means.
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
