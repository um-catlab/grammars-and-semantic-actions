{-
  The connectives of the lambda theory: one tensor per operation, plus
  the whole generic combinator layer in one `open`.

  Downstream modules open THIS, not `RulesSub`/`Decidable` directly.
  `LamG` is the reason the theory is many-sorted: its two slots live in
  different grammar sorts, so `if_then_else_` cannot express it.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Unit

open import TheoryGrammar.Base
open import TheoryGrammar.Substrate
open import TheoryGrammar.RulesSub
open import TheoryGrammar.Decidable
open import TheoryGrammar.Instances.Lambda.Signature
open import TheoryGrammar.Instances.Lambda.Substrate

module LamBase (Name : Type₀) where

  open Terms Name public
  -- connectives, every additive intro/elim, and the generic internal
  -- theory of decisions
  open DecSub λSub public

  TmG : Type₁
  TmG = TheoryTy ℓ-zero tm          -- Raw  → Type

  NmG : Type₁
  NmG = TheoryTy ℓ-zero nm          -- Name → Type

  VarG : NmG → TmG
  VarG P = ⊗ˢ varOp (λ _ → P)

  AppG : TmG → TmG → TmG
  AppG A B = ⊗ˢ appOp (λ b → if b then A else B)

  LamG : NmG → TmG → TmG
  LamG P A = ⊗ˢ lamOp (λ { true → P ; false → A })

  -- PRIMITIVES: intro and elim of the three tensors.  Everything else
  -- in this instance is a composite of these.
  var-mk : {P : NmG} {n : Name} → P n → VarG P (var n)
  var-mk {n = n} p = mkVar n , λ _ → p

  app-mk : {A B : TmG} {u v : Raw} → A u → B v → AppG A B (app u v)
  app-mk {u = u} {v} a b = mkApp u v , λ { true → a ; false → b }

  lam-mk : {P : NmG} {A : TmG} {n : Name} {t : Raw}
         → P n → A t → LamG P A (lam n t)
  lam-mk {n = n} {t} p a = mkLam n t , λ { true → p ; false → a }

  var-elim : {P : NmG} {C : TmG} → (∀ n → P n → C (var n)) → VarG P ⊢ C
  var-elim f _ (mkVar n , h) = f n (h tt)

  app-elim : {A B C : TmG} → (∀ u v → A u → B v → C (app u v)) → AppG A B ⊢ C
  app-elim f _ (mkApp u v , h) = f u v (h true) (h false)

  lam-elim : {P : NmG} {A : TmG} {C : TmG}
           → (∀ n t → P n → A t → C (lam n t)) → LamG P A ⊢ C
  lam-elim f _ (mkLam n t , h) = f n t (h true) (h false)
