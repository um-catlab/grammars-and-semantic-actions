{-
  THE THREE DEPENDENT TENSORS, and their decisions.

  Each is a place where a slot's content determines another slot's (or
  the whole's) GRAMMAR, so the ⊕ᴰ that guesses it has to be collapsed
  against a representable before it can be decided:

    LamGᵈ   the bound NAME determines the body's context   (`⌈ n ⌉`)
    AnnGᵈ   the annotation TYPE determines what is checked (`⌈ A ⌉`)
    AppGᵈ   the function's synthesised type determines the argument's
            checking type -- and here there is no representable to
            collapse against, only `Split-isProp`, which is why the
            application case is the one that needs `synUnique`

  `lam-collapse` and `ann-collapse` are the only `Eq.refl` matches in
  the instance; both are `⌈⌉-UP`, the Yoneda lemma, spelled out.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.SimplyTyped.Dependent where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Relation.Nullary.Base using (Discrete)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Decidable
open import TheoryGrammar.Instances.SimplyTyped.Signature
open import TheoryGrammar.Instances.SimplyTyped.Fibered
open import TheoryGrammar.Instances.SimplyTyped.Base
open import TheoryGrammar.Instances.SimplyTyped.Readable
open import TheoryGrammar.Instances.SimplyTyped.Types

module StDependent (Name : Type₀) where

  open StBase Name
  open StReadable Name
  open StTypes Name

  -- ================================================================
  -- The binder.
  -- ================================================================

  LamGᵈ : (Name → TmG) → TmG
  LamGᵈ P t = Σ[ sp ∈ IsLam t ]
                P (TParts lamOp t sp true) (TParts lamOp t sp false)

  lam-collapse : {P : Name → TmG} → ⊕ᴰ Name (λ n → LamG (Nm n) (P n)) ⊢ LamGᵈ P
  lam-collapse _ (n , sp , h) with h true
  ... | Eq.refl = sp , h false

  lam-collapse⁻ : {P : Name → TmG} → LamGᵈ P ⊢ ⊕ᴰ Name (λ n → LamG (Nm n) (P n))
  lam-collapse⁻ t (sp , a) =
    TParts lamOp t sp true , sp , λ { true → Eq.refl ; false → a }

  private
    decLam : (P : Name → TmG) (t : Raw) (sp : IsLam t)
           → Dec⟨ P (TParts lamOp t sp true) ⟩ (TParts lamOp t sp false)
           → Dec⟨ LamGᵈ P ⟩ t
    decLam P t sp =
      dec-elim (P (TParts lamOp t sp true)) (TParts lamOp t sp false)
        (λ a → dec-yes (LamGᵈ P) t (sp , a))
        (λ k → dec-no (LamGᵈ P) t λ x →
           k (subst (λ s → P (TParts lamOp t s true) (TParts lamOp t s false))
                    (Split-isProp lamOp t (x .fst) sp) (x .snd)))

  dec-lamᵈ : (P : Name → TmG) (t : Raw)
           → ((sp : IsLam t)
              → Dec⟨ P (TParts lamOp t sp true) ⟩ (TParts lamOp t sp false))
           → Dec⟨ LamGᵈ P ⟩ t
  dec-lamᵈ P t d =
    dec-elim (⊗ˢ lamOp (λ _ → ⊤G)) t
      (λ x → decLam P t (x .fst) (d (x .fst)))
      (λ k → dec-no (LamGᵈ P) t λ y → k (y .fst , λ _ → tt))
      (⊗-decSplit lamOp t tt)

  -- ================================================================
  -- The annotation: the direction switch, and the one place a `ty`
  -- slot is read.
  -- ================================================================

  AnnGᵈ : (Ty → TmG) → TmG
  AnnGᵈ P t = Σ[ sp ∈ IsAnn t ]
                P (TParts annOp t sp false) (TParts annOp t sp true)

  ann-collapse : {P : Ty → TmG}
               → ⊕ᴰ Ty (λ A → AnnG (P A) (⌈_⌉ {s = ty} A)) ⊢ AnnGᵈ P
  ann-collapse _ (A , sp , h) with h false
  ... | Eq.refl = sp , h true

  ann-collapse⁻ : {P : Ty → TmG}
                → AnnGᵈ P ⊢ ⊕ᴰ Ty (λ A → AnnG (P A) (⌈_⌉ {s = ty} A))
  ann-collapse⁻ t (sp , a) =
    TParts annOp t sp false , sp , λ { true → a ; false → Eq.refl }

  private
    decAnn : (P : Ty → TmG) (t : Raw) (sp : IsAnn t)
           → Dec⟨ P (TParts annOp t sp false) ⟩ (TParts annOp t sp true)
           → Dec⟨ AnnGᵈ P ⟩ t
    decAnn P t sp =
      dec-elim (P (TParts annOp t sp false)) (TParts annOp t sp true)
        (λ a → dec-yes (AnnGᵈ P) t (sp , a))
        (λ k → dec-no (AnnGᵈ P) t λ x →
           k (subst (λ s → P (TParts annOp t s false) (TParts annOp t s true))
                    (Split-isProp annOp t (x .fst) sp) (x .snd)))

  dec-annᵈ : (P : Ty → TmG) (t : Raw)
           → ((sp : IsAnn t)
              → Dec⟨ P (TParts annOp t sp false) ⟩ (TParts annOp t sp true))
           → Dec⟨ AnnGᵈ P ⟩ t
  dec-annᵈ P t d =
    dec-elim (⊗ˢ annOp (λ _ → ⊤G)) t
      (λ x → decAnn P t (x .fst) (d (x .fst)))
      (λ k → dec-no (AnnGᵈ P) t λ y → k (y .fst , λ _ → tt))
      (⊗-decSplit annOp t tt)
