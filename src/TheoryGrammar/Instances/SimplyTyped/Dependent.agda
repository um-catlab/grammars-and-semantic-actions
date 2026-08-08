{- THE TWO REPRESENTABLE-COLLAPSIBLE DEPENDENT TENSORS, and their
   decisions. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.SimplyTyped.Dependent where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Decidable
open import TheoryGrammar.Instances.SimplyTyped.Signature
open import TheoryGrammar.Instances.SimplyTyped.Fibered
open import TheoryGrammar.Instances.SimplyTyped.Base
open import TheoryGrammar.Instances.SimplyTyped.Readable

module StDependent (Name : Type₀) where

  open StBase Name
  open StReadable Name

  -- The binder.

  -- `LamGᵈ P` denotes "the term is a lambda, and its BODY satisfies `P` at
  -- the very name this lambda binds".
  LamGᵈ : (Name → TmG) → TmG
  LamGᵈ P = ⊗ˢᵈ lamOp λ ps → P (ps true) (ps false)

  -- ... and that is the same grammar as the ⊕ᴰ that guesses the name,
  -- because the `⌈ n ⌉` slot pins the guess.  Both ways round, and the
  -- `Eq.refl` matches are `⌈⌉-UP` -- the Yoneda lemma -- spelled out.
  lam-collapse : {P : Name → TmG} → ⊕ᴰ Name (λ n → LamG (Nm n) (P n)) ⊢ LamGᵈ P
  lam-collapse _ (n , sp , h) with h true
  ... | Eq.refl = sp , h false

  -- PRIMITIVE (phase 1): the `⊕ᴰ` tag is READ OFF the splitting, so it
  -- varies with the world; `⊕ᴰ-I` takes a tag fixed in advance and cannot
  -- express it.
  lam-collapse⁻ : {P : Name → TmG} → LamGᵈ P ⊢ ⊕ᴰ Name (λ n → LamG (Nm n) (P n))
  lam-collapse⁻ t (sp , a) =
    TParts lamOp t sp true , sp , λ { true → Eq.refl ; false → a }

  -- the decision AT a given splitting: any other splitting of the same
  -- term is that one, by unique readability, so a refutation of the
  -- body refutes the whole
  dec-lamᵈ-at : (P : Name → TmG) (t : Raw) (sp : IsLam t)
              → Dec⟨ P (TParts lamOp t sp true) ⟩ (TParts lamOp t sp false)
              → Dec⟨ LamGᵈ P ⟩ t
  dec-lamᵈ-at P t sp =
    dec-elim (P (TParts lamOp t sp true)) (TParts lamOp t sp false)
      (λ a → dec-yes (LamGᵈ P) t (sp , a))
      (λ k → dec-no (LamGᵈ P) t λ x →
         k (subst (λ s → P (TParts lamOp t s true) (TParts lamOp t s false))
                  (Split-isProp lamOp t (x .fst) sp) (x .snd)))

  -- ... and hence the decision, after `⊗-decSplit` supplies a splitting
  dec-lamᵈ : (P : Name → TmG) (t : Raw)
           → ((sp : IsLam t)
              → Dec⟨ P (TParts lamOp t sp true) ⟩ (TParts lamOp t sp false))
           → Dec⟨ LamGᵈ P ⟩ t
  dec-lamᵈ P t d =
    dec-elim (⊗ˢ lamOp (λ _ → ⊤G)) t
      (λ x → dec-lamᵈ-at P t (x .fst) (d (x .fst)))
      (λ k → dec-no (LamGᵈ P) t λ y → k (y .fst , λ _ → tt))
      (⊗-decSplit lamOp t tt)

  -- The annotation: the direction switch, and the one place a `ty`
  -- slot is read.

  -- `AnnGᵈ P` denotes "the term is an annotation, and its SUBJECT
  -- satisfies `P` at the very type written in the annotation".  Again
  -- the type is read off the splitting, not guessed.
  AnnGᵈ : (Ty → TmG) → TmG
  AnnGᵈ P t = Σ[ sp ∈ IsAnn t ]
                P (TParts annOp t sp false) (TParts annOp t sp true)

  ann-collapse : {P : Ty → TmG}
               → ⊕ᴰ Ty (λ A → AnnG (P A) (⌈_⌉ {s = ty} A)) ⊢ AnnGᵈ P
  ann-collapse _ (A , sp , h) with h false
  ... | Eq.refl = sp , h true

  -- PRIMITIVE (phase 1): as `lam-collapse⁻` above -- the `⊕ᴰ` tag is
  -- read off the splitting, so no `⊕ᴰ-I` applies.
  ann-collapse⁻ : {P : Ty → TmG}
                → AnnGᵈ P ⊢ ⊕ᴰ Ty (λ A → AnnG (P A) (⌈_⌉ {s = ty} A))
  ann-collapse⁻ t (sp , a) =
    TParts annOp t sp false , sp , λ { true → a ; false → Eq.refl }

  -- the decision at a given splitting, as for `lam`
  dec-annᵈ-at : (P : Ty → TmG) (t : Raw) (sp : IsAnn t)
              → Dec⟨ P (TParts annOp t sp false) ⟩ (TParts annOp t sp true)
              → Dec⟨ AnnGᵈ P ⟩ t
  dec-annᵈ-at P t sp =
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
      (λ x → dec-annᵈ-at P t (x .fst) (d (x .fst)))
      (λ k → dec-no (AnnGᵈ P) t λ y → k (y .fst , λ _ → tt))
      (⊗-decSplit annOp t tt)
