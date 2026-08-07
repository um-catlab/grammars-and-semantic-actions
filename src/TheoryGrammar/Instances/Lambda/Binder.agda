{-
  Yoneda for the binder: the one connective the generic layer cannot
  supply, because the body's grammar depends on the name in the slot.

  Guessing the bound name with `⊕ᴰ Name` and pinning it with the
  representable `⌈ n ⌉` is the same as reading it off the splitting.
  That is `⌈⌉-UP`, and `lam-collapse` is the only `Eq.refl` match in the
  whole instance.

  Defines `LamGᵈ`, the iso `lam-collapse`/`lam-collapse⁻` against the
  guessed form, and its decision `dec-lamᵈ` (with `dec-lamᵈ-at` at a
  given splitting).
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Binder where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Instances.Lambda.Signature
open import TheoryGrammar.Instances.Lambda.Base
open import TheoryGrammar.Instances.Lambda.Readable

module Binder (Name : Type₀) where

  open LamBase Name
  open Readable Name

  -- the DEPENDENT lam tensor.  `LamGᵈ A t` DENOTES: "`t` is a lambda,
  -- and its body satisfies `A` AT THE NAME `t` binds" -- so the body's
  -- grammar sees the bound name.
  LamGᵈ : (Name → TmG) → TmG
  LamGᵈ A t =
    Σ[ sp ∈ IsLam t ] A (LParts lamOp t sp true) (LParts lamOp t sp false)

  lam-collapse : {A : Name → TmG} → ⊕ᴰ Name (λ n → LamG ⌈ n ⌉ (A n)) ⊢ LamGᵈ A
  lam-collapse _ (n , sp , h) with h true
  ... | Eq.refl = sp , h false

  lam-collapse⁻ : {A : Name → TmG} → LamGᵈ A ⊢ ⊕ᴰ Name (λ n → LamG ⌈ n ⌉ (A n))
  lam-collapse⁻ t (sp , a) =
    LParts lamOp t sp true , sp , λ { true → Eq.refl ; false → a }

  -- its decision, exactly parallel to the generic `dec-⊗`: both
  -- decisions -- of the body, and of there being a splitting at all --
  -- live at a FIXED index, so both go through `dec-elim`.

  -- `dec-lamᵈ-at` decides `LamGᵈ A` GIVEN a splitting: the positive
  -- branch pairs it with the body's witness, the negative one carries
  -- any other splitting back to this one along `Split-isProp`.  It is
  -- not `private`: it is the half of `dec-lamᵈ` that does the work, and
  -- a caller who already has the splitting should be able to say so.
  dec-lamᵈ-at : (A : Name → TmG) (t : Raw) (sp : IsLam t)
              → Dec⟨ A (LParts lamOp t sp true) ⟩ (LParts lamOp t sp false)
              → Dec⟨ LamGᵈ A ⟩ t
  dec-lamᵈ-at A t sp =
    dec-elim (A (LParts lamOp t sp true)) (LParts lamOp t sp false)
      (λ a → dec-yes (LamGᵈ A) t (sp , a))
      (λ k → dec-no (LamGᵈ A) t λ x →
         k (subst (λ s → A (LParts lamOp t s true) (LParts lamOp t s false))
                  (Split-isProp lamOp t (x .fst) sp) (x .snd)))

  -- ... and `dec-lamᵈ` decides whether there is a splitting at all,
  -- then defers.
  dec-lamᵈ : (A : Name → TmG) (t : Raw)
           → ((sp : IsLam t)
              → Dec⟨ A (LParts lamOp t sp true) ⟩ (LParts lamOp t sp false))
           → Dec⟨ LamGᵈ A ⟩ t
  dec-lamᵈ A t d =
    dec-elim (⊗ˢ lamOp (λ _ → ⊤G)) t
      (λ x → dec-lamᵈ-at A t (x .fst) (d (x .fst)))
      (λ k → dec-no (LamGᵈ A) t λ y → k (y .fst , λ _ → tt))
      (⊗-decSplit lamOp t tt)
