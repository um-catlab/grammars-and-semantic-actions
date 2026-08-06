{-
  Decidability as a CONNECTIVE, additively.  Needs only a `Model` --
  nothing here mentions the operations.

  A decision for `A` with complement `A'` is a map `⊤ ⊢ A ⊕ A'` together
  with the exclusion `(A & A') ⊢ ⊥`, without which `⊕-I₂ ∘ ⊤-I` would
  "decide" everything at `A' = ⊤`.  `¬G A = A ⇒ ⊥` is proved to be the
  LARGEST complement (`largest`), so normalising to the default
  `Dec⟨ A ⟩ = A ⊕ ¬G A` loses nothing -- `toDec` does it.

  Every proof below is a composite of `Rules`' intro/elim, with ONE
  exception: `⊕-E-at`, the POINTWISE elimination of a sum, and the
  `dec-elim` it specialises to.  Those are elimination rules, so like
  `Rules.⊕-E` they are defined by matching `inl`/`inr` -- and that is
  the only place in the development a sum may be matched at all.  No
  `Dec`, no `yes`/`no` anywhere.
-}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Decidable.Additive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥*)

open import TheoryGrammar.Base
open import TheoryGrammar.Rules

private variable ℓS ℓ ℓ' ℓX ℓA ℓB ℓC ℓY ℓZ : Level


module DecAdd {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (M : Model σ ℓX) where

  open Notation M public
  open Rules M public

  private variable
    s : S
    A : TheoryTy ℓA s
    B : TheoryTy ℓB s
    C : TheoryTy ℓC s

  -- internal negation
  ¬G_ : TheoryTy ℓA s → TheoryTy ℓA s
  ¬G A = A ⇒ ⊥G

  infix 32 ¬G_

  -- the default complement: internal negation
  Dec⟨_⟩ : TheoryTy ℓA s → TheoryTy ℓA s
  Dec⟨ A ⟩ = A ⊕ ¬G A

  -- The introduction rules, with the grammar NAMED.  Naming it is not
  -- optional: `Dec⟨ A ⟩` unfolds to `A ⊕ ¬G A`, and a grammar-valued
  -- implicit cannot be recovered from `?A m ⊎ ?B m` once `m` is already
  -- in the metavariable's context.
  dec-yes : (A : TheoryTy ℓA s) → A ⊢ Dec⟨ A ⟩
  dec-yes A = ⊕-I₁ {A = A} {B = ¬G A}

  dec-no : (A : TheoryTy ℓA s) → ¬G A ⊢ Dec⟨ A ⟩
  dec-no A = ⊕-I₂ {B = ¬G A} {A = A}

  -- ================================================================
  -- The additive lemmas the decision combinators are built from.
  -- ================================================================

  &-swap : (A & B) ⊢ (B & A)
  &-swap = &-I &-E₂ &-E₁

  -- ex falso: a grammar and its negation are jointly empty
  contra : (A & ¬G A) ⊢ ⊥G
  contra {A = A} = ⇒-app ∘⊢ &-swap

  -- `&` distributes over `⊕`.  `⊕-E` under a `⇒`, then uncurry: proved
  -- from intro/elim alone, with no case split on the sum.
  dist& : ((A ⊕ B) & C) ⊢ ((A & C) ⊕ (B & C))
  dist& = Iso.inv ⇒-UP (⊕-E (⇒-I ⊕-I₁) (⇒-I ⊕-I₂))

  -- contravariance of negation
  ¬G-map : B ⊢ A → ¬G A ⊢ ¬G B
  ¬G-map g = ⇒-I (contra ∘⊢ &-I (g ∘⊢ &-E₂) &-E₁)

  -- de Morgan, the constructive direction: what refuting a sum needs
  deMorgan : (A : TheoryTy ℓA s) (B : TheoryTy ℓB s)
           → (¬G A & ¬G B) ⊢ ¬G (A ⊕ B)
  deMorgan A B =
    ⇒-I (⊕-E (contra ∘⊢ &-I &-E₁ (&-E₁ ∘⊢ &-E₂))
             (contra ∘⊢ &-I &-E₁ (&-E₂ ∘⊢ &-E₂))
         ∘⊢ (dist& ∘⊢ &-swap))

  -- ================================================================
  -- COMPLEMENTS.  A decision is only informative if its two halves
  -- exclude each other -- without that, `⊕-I₂ ∘⊢ ⊤-I` "decides" every
  -- A at A' = ⊤G and says nothing at all.  So a decision carries the
  -- exclusion, and `¬G A` is characterised as the LARGEST complement:
  -- every other one factors through it, which is why nothing is lost by
  -- normalising to `Dec⟨ A ⟩`.
  -- ================================================================

  Complement : TheoryTy ℓA s → TheoryTy ℓB s → Type (ℓ-max ℓX (ℓ-max ℓA ℓB))
  Complement A A' = (A & A') ⊢ ⊥G

  record Decision (A : TheoryTy ℓA s) (A' : TheoryTy ℓB s)
    : Type (ℓ-max ℓX (ℓ-max ℓA ℓB)) where
    field
      decide  : ⊤G ⊢ (A ⊕ A')
      exclude : Complement A A'

  open Decision public

  -- `¬G A` is a complement ...
  ¬G-excludes : (A : TheoryTy ℓA s) → Complement A (¬G A)
  ¬G-excludes A = contra {A = A}

  -- ... and the largest one: any complement embeds into it
  largest : {A : TheoryTy ℓA s} {A' : TheoryTy ℓB s}
          → Complement A A' → A' ⊢ ¬G A
  largest d = ⇒-I (d ∘⊢ &-swap)

  -- so every decision, at whatever complement, yields the default one
  toDec : {A : TheoryTy ℓA s} {A' : TheoryTy ℓB s}
        → Decision A A' → ⊤G ⊢ Dec⟨ A ⟩
  toDec {A = A} D = ⊕-E (dec-yes A) (dec-no A ∘⊢ largest (D .exclude)) ∘⊢ D .decide

  -- and the default one is a decision
  decDefault : (A : TheoryTy ℓA s) → ⊤G ⊢ Dec⟨ A ⟩ → Decision A (¬G A)
  decDefault A f .decide  = f
  decDefault A f .exclude = ¬G-excludes A

  -- ================================================================
  -- Closure properties of decidability.
  -- ================================================================

  -- along an internal logical equivalence
  dec-map : (A : TheoryTy ℓA s) (B : TheoryTy ℓB s)
          → A ⊢ B → B ⊢ A → Dec⟨ A ⟩ ⊢ Dec⟨ B ⟩
  dec-map A B f g = ⊕-E (dec-yes B ∘⊢ f) (dec-no B ∘⊢ ¬G-map g)

  -- under `⊕`: two distributions and a de Morgan
  dec-⊕ : (A : TheoryTy ℓA s) (B : TheoryTy ℓB s)
        → (Dec⟨ A ⟩ & Dec⟨ B ⟩) ⊢ Dec⟨ A ⊕ B ⟩
  dec-⊕ A B =
    ⊕-E (dec-yes (A ⊕ B) ∘⊢ (⊕-I₁ ∘⊢ &-E₁))
        (⊕-E (dec-yes (A ⊕ B) ∘⊢ (⊕-I₂ ∘⊢ &-E₁))
             (dec-no (A ⊕ B) ∘⊢ (deMorgan A B ∘⊢ &-swap))
         ∘⊢ (dist& ∘⊢ &-swap))
    ∘⊢ dist&

  -- under `&`
  dec-& : (A : TheoryTy ℓA s) (B : TheoryTy ℓB s)
        → (Dec⟨ A ⟩ & Dec⟨ B ⟩) ⊢ Dec⟨ A & B ⟩
  dec-& A B =
    ⊕-E (⊕-E (dec-yes (A & B) ∘⊢ &-swap)
             (dec-no (A & B) ∘⊢ (¬G-map &-E₂ ∘⊢ &-E₁))
         ∘⊢ (dist& ∘⊢ &-swap))
        (dec-no (A & B) ∘⊢ (¬G-map &-E₁ ∘⊢ &-E₁))
    ∘⊢ dist&

  -- the units decide themselves
  dec-⊤ : ⊤G {s} ⊢ Dec⟨ ⊤G {s} ⟩
  dec-⊤ = dec-yes ⊤G

  dec-⊥ : ⊤G {s} ⊢ Dec⟨ ⊥G {s} ⟩
  dec-⊥ = dec-no ⊥G ∘⊢ ⇒-I &-E₂
