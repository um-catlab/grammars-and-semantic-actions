{-# OPTIONS --lossy-unification #-}
{- A LISTED TYPE -- the enumeration TOGETHER WITH its completeness. -}
module TheoryGrammar.Enumerable.Listed where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.List
open import Cubical.Data.Unit

open import TheoryGrammar.Enumerable

private variable ℓ ℓA ℓB ℓC : Level

record Listed (A : Type ℓ) : Type ℓ where
  field
    elts     : List A
    complete : (a : A) → a ∈L elts

open Listed public

-- the two searches, in the form the recursions below want them
module _ {A : Type ℓ} (L : Listed A) {B : A → Type ℓB} where

  -- a Σ over a listed type is decided, and the NO branch is a genuine
  -- refutation because the list is complete
  searchΣ : ((a : A) → B a ⊎ No (B a))
          → (Σ[ a ∈ A ] B a) ⊎ No (Σ[ a ∈ A ] B a)
  searchΣ = decΣ (L .elts) (L .complete)

  -- ... and a Π, returning the OFFENDING element.  A caller turning
  -- "this component fails" into "the whole fails" needs to know WHICH,
  -- and `No ((a : A) → B a)` has forgotten it.
  searchΠ : ((a : A) → B a ⊎ No (B a))
          → ((a : A) → B a) ⊎ (Σ[ a ∈ A ] No (B a))
  searchΠ = findΠ (L .elts) (L .complete)

-- NAMED ELIMINATORS FOR A DECISION, at the `⊎` level.

-- transport a decision along a logical equivalence
mapD : {A : Type ℓ} {B : Type ℓB} → (A → B) → (B → A) → A ⊎ No A → B ⊎ No B
mapD f g (inl a) = inl (f a)
mapD f g (inr k) = inr λ b → k (g b)

-- "this component fails" ⟹ "the product fails".  The `Σ` is what
-- `findΠ` hands back, and keeping the offending index is exactly why it
-- does: `No ((a : A) → B a)` alone could not build this.
missΠ : {A : Type ℓ} {B : A → Type ℓB}
      → Σ[ a ∈ A ] No (B a) → No ((a : A) → B a)
missΠ (a , k) f = k (f a)

-- the general shape a search result is consumed in: a success continues,
-- a failure refutes
elimD : {P : Type ℓ} {E : Type ℓB} {R : Type ℓC}
      → (P → R ⊎ No R) → (E → No R) → P ⊎ E → R ⊎ No R
elimD f g (inl p) = f p
elimD f g (inr e) = inr (g e)
