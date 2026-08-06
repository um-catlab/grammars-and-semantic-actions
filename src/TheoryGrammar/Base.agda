{-
  LambekD, generic in the input theory.

  A priori distinct from Grammar/: this copies the shape rather than
  importing it.  The differences:

    Grammar/                       TheoryGrammar/
    --------                       --------------
    Grammar ℓ = String → Type ℓ    TheoryTy ℓ s = carrier s → Type ℓ
    one binary ⊗ (concatenation)   one ⊗[o] per OPERATION of the theory
    two residuals ⊸ ⟜             one residual per (operation, slot)
    ε, literal                     representables at each element
    additives                      IDENTICAL -- they never saw the monoid

  Parameterised by a many-sorted signature and a MODEL of it.  The model,
  not the signature, is what the types are indexed by; equations of the
  theory hold in the model and therefore lift to isomorphisms between the
  composite connectives (TheoryGrammar.Equations).

  `SortedSig` mirrors `Cubical.Algebra.Theory.Sorted` in
  cubical-categorical-logic field-for-field, so the two can be identified
  once that development is visible from this library.
-}
module TheoryGrammar.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥*)
import Cubical.Data.Equality as Eq

private variable ℓS ℓ ℓ' ℓX ℓA ℓB ℓC ℓY : Level

-- ==================================================================
-- Signatures and models.
-- ==================================================================

record SortedSig (S : Type ℓS) ℓ ℓ' : Type (ℓ-max ℓS (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))) where
  field
    ops        : Type ℓ
    arities    : ops → Type ℓ'
    sortOf     : (o : ops) → arities o → S
    resultSort : ops → S

open SortedSig public

record Model {S : Type ℓS} (σ : SortedSig S ℓ ℓ') ℓX
  : Type (ℓ-max ℓS (ℓ-max ℓ (ℓ-max ℓ' (ℓ-suc ℓX)))) where
  field
    carrier : S → Type ℓX
    op      : (o : σ .ops)
            → ((a : σ .arities o) → carrier (σ .sortOf o a))
            → carrier (σ .resultSort o)

open Model public

-- ==================================================================
-- Types of the calculus: families indexed by the model's carrier.
-- ==================================================================

-- ==================================================================
-- THE ADDITIVE LAYER NEEDS ONLY A CARRIER.
--
-- `TheoryTy`, `_⊢_`, every additive, and the representables mention the
-- carrier and NOTHING else -- no operation, no splittings.  Stating that
-- as its own module is not tidiness: it is what lets a PARTIAL algebra
-- use the calculus.  A promodel with no total operation still has a
-- carrier, so it still has the whole additive fragment; only `⊗[ o ]`
-- below needs `op`, and `⊗ˢ` (over a `Fibered`) needs merely `Split`.
--
-- `Notation` is then this module plus the two op-dependent definitions,
-- so every existing `Notation M` user is unaffected.
-- ==================================================================

module CarrierNotation {S : Type ℓS} (X : S → Type ℓX) where

  TheoryTy : (ℓA : Level) → S → Type (ℓ-max ℓX (ℓ-suc ℓA))
  TheoryTy ℓA s = X s → Type ℓA

  -- morphisms: carrier-preserving, exactly as A ⊢ B for grammars
  _⊢_ : ∀ {s} → TheoryTy ℓA s → TheoryTy ℓB s → Type (ℓ-max ℓX (ℓ-max ℓA ℓB))
  A ⊢ B = ∀ m → A m → B m

  infix 1 _⊢_

  id⊢ : ∀ {s} {A : TheoryTy ℓA s} → A ⊢ A
  id⊢ _ x = x

  _∘⊢_ : ∀ {s} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} {C : TheoryTy ℓC s}
       → B ⊢ C → A ⊢ B → A ⊢ C
  (g ∘⊢ f) m x = g m (f m x)

  -- ================================================================
  -- ADDITIVES.  Identical to Grammar/: they never mentioned the monoid,
  -- so they port verbatim, only re-indexed.
  -- ================================================================

  ⊤G : ∀ {s} → TheoryTy ℓ-zero s
  ⊤G _ = Unit

  ⊥G : ∀ {s} → TheoryTy ℓ-zero s
  ⊥G _ = ⊥*

  _&_ : ∀ {s} → TheoryTy ℓA s → TheoryTy ℓB s → TheoryTy (ℓ-max ℓA ℓB) s
  (A & B) m = A m × B m

  _⊕_ : ∀ {s} → TheoryTy ℓA s → TheoryTy ℓB s → TheoryTy (ℓ-max ℓA ℓB) s
  (A ⊕ B) m = A m ⊎ B m

  _⇒_ : ∀ {s} → TheoryTy ℓA s → TheoryTy ℓB s → TheoryTy (ℓ-max ℓA ℓB) s
  (A ⇒ B) m = A m → B m

  ⊕ᴰ : ∀ {s} (Y : Type ℓY) → (Y → TheoryTy ℓA s) → TheoryTy (ℓ-max ℓY ℓA) s
  ⊕ᴰ Y A m = Σ[ y ∈ Y ] A y m

  &ᴰ : ∀ {s} (Y : Type ℓY) → (Y → TheoryTy ℓA s) → TheoryTy (ℓ-max ℓY ℓA) s
  &ᴰ Y A m = (y : Y) → A y m

  -- representables: the analogue of `literal` and `ε` at once.  Every
  -- element of the carrier gives one; the constants of the signature
  -- give the distinguished ones.
  ⌈_⌉ : ∀ {s} → X s → TheoryTy ℓX s
  ⌈ a ⌉ m = m Eq.≡ a

-- ==================================================================
-- MULTIPLICATIVES.  One per operation, by convolution along it.  THIS
-- is the fragment that needs a total operation -- and the reason
-- `Fibered`/`⊗ˢ` exists is to get the same connective from `Split`
-- alone, which a partial algebra can supply.
-- ==================================================================

module Notation {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (M : Model σ ℓX) where

  open CarrierNotation (M .carrier) public

  ⊗[_] : (o : σ .ops)
       → ((a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
       → TheoryTy (ℓ-max ℓX (ℓ-max ℓ' ℓA)) (σ .resultSort o)
  ⊗[ o ] A m =
    Σ[ m⃗ ∈ ((a : σ .arities o) → M .carrier (σ .sortOf o a)) ]
      ((M .op o m⃗ Eq.≡ m) × ((a : σ .arities o) → A a (m⃗ a)))

  -- functorial action
  ⊗map : (o : σ .ops)
       {A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a)}
       {B : (a : σ .arities o) → TheoryTy ℓB (σ .sortOf o a)}
       → (∀ a → A a ⊢ B a)
       → ⊗[ o ] A ⊢ ⊗[ o ] B
  ⊗map o f m (m⃗ , e , g) = m⃗ , e , λ a → f a (m⃗ a) (g a)
