{-# OPTIONS --lossy-unification #-}
{- THE SEPARATING CONJUNCTION, generic in a monoid `Fibered`. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Theories.MonoidSep where

open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib
open import TheoryGrammar.Theories.Monoid

-- Levels pinned at ℓ-zero, as in `MonoidStar` and for the same reason:
-- that is what every monoid instance in this tree uses, and leaving
-- them open costs a `ℓ-max` in the type of `_∗_` for no gain.
module MonSep (Fib : Fibered monoidSig ℓ-zero ℓ-zero) where

  private module R = RulesF Fib
  open R using (_⊢_; ⊗ˢ; ⊗ˢ-map; idg; _∘g_)

  Gr : Type₁
  Gr = R.TheoryTy ℓ-zero tt

  -- The separating conjunction, and its unit.

  infixr 20 _∗_

  _∗_ : Gr → Gr → Gr
  A ∗ B = ⊗ˢ appop (boolΠ A B)

  -- the unit: `nilop` has empty arity, so there is no payload at all
  empS : Gr
  empS = ⊗ˢ nilop (λ ())

  -- FUNCTORIALITY, and the two frame rules as its special cases.

  ∗-map : {A A' B B' : Gr} → A ⊢ A' → B ⊢ B' → (A ∗ B) ⊢ (A' ∗ B')
  ∗-map {A} {A'} {B} {B'} f g =
    ⊗ˢ-map appop {A = boolΠ A B} {B = boolΠ A' B'}
      (boolΠ {M = λ a → boolΠ {M = λ _ → Gr} A  B  a
                      ⊢ boolΠ {M = λ _ → Gr} A' B' a} f g)

  frame : {A B : Gr} (C : Gr) → A ⊢ B → (A ∗ C) ⊢ (B ∗ C)
  frame {A} {B} C f = ∗-map {A} {B} {C} {C} f idg

  frameL : {A B : Gr} (C : Gr) → A ⊢ B → (C ∗ A) ⊢ (C ∗ B)
  frameL {A} {B} C f = ∗-map {C} {C} {A} {B} idg f

  -- ... AND THE FRAME RULE CARRIES NO INFORMATION ABOUT A `Fibered`.
