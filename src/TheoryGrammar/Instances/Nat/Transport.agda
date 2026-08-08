{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- THE CATALAN RECURRENCE, TRANSPORTED TO STRINGS. This file is the
   composition the other two advertise and neither could perform alone:
   Species.agda proves D ≅ 1 ⊕ (x ⊗ D ⊗ x ⊗ D) over (ℕ, +) Length.agda
   proves `length` reflects splittings here pull D ≅ pull 1 ⊕ (pull x ⊗ … )
   over strings and the... -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Nat.Transport (Char : Type₀) where

open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)

-- the strings side, `pull`, and the transport machinery
open import TheoryGrammar.Instances.Nat.Length Char public

-- the ℕ side, qualified: `Species` exports `Gr`, `_⊗'_`, `ε'` under the
-- same names as the string instance
import TheoryGrammar.Instances.Nat.Species as Sp

-- The transported grammar, and the two halves of the recurrence.

-- "the length of this string admits a Dyck bracketing"
DyckLen : Gr
DyckLen = pull Sp.D

-- The right-hand side of the recurrence, at strings.  Note this is
-- written with the STRING `_⊗'_` and `_⊕_`: it is a statement about
-- string grammars, with no ℕ left in it except inside `pull`.
DyckLenBody : Gr
DyckLenBody =
  pull Sp.ε' ⊕ (pull Sp.x ⊗' pull Sp.D ⊗' pull Sp.x ⊗' pull Sp.D)

-- The multiplicative half, one factor at a time.

private
  inner : pull (Sp.x Sp.⊗' Sp.D) ⊢ (pull Sp.x ⊗' pull Sp.D)
  inner = pull⊗ˢ' Sp.x Sp.D

  middle : pull (Sp.D Sp.⊗' Sp.x Sp.⊗' Sp.D)
         ⊢ (pull Sp.D ⊗' pull Sp.x ⊗' pull Sp.D)
  middle =
    ⊗ˢ-map appop
      {A = λ b → if b then pull Sp.D else pull (Sp.x Sp.⊗' Sp.D)}
      {B = λ b → if b then pull Sp.D else (pull Sp.x ⊗' pull Sp.D)}
      (λ { true → idg ; false → inner })
    ∘g pull⊗ˢ' Sp.D (Sp.x Sp.⊗' Sp.D)

  outer : pull (Sp.x Sp.⊗' Sp.D Sp.⊗' Sp.x Sp.⊗' Sp.D)
        ⊢ (pull Sp.x ⊗' pull Sp.D ⊗' pull Sp.x ⊗' pull Sp.D)
  outer =
    ⊗ˢ-map appop
      {A = λ b → if b then pull Sp.x else pull (Sp.D Sp.⊗' Sp.x Sp.⊗' Sp.D)}
      {B = λ b → if b then pull Sp.x else (pull Sp.D ⊗' pull Sp.x ⊗' pull Sp.D)}
      (λ { true → idg ; false → middle })
    ∘g pull⊗ˢ' Sp.x (Sp.D Sp.⊗' Sp.x Sp.⊗' Sp.D)

-- THE THEOREM. `pullTerm` carries the ℕ-level derivation across for free
-- -- that is the additive half, and `pull (A ⊕ B)` really is `pull A ⊕
-- pull B` on the nose (`ChangeOfTheory.pull-⊕` is `refl`), so the `⊕`
-- needs no transport at all.

dyckLen-unroll : DyckLen ⊢ DyckLenBody
dyckLen-unroll = ⊕-E ⊕-I₁ (⊕-I₂ ∘g outer) ∘g pullTerm Sp.dyck-unroll

-- ... AND BACK.

private
  inner⁻ : (pull Sp.x ⊗' pull Sp.D) ⊢ pull (Sp.x Sp.⊗' Sp.D)
  inner⁻ = pull⊗ˢ'⁻ Sp.x Sp.D

  middle⁻ : (pull Sp.D ⊗' pull Sp.x ⊗' pull Sp.D)
          ⊢ pull (Sp.D Sp.⊗' Sp.x Sp.⊗' Sp.D)
  middle⁻ =
    pull⊗ˢ'⁻ Sp.D (Sp.x Sp.⊗' Sp.D)
    ∘g ⊗ˢ-map appop
         {A = λ b → if b then pull Sp.D else (pull Sp.x ⊗' pull Sp.D)}
         {B = λ b → if b then pull Sp.D else pull (Sp.x Sp.⊗' Sp.D)}
         (λ { true → idg ; false → inner⁻ })

  outer⁻ : (pull Sp.x ⊗' pull Sp.D ⊗' pull Sp.x ⊗' pull Sp.D)
         ⊢ pull (Sp.x Sp.⊗' Sp.D Sp.⊗' Sp.x Sp.⊗' Sp.D)
  outer⁻ =
    pull⊗ˢ'⁻ Sp.x (Sp.D Sp.⊗' Sp.x Sp.⊗' Sp.D)
    ∘g ⊗ˢ-map appop
         {A = λ b → if b then pull Sp.x else (pull Sp.D ⊗' pull Sp.x ⊗' pull Sp.D)}
         {B = λ b → if b then pull Sp.x else pull (Sp.D Sp.⊗' Sp.x Sp.⊗' Sp.D)}
         (λ { true → idg ; false → middle⁻ })

dyckLen-roll : DyckLenBody ⊢ DyckLen
dyckLen-roll = pullTerm Sp.dyck-roll ∘g ⊕-E ⊕-I₁ (⊕-I₂ ∘g outer⁻)
