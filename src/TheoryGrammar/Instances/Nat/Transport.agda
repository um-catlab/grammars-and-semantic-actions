{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE CATALAN RECURRENCE, TRANSPORTED TO STRINGS.

  This file is the composition the other two advertise and neither could
  perform alone:

      Species.agda   proves  D ≅ 1 ⊕ (x ⊗ D ⊗ x ⊗ D)      over (ℕ, +)
      Length.agda    proves  `length` reflects splittings
      -------------------------------------------------------------
      here           pull D ≅ pull 1 ⊕ (pull x ⊗ … )       over strings

  and the point is that the second line is the ONLY input needed.  The
  Dyck recurrence is proved once, at ℕ, with no mention of strings; the
  string-level isomorphism is then a composite of `pullTerm` (free, the
  additive half) and `pull⊗ˢ'` (the Conduché half).  Over abelianisation
  the same composite does not typecheck, because `pull⊗⁻` does not exist
  -- which is exactly the content of `ChangeOfTheory`'s header.

  WHY IT COULD NOT BE WRITTEN UNTIL NOW.  Two obstructions, both removed:

    (1) `Strings/Base` and `Nat/Base` each declared their own `MonOp`, so
        `ModelHom strModel natModel` could not be STATED.  Fixed by the
        shared `TheoryGrammar.Theories.Monoid`.

    (2) `transportGF` speaks the MODEL-level `_ℕ⊗_` (`⊗[ appop ]`),
        because that is the connective `ChangeOfTheory` is stated at,
        while every ℕ-side program is written at the substrate-level
        `⊗ˢ`.  Fixed by `⊗ˢᴺ→⊗ᴺ` / `⊗ᴺ→⊗ˢᴺ` and `pull⊗ˢ'` in `Length`.

  WHAT THE RESULT IS, AND IS NOT.  `pull D w` is "the LENGTH of w admits
  a Dyck bracketing", not "w is a Dyck word": `length` forgets which
  letters were used, so what transports is the length-graded shadow.
  Getting the bracket language on the nose is a change of SIGNATURE (a
  two-letter alphabet with a matching constraint), not of model.  The
  content here is the transport principle, and Dyck is its witness.
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Nat.Transport (Char : Type₀) where

open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)

-- the strings side, `pull`, and the transport machinery
open import TheoryGrammar.Instances.Nat.Length Char public

-- the ℕ side, qualified: `Species` exports `Gr`, `_⊗'_`, `ε'` under the
-- same names as the string instance
import TheoryGrammar.Instances.Nat.Species as Sp

-- ==================================================================
-- The transported grammar, and the two halves of the recurrence.
-- ==================================================================

-- "the length of this string admits a Dyck bracketing"
DyckLen : Gr
DyckLen = pull Sp.D

-- The right-hand side of the recurrence, at strings.  Note this is
-- written with the STRING `_⊗'_` and `_⊕_`: it is a statement about
-- string grammars, with no ℕ left in it except inside `pull`.
DyckLenBody : Gr
DyckLenBody =
  pull Sp.ε' ⊕ (pull Sp.x ⊗' pull Sp.D ⊗' pull Sp.x ⊗' pull Sp.D)

-- ==================================================================
-- The multiplicative half, one factor at a time.
--
-- `_⊗'_` is `infixr 20`, so the body is `x ⊗ (D ⊗ (x ⊗ D))` and the
-- transport peels it in the same association.  Every family is pinned
-- explicitly -- the CLAUDE.md trap: `⊗ˢ appop (λ a → pull (B a))`
-- unfolds to a Σ in which the family occurs only under `pull` and under
-- `parts`, so no first-order unifier recovers it.
-- ==================================================================

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

-- ==================================================================
-- THE THEOREM.  `pullTerm` carries the ℕ-level derivation across for
-- free -- that is the additive half, and `pull (A ⊕ B)` really is
-- `pull A ⊕ pull B` on the nose (`ChangeOfTheory.pull-⊕` is `refl`), so
-- the `⊕` needs no transport at all.  Only the tensor does.
-- ==================================================================

dyckLen-unroll : DyckLen ⊢ DyckLenBody
dyckLen-unroll = ⊕-E ⊕-I₁ (⊕-I₂ ∘g outer) ∘g pullTerm Sp.dyck-unroll

-- ==================================================================
-- ... AND BACK.  This is the direction that needs `lengthReflects`:
-- `pull⊗ˢ'⁻` is built from `pull⊗⁻`, which exists exactly because
-- `length` is Conduché.  Over abelianisation everything above this line
-- still typechecks and everything below it does not -- which is the
-- sharpest way to see what "reflects splittings" is doing.
-- ==================================================================

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
