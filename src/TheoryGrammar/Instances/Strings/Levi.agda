{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- LEVI, AND THE FREE MONOID'S REFINEMENT LAW -- WITHOUT `decChar`. -}
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sum using (_⊎_; inl; inr)
import Cubical.Data.Equality as Eq

module TheoryGrammar.Instances.Strings.Levi (Char : Type₀) where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Unit
open import Cubical.Data.List

open import TheoryGrammar.Refinement
open import TheoryGrammar.Instances.Strings.Base Char

import TheoryGrammar.Instances.Strings.Recompose as Rc
open Rc Char using (isNilEq)

open Refine strFib

-- 0.  Homogeneity.  One sort, so both coercions are `refl` and
--     `SplitH`/`partsH` are `Split`/`parts` on the nose.

appHom : HomOp tt
appHom .op⋆    = appop
appHom .resH   = Eq.refl
appHom .argH _ = Eq.refl

-- 1.  LEVI.  No decidable equality: the two splittings share their
--     output, so the `cons`/`cons` case has nothing to compare.

Refines : String → String → String → String → Type₀
Refines u₁ v₁ u₂ v₂ = Σ[ t ∈ String ] (Split3 u₁ t u₂ × Split3 t v₂ v₁)

levi : ∀ {u₁ v₁ u₂ v₂ w} → Split3 u₁ v₁ w → Split3 u₂ v₂ w
     → Refines u₁ v₁ u₂ v₂ ⊎ Refines u₂ v₂ u₁ v₁
levi nil       sp'        = inl (_ , nil , sp')
levi (cons sp) nil        = inr (_ , nil , cons sp)
levi (cons sp) (cons sp') = go (levi sp sp')
  where go : _ → _
        go (inl (t , P , Q)) = inl (t , cons P , Q)
        go (inr (t , P , Q)) = inr (t , cons P , Q)

-- 2.  `Refines` IS the 2x2 matrix with the upper-right cell empty.

refines→refinement : ∀ {w u₁ v₁ u₂ v₂} {s₁ : Split3 u₁ v₁ w} {s₂ : Split3 u₂ v₂ w}
        → Refines u₁ v₁ u₂ v₂
        → Refinement appHom appHom w (u₁ , v₁ , s₁) (u₂ , v₂ , s₂)
refines→refinement {u₁ = u₁} {v₂ = v₂} (t , P , Q) = R
  where
  R : Refinement appHom appHom _ _ _
  R .cell true  true  = u₁
  R .cell true  false = []
  R .cell false true  = t
  R .cell false false = v₂
  R .rowSplit true  = u₁ , [] , split3-idʳ u₁
  R .rowSplit false = t , v₂ , Q
  R .rowCell true  true  = Eq.refl
  R .rowCell true  false = Eq.refl
  R .rowCell false true  = Eq.refl
  R .rowCell false false = Eq.refl
  R .colSplit true  = u₁ , t , P
  R .colSplit false = [] , v₂ , nil
  R .colCell true  true  = Eq.refl
  R .colCell true  false = Eq.refl
  R .colCell false true  = Eq.refl
  R .colCell false false = Eq.refl

-- The upper-right cell is `[]` BY CONSTRUCTION -- so the sharp form
-- carries the equation rather than the `Unit`-valued predicate, and
-- `zero→refines` has nothing to recover with `isNilEq`.
refines→cellNil : ∀ {w u₁ v₁ u₂ v₂} {s₁ : Split3 u₁ v₁ w} {s₂ : Split3 u₂ v₂ w}
                → (r : Refines u₁ v₁ u₂ v₂)
                → refines→refinement {s₁ = s₁} {s₂ = s₂} r .cell true false
                  Eq.≡ []
refines→cellNil (t , P , Q) = Eq.refl

refines→zero : ∀ {w u₁ v₁ u₂ v₂} {s₁ : Split3 u₁ v₁ w} {s₂ : Split3 u₂ v₂ w}
             → (r : Refines u₁ v₁ u₂ v₂)
             → IsNil (refines→refinement {s₁ = s₁} {s₂ = s₂} r .cell true false)
refines→zero (t , P , Q) = tt

-- Backward, and this is the direction with content: ANY refinement
-- whose upper-right cell is empty is a `Refines`.  The middle piece is
-- the OTHER off-diagonal cell.
zero→refines : ∀ {w u₁ v₁ u₂ v₂} {s₁ : Split3 u₁ v₁ w} {s₂ : Split3 u₂ v₂ w}
             → (R : Refinement appHom appHom w (u₁ , v₁ , s₁) (u₂ , v₂ , s₂))
             → IsNil (R .cell true false) → Refines u₁ v₁ u₂ v₂
zero→refines {u₁ = u₁} {v₂ = v₂} R z = R .cell false true , colToRow , rowToCol
  where
  zz : R .cell true false Eq.≡ []
  zz = isNilEq _ z

  c00≡u₁ : R .cell true true Eq.≡ u₁
  c00≡u₁ = Eq.sym (R .rowCell true true)
         Eq.∙ split3-nilʳ (split3-coe Eq.refl (R .rowCell true false Eq.∙ zz) Eq.refl
                                      (R .rowSplit true .snd .snd))

  c11≡v₂ : R .cell false false Eq.≡ v₂
  c11≡v₂ = Eq.sym (R .colCell false false)
         Eq.∙ split3-nilˡ (split3-coe (R .colCell false true Eq.∙ zz) Eq.refl Eq.refl
                                      (R .colSplit false .snd .snd))

  colToRow : Split3 u₁ (R .cell false true) _
  colToRow = split3-coe (R .colCell true true Eq.∙ c00≡u₁) (R .colCell true false)
                        Eq.refl (R .colSplit true .snd .snd)

  rowToCol : Split3 (R .cell false true) v₂ _
  rowToCol = split3-coe (R .rowCell false true) (R .rowCell false false Eq.∙ c11≡v₂)
                        Eq.refl (R .rowSplit false .snd .snd)

zero→refines-transpose : ∀ {w u₁ v₁ u₂ v₂} {s₁ : Split3 u₁ v₁ w} {s₂ : Split3 u₂ v₂ w}
              → (R : Refinement appHom appHom w (u₁ , v₁ , s₁) (u₂ , v₂ , s₂))
              → IsNil (R .cell false true) → Refines u₂ v₂ u₁ v₁
zero→refines-transpose R z = zero→refines (transpose R) z

-- 3.  REFINABILITY, from `levi` and nothing else.

refinesOr→refinement : ∀ {w u₁ v₁ u₂ v₂} {s₁ : Split3 u₁ v₁ w} {s₂ : Split3 u₂ v₂ w}
         → Refines u₁ v₁ u₂ v₂ ⊎ Refines u₂ v₂ u₁ v₁
         → Refinement appHom appHom w (u₁ , v₁ , s₁) (u₂ , v₂ , s₂)
refinesOr→refinement (inl r) = refines→refinement r
refinesOr→refinement (inr r) = transpose (refines→refinement r)

strRefinable : Refinable appHom appHom
strRefinable w (u₁ , v₁ , s₁) (u₂ , v₂ , s₂) = refinesOr→refinement (levi s₁ s₂)

-- LEVI, RESTATED.  Two splittings of one word admit a refinement with
-- an off-diagonal cell empty -- and the disjunction is which one.  In
-- eliminator form, so no sum appears in the statement.
leviZero : ∀ {ℓZ} {w u₁ v₁ u₂ v₂} (s₁ : Split3 u₁ v₁ w) (s₂ : Split3 u₂ v₂ w)
           {Z : Type ℓZ}
         → ((R : Refinement appHom appHom w (u₁ , v₁ , s₁) (u₂ , v₂ , s₂))
            → IsNil (R .cell true false) → Z)
         → ((R : Refinement appHom appHom w (u₁ , v₁ , s₁) (u₂ , v₂ , s₂))
            → IsNil (R .cell false true) → Z)
         → Z
leviZero {u₁ = u₁} {v₁} {u₂} {v₂} s₁ s₂ {Z} f g = go (levi s₁ s₂)
  where go : Refines u₁ v₁ u₂ v₂ ⊎ Refines u₂ v₂ u₁ v₁ → Z
        go (inl r) = f (refines→refinement r) tt
        go (inr r) = g (transpose (refines→refinement r)) tt

-- 4.  DIAGONALITY, given that the middle piece is empty.  The `⊛`
--     hypothesis that SUPPLIES that emptiness is `Refinement`'s, and
--     is the only part of the old file that needed `decChar`.

refines→diagonal : ∀ {w u₁ v₁ u₂ v₂} {s₁ : Split3 u₁ v₁ w} {s₂ : Split3 u₂ v₂ w}
        → (r : Refines u₁ v₁ u₂ v₂) → IsNil (r .fst)
        → Diagonal (refines→refinement {s₁ = s₁} {s₂ = s₂} r)
refines→diagonal {s₁ = s₁} {s₂} r@(t , P , Q) z = rows , cols
  where
  rows : DiagonalRows (refines→refinement {s₁ = s₁} {s₂ = s₂} r)
  rows true  = Eq.refl
  rows false = split3-nilˡ (split3-coe (isNilEq t z) Eq.refl Eq.refl Q)
  cols : DiagonalCols (refines→refinement {s₁ = s₁} {s₂ = s₂} r)
  cols true  = split3-nilʳ (split3-coe Eq.refl (isNilEq t z) Eq.refl P)
  cols false = Eq.refl

-- 5.  It computes.  Two splittings of `a ∷ b ∷ []` -- the empty cut and
-- the full cut -- refine with lower-left cell `a ∷ b ∷ []` and the
-- other three empty.

private
  module _ (a b : Char) where
    w₂ : String
    w₂ = a ∷ b ∷ []

    pL : SplitH appHom w₂
    pL = [] , w₂ , nil

    pR : SplitH appHom w₂
    pR = w₂ , [] , split3-idʳ w₂

    Rab : Refinement appHom appHom w₂ pL pR
    Rab = strRefinable w₂ pL pR

    _ : Rab .cell false true Eq.≡ w₂
    _ = Eq.refl

    _ : Rab .cell true true Eq.≡ []
    _ = Eq.refl

    _ : Rab .cell true false Eq.≡ []
    _ = Eq.refl

    _ : Rab .cell false false Eq.≡ []
    _ = Eq.refl
