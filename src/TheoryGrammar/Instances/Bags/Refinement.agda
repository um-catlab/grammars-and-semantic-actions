{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- THE FREE COMMUTATIVE MONOID IS A REFINEMENT MONOID -- the Riesz
   refinement property, and the `I = ⊤` control for `Traces`. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Bags.Refinement (A : Type₀) where

open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Unit
open import Cubical.Data.List
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Refinement
open import TheoryGrammar.Instances.Bags.Base A public

open Refine bagFib

appHom : HomOp tt
appHom .op⋆    = appop
appHom .resH   = Eq.refl
appHom .argH _ = Eq.refl

-- The intersection of two interleavings of one bag, as a 2x2 matrix of
-- bags together with the four interleavings that make it one: the rows
-- recompose the parts of the first splitting, the columns those of the
-- second.
record Cross (u₁ v₁ u₂ v₂ : Bag) : Type₀ where
  field
    -- the four intersections, `cᵢⱼ` = (i-th part of the first) ∩
    -- (j-th part of the second)
    c₀₀ c₀₁ c₁₀ c₁₁ : Bag
    -- each ROW recomposes to a part of the first splitting ...
    row₀ : Ilv c₀₀ c₀₁ u₁
    row₁ : Ilv c₁₀ c₁₁ v₁
    -- ... and each COLUMN to a part of the second
    col₀ : Ilv c₀₀ c₁₀ u₂
    col₁ : Ilv c₀₁ c₁₁ v₂

open Cross public

cross : ∀ {u₁ v₁ u₂ v₂ w} → Ilv u₁ v₁ w → Ilv u₂ v₂ w → Cross u₁ v₁ u₂ v₂
cross nil nil =
  record { c₀₀ = [] ; c₀₁ = [] ; c₁₀ = [] ; c₁₁ = []
         ; row₀ = nil ; row₁ = nil ; col₀ = nil ; col₁ = nil }
cross (left {x = y} d₁) (left d₂) =
  record { c₀₀ = y ∷ r .c₀₀ ; c₀₁ = r .c₀₁ ; c₁₀ = r .c₁₀ ; c₁₁ = r .c₁₁
         ; row₀ = left (r .row₀) ; row₁ = r .row₁
         ; col₀ = left (r .col₀) ; col₁ = r .col₁ }
  where r = cross d₁ d₂
cross (left {x = y} d₁) (right d₂) =
  record { c₀₀ = r .c₀₀ ; c₀₁ = y ∷ r .c₀₁ ; c₁₀ = r .c₁₀ ; c₁₁ = r .c₁₁
         ; row₀ = right (r .row₀) ; row₁ = r .row₁
         ; col₀ = r .col₀ ; col₁ = left (r .col₁) }
  where r = cross d₁ d₂
cross (right {x = y} d₁) (left d₂) =
  record { c₀₀ = r .c₀₀ ; c₀₁ = r .c₀₁ ; c₁₀ = y ∷ r .c₁₀ ; c₁₁ = r .c₁₁
         ; row₀ = r .row₀ ; row₁ = left (r .row₁)
         ; col₀ = right (r .col₀) ; col₁ = r .col₁ }
  where r = cross d₁ d₂
cross (right {x = y} d₁) (right d₂) =
  record { c₀₀ = r .c₀₀ ; c₀₁ = r .c₀₁ ; c₁₀ = r .c₁₀ ; c₁₁ = y ∷ r .c₁₁
         ; row₀ = r .row₀ ; row₁ = right (r .row₁)
         ; col₀ = r .col₀ ; col₁ = right (r .col₁) }
  where r = cross d₁ d₂

bagRefinable : Refinable appHom appHom
bagRefinable w (u₁ , v₁ , d₁) (u₂ , v₂ , d₂) = R
  where
  r = cross d₁ d₂
  R : Refinement appHom appHom w (u₁ , v₁ , d₁) (u₂ , v₂ , d₂)
  R .cell true  true  = r .c₀₀
  R .cell true  false = r .c₀₁
  R .cell false true  = r .c₁₀
  R .cell false false = r .c₁₁
  R .rowSplit true  = r .c₀₀ , r .c₀₁ , r .row₀
  R .rowSplit false = r .c₁₀ , r .c₁₁ , r .row₁
  R .rowCell true  true  = Eq.refl
  R .rowCell true  false = Eq.refl
  R .rowCell false true  = Eq.refl
  R .rowCell false false = Eq.refl
  R .colSplit true  = r .c₀₀ , r .c₁₀ , r .col₀
  R .colSplit false = r .c₀₁ , r .c₁₁ , r .col₁
  R .colCell true  true  = Eq.refl
  R .colCell true  false = Eq.refl
  R .colCell false true  = Eq.refl
  R .colCell false false = Eq.refl

-- REFINABLE, NOT RIGID.  `x ∷ y ∷ []` splits as `(x , y)` and as
-- `(y , x)`; rigidity would identify those parts, hence the alphabet.

rigid→singletonEq : (rg : Rigid bagRefinable) (x y : A) → (x ∷ []) Eq.≡ (y ∷ [])
rigid→singletonEq rg x y =
  rigid→sameParts bagRefinable rg (x ∷ y ∷ [])
    (x ∷ [] , y ∷ [] , left (right nil))
    (y ∷ [] , x ∷ [] , right (left nil)) true

-- It computes: the two crossed splittings above refine with the two
-- off-diagonal cells inhabited and the diagonal empty.

private
  module _ (x y : A) where
    dLR : Ilv (x ∷ []) (y ∷ []) (x ∷ y ∷ [])
    dLR = left (right nil)

    dRL : Ilv (y ∷ []) (x ∷ []) (x ∷ y ∷ [])
    dRL = right (left nil)

    _ : cross dLR dRL .c₀₀ Eq.≡ []
    _ = Eq.refl
    _ : cross dLR dRL .c₀₁ Eq.≡ (x ∷ [])
    _ = Eq.refl
    _ : cross dLR dRL .c₁₀ Eq.≡ (y ∷ [])
    _ = Eq.refl
    _ : cross dLR dRL .c₁₁ Eq.≡ []
    _ = Eq.refl
