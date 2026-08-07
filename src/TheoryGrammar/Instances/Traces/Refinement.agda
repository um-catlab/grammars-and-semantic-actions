{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- A TRACE MONOID IS A REFINEMENT MONOID -- for every independence
   relation, with no hypothesis on `Ind` at all.

   `ITr Ind u v w` is a two-colouring of the positions of `w` whose every
   inversion is independent.  Two colourings INTERSECT, and the four
   intersections are the matrix; each side condition the intersection
   needs is an inversion of one of the two given colourings, so `cross`
   consults `Ind` only through `itrIndepAllˡ`/`itrIndepAllʳ`, never
   through a decision.  Everything is at the level of WORDS, so the
   result descends to the quotient rather than being assumed of it.

   The endpoints interpolate: at `Ind = ⊤` this is the bag refinement,
   and at `Ind = ⊥` the off-diagonal cells cannot both be inhabited,
   which is `levi`'s two-case disjunction (`offDiagZero`; `bothCorners`
   is a word where both ARE inhabited once one pair commutes).

   PRIMITIVE: `_∈ᵂ_` (membership, used only to state `Indep2`). -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Traces.Refinement
  (Letter : Type₀) (Ind : Letter → Letter → Type₀) where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Unit
open import Cubical.Data.List
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Refinement
open import TheoryGrammar.Instances.Traces.Base Letter Ind public

open Refine trFib

appHom : HomOp tt
appHom .op⋆    = appop
appHom .resH   = Eq.refl
appHom .argH _ = Eq.refl

-- ==================================================================
-- A sub-factor owes no more than the whole does.  This is the ONLY
-- lemma about `Ind`, and it is what discharges every side condition
-- below: the letter a `right` step must commute past is always owed by
-- a factor of a word whose debt is already known.
--
-- Stated once per factor rather than as a pair: every use below wants
-- one side, and the paired form was only ever projected.
-- ==================================================================

itrIndepAllˡ : ∀ {u v w y} → ITr Ind u v w → IndepAll Ind w y → IndepAll Ind u y
itrIndepAllˡ nil         _       = tt
itrIndepAllˡ (left s)    (i , h) = i , itrIndepAllˡ s h
itrIndepAllˡ (right _ s) (_ , h) = itrIndepAllˡ s h

itrIndepAllʳ : ∀ {u v w y} → ITr Ind u v w → IndepAll Ind w y → IndepAll Ind v y
itrIndepAllʳ nil         _       = tt
itrIndepAllʳ (left s)    (_ , h) = itrIndepAllʳ s h
itrIndepAllʳ (right _ s) (i , h) = i , itrIndepAllʳ s h

-- ==================================================================
-- THE MATRIX, as a record so the four entries and the four splittings
-- stay in step.
-- ==================================================================

-- The intersection of two colourings of one word, as a 2x2 matrix of
-- words together with the four factorisations that make it one: the
-- rows recompose the parts of the first colouring, the columns those
-- of the second.
record Cross (u₁ v₁ u₂ v₂ : Word) : Type₀ where
  field
    -- the four intersections, `cᵢⱼ` = (i-th part of the first) ∩
    -- (j-th part of the second)
    c₀₀ c₀₁ c₁₀ c₁₁ : Word
    -- each ROW recomposes to a part of the first colouring ...
    row₀ : ITr Ind c₀₀ c₀₁ u₁
    row₁ : ITr Ind c₁₀ c₁₁ v₁
    -- ... and each COLUMN to a part of the second
    col₀ : ITr Ind c₀₀ c₁₀ u₂
    col₁ : ITr Ind c₀₁ c₁₁ v₂

open Cross public

-- THE THEOREM.  Four clauses, one per pair of colours at the head
-- letter; the letter lands in the cell its two colours name.
cross : ∀ {u₁ v₁ u₂ v₂ w} → ITr Ind u₁ v₁ w → ITr Ind u₂ v₂ w
      → Cross u₁ v₁ u₂ v₂
cross nil nil =
  record { c₀₀ = [] ; c₀₁ = [] ; c₁₀ = [] ; c₁₁ = []
         ; row₀ = nil ; row₁ = nil ; col₀ = nil ; col₁ = nil }
cross (left {x = y} d₁) (left d₂) =
  record { c₀₀ = y ∷ r .c₀₀ ; c₀₁ = r .c₀₁ ; c₁₀ = r .c₁₀ ; c₁₁ = r .c₁₁
         ; row₀ = left (r .row₀) ; row₁ = r .row₁
         ; col₀ = left (r .col₀) ; col₁ = r .col₁ }
  where r = cross d₁ d₂
cross (left {x = y} d₁) (right h₂ d₂) =
  record { c₀₀ = r .c₀₀ ; c₀₁ = y ∷ r .c₀₁ ; c₁₀ = r .c₁₀ ; c₁₁ = r .c₁₁
         ; row₀ = right (itrIndepAllˡ (r .col₀) h₂) (r .row₀)
         ; row₁ = r .row₁
         ; col₀ = r .col₀ ; col₁ = left (r .col₁) }
  where r = cross d₁ d₂
cross (right {x = y} h₁ d₁) (left d₂) =
  record { c₀₀ = r .c₀₀ ; c₀₁ = r .c₀₁ ; c₁₀ = y ∷ r .c₁₀ ; c₁₁ = r .c₁₁
         ; row₀ = r .row₀ ; row₁ = left (r .row₁)
         ; col₀ = right (itrIndepAllˡ (r .row₀) h₁) (r .col₀)
         ; col₁ = r .col₁ }
  where r = cross d₁ d₂
cross (right {x = y} h₁ d₁) (right h₂ d₂) =
  record { c₀₀ = r .c₀₀ ; c₀₁ = r .c₀₁ ; c₁₀ = r .c₁₀ ; c₁₁ = y ∷ r .c₁₁
         ; row₀ = r .row₀
         ; row₁ = right (itrIndepAllʳ (r .col₀) h₂) (r .row₁)
         ; col₀ = r .col₀
         ; col₁ = right (itrIndepAllʳ (r .row₀) h₁) (r .col₁) }
  where r = cross d₁ d₂

-- ... and that is refinability of the promodel, with no coercion: the
-- signature has one sort, so `SplitH`/`partsH` are `Split`/`parts`.
trRefinable : Refinable appHom appHom
trRefinable w (u₁ , v₁ , d₁) (u₂ , v₂ , d₂) = R
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

-- ==================================================================
-- THE STRONG FORM: the two off-diagonal cells are INDEPENDENT.
--
-- This is the extra content a trace monoid has over a bare refinement
-- monoid, and it is what specialises to Levi's disjunction.  It costs
-- one hypothesis -- symmetry of `Ind`, which every independence alphabet
-- has, and which `cross` itself never needed.
-- ==================================================================

-- PRIMITIVE.  `a ∈ᵂ u` denotes: `a` occurs at some position of `u`.
infix 4 _∈ᵂ_
data _∈ᵂ_ (a : Letter) : Word → Type₀ where
  here  : ∀ {u} → a ∈ᵂ (a ∷ u)
  there : ∀ {b u} → a ∈ᵂ u → a ∈ᵂ (b ∷ u)

-- every letter of `u` commutes with every letter of `v`
Indep2 : Word → Word → Type₀
Indep2 u v = ∀ {a b} → a ∈ᵂ u → b ∈ᵂ v → Ind a b

indepAll∈ : ∀ {u y a} → a ∈ᵂ u → IndepAll Ind u y → Ind a y
indepAll∈ here      (i , _) = i
indepAll∈ (there m) (_ , h) = indepAll∈ m h

crossIndep : (∀ {a b} → Ind a b → Ind b a)
           → ∀ {u₁ v₁ u₂ v₂ w} (d₁ : ITr Ind u₁ v₁ w) (d₂ : ITr Ind u₂ v₂ w)
           → Indep2 (cross d₁ d₂ .c₀₁) (cross d₁ d₂ .c₁₀)
crossIndep sy nil nil ()
crossIndep sy (left d₁) (left d₂) = crossIndep sy d₁ d₂
crossIndep sy (left d₁) (right h₂ d₂) here      n =
  sy (indepAll∈ n (itrIndepAllʳ (cross d₁ d₂ .col₀) h₂))
crossIndep sy (left d₁) (right h₂ d₂) (there m) n = crossIndep sy d₁ d₂ m n
crossIndep sy (right h₁ d₁) (left d₂) m here      =
  indepAll∈ m (itrIndepAllʳ (cross d₁ d₂ .row₀) h₁)
crossIndep sy (right h₁ d₁) (left d₂) m (there n) = crossIndep sy d₁ d₂ m n
crossIndep sy (right h₁ d₁) (right h₂ d₂) = crossIndep sy d₁ d₂

-- AT `I = ⊥`: independence of the two off-diagonal cells says one of
-- them is EMPTY.  That is exactly `levi`'s case split, and it explains
-- why the ordered version has one and the commutative version does not:
-- the disjunction is not part of the refinement axiom, it is what the
-- refinement axiom degenerates to when nothing commutes.  Stated as an
-- eliminator, so no sum appears.
offDiagZero : ∀ {ℓZ} {Z : Type ℓZ} → (∀ {a b} → Ind a b → ⊥)
            → {u v : Word} → Indep2 u v
            → (IsNil u → Z) → (IsNil v → Z) → Z
offDiagZero ni {[]}    {_}     ind f g = f tt
offDiagZero ni {_ ∷ _} {[]}    ind f g = g tt
offDiagZero ni {_ ∷ _} {_ ∷ _} ind f g = E.rec (ni (ind here here))

-- ==================================================================
-- It computes -- and the two off-diagonal cells really can BOTH be
-- inhabited, which is the whole difference from the free monoid.
-- ==================================================================

private
  module _ (x y : Letter) where

    wxy : Word
    wxy = x ∷ y ∷ []

    -- `w` all on the left; and `w` cut after `x`
    dAll : ITr Ind (x ∷ y ∷ []) [] wxy
    dAll = left (left nil)

    dCut : ITr Ind (x ∷ []) (y ∷ []) wxy
    dCut = left (right tt nil)

    _ : cross dAll dCut .c₀₀ Eq.≡ (x ∷ [])
    _ = Eq.refl
    _ : cross dAll dCut .c₀₁ Eq.≡ (y ∷ [])
    _ = Eq.refl
    _ : cross dAll dCut .c₁₀ Eq.≡ []
    _ = Eq.refl
    _ : cross dAll dCut .c₁₁ Eq.≡ []
    _ = Eq.refl

  -- BOTH CORNERS.  With `y` commuting past `x`, the word `x y` splits
  -- as `(x , y)` and also as `(y , x)`; the refinement of those two has
  -- `c₀₁ = x`, `c₁₀ = y`, and no `Refines`-shaped statement can hold.
  module bothCorners (x y : Letter) (yx : Ind y x) where

    dLR : ITr Ind (x ∷ []) (y ∷ []) (x ∷ y ∷ [])
    dLR = left (right tt nil)

    dRL : ITr Ind (y ∷ []) (x ∷ []) (x ∷ y ∷ [])
    dRL = right (yx , tt) (left nil)

    _ : cross dLR dRL .c₀₀ Eq.≡ []
    _ = Eq.refl
    _ : cross dLR dRL .c₀₁ Eq.≡ (x ∷ [])
    _ = Eq.refl
    _ : cross dLR dRL .c₁₀ Eq.≡ (y ∷ [])
    _ = Eq.refl
    _ : cross dLR dRL .c₁₁ Eq.≡ []
    _ = Eq.refl
