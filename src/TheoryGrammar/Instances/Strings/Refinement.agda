{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- THE FREE MONOID IS A REFINEMENT MONOID -- and Levi's DISJUNCTION is
   "which off-diagonal cell vanishes".

   `SeqUnambig.Refines u₁ v₁ u₂ v₂ = Σ t. Split3 u₁ t u₂ × Split3 t v₂ v₁`
   is not a weaker statement than the 2x2 matrix: it IS the matrix
   `[[u₁ , ε] , [t , v₂]]`, with the upper-right entry forced empty.
   That is proved both ways below (`refines→zero`, `zero→refines`), so
   the two-case disjunction of `levi` is exactly the choice of WHICH
   off-diagonal vanishes -- and the commutative and trace versions have
   no case split because there nothing has to vanish.

   Nothing is reproved: `strRefinable` consumes `levi`.

   MAIN: `strRefinable`, `leviZero` (`levi` in eliminator form),
   `strNonOverlap`, and `recoversˡ`/`recoversʳ` -- `SeqUnambig.sameParts`
   as two lemmas.

   PRIMITIVE: `s3coe` (the file's one `Eq.refl` match).  `s3nilR` and
   `splitRefl` duplicate `Laws.splitNilR` and `Par.splitRightNil`, which
   are not on this file's import chain; they belong in `Strings/Base`
   (whereupon `s3nilʳ`/`s3nilˡ`/`split3-coe` are the names they want). -}
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sum using (_⊎_; inl; inr)
import Cubical.Data.Equality as Eq
open import TheoryGrammar.Enumerable using (No)

module TheoryGrammar.Instances.Strings.Refinement
  (Char : Type₀)
  (decChar : (a b : Char) → (a Eq.≡ b) ⊎ No (a Eq.≡ b))
  where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Unit
open import Cubical.Data.List

open import TheoryGrammar.Refinement
open import TheoryGrammar.Instances.Strings.SeqUnambig Char decChar public

open Refine strFib

-- ==================================================================
-- Concatenation is homogeneous: one sort, so both coercions are `refl`
-- and `SplitH`/`partsH` are `Split`/`parts` on the nose.
-- ==================================================================

appHom : HomOp tt
appHom .op⋆    = appop
appHom .resH   = Eq.refl
appHom .argH _ = Eq.refl

-- PRIMITIVE.  Move a splitting along strict equalities of its indices.
s3coe : ∀ {a a' b b' c c'} → a Eq.≡ a' → b Eq.≡ b' → c Eq.≡ c'
      → Split3 a b c → Split3 a' b' c'
s3coe Eq.refl Eq.refl Eq.refl s = s

s3nilR : ∀ {u w} → Split3 u [] w → u Eq.≡ w
s3nilR nil      = Eq.refl
s3nilR (cons s) = go (s3nilR s)
  where go : _ → _
        go Eq.refl = Eq.refl

s3nilL : ∀ {v w} → Split3 [] v w → v Eq.≡ w
s3nilL nil = Eq.refl

splitRefl : (u : String) → Split3 u [] u
splitRefl []      = nil
splitRefl (c ∷ u) = cons (splitRefl u)

isNilEq : (u : String) → IsNil u → u Eq.≡ []
isNilEq []      _  = Eq.refl
isNilEq (_ ∷ _) ()

-- ==================================================================
-- 1.  `Refines` IS A REFINEMENT WITH A FORCED ZERO.
--
-- Forward: read the matrix off `Refines`.  The upper-right cell is
-- `[]` by construction, and the remaining three are `u₁`, `t`, `v₂`.
-- ==================================================================

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
  R .rowSplit true  = u₁ , [] , splitRefl u₁
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

-- ... and the `IsNil` form `levi`'s interface is stated in, which is
-- what `leviZero` and `zero→refines` speak
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
         Eq.∙ s3nilR (s3coe Eq.refl (R .rowCell true false Eq.∙ zz) Eq.refl
                            (R .rowSplit true .snd .snd))

  c11≡v₂ : R .cell false false Eq.≡ v₂
  c11≡v₂ = Eq.sym (R .colCell false false)
         Eq.∙ s3nilL (s3coe (R .colCell false true Eq.∙ zz) Eq.refl Eq.refl
                            (R .colSplit false .snd .snd))

  colToRow : Split3 u₁ (R .cell false true) _
  colToRow = s3coe (R .colCell true true Eq.∙ c00≡u₁) (R .colCell true false)
                   Eq.refl (R .colSplit true .snd .snd)

  rowToCol : Split3 (R .cell false true) v₂ _
  rowToCol = s3coe (R .rowCell false true) (R .rowCell false false Eq.∙ c11≡v₂)
                   Eq.refl (R .rowSplit false .snd .snd)

-- ... and the mirror case is the transpose, with no new proof
zero→refines-transpose : ∀ {w u₁ v₁ u₂ v₂} {s₁ : Split3 u₁ v₁ w} {s₂ : Split3 u₂ v₂ w}
              → (R : Refinement appHom appHom w (u₁ , v₁ , s₁) (u₂ , v₂ , s₂))
              → IsNil (R .cell false true) → Refines u₂ v₂ u₁ v₁
zero→refines-transpose R z = zero→refines (transpose R) z

-- ==================================================================
-- 2.  REFINABILITY, from `levi` and nothing else.
-- ==================================================================

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

-- ==================================================================
-- 3.  `SeqUnambig.sameParts`, AS AN INSTANCE OF THE GENERIC THEOREM.
--
-- `⊛` enters at exactly one point: it forces the middle piece empty,
-- which is `Diagonal`.  Everything after that is `Refinement`'s.
-- ==================================================================

noMiddle : {A B : Gr} → A ⊛ B
         → ∀ {u₁ v₁ u₂ v₂ t} → A u₁ → B v₁ → A u₂ → B v₂
         → Split3 u₁ t u₂ → Split3 t v₂ v₁ → IsNil t
noMiddle su a₁ b₁ a₂ b₂ P nil                = tt
noMiddle su a₁ b₁ a₂ b₂ P (cons {c = c'} q') = clash (su c')
  where clash : _ → _
        clash (inl nf)  = lower (nf a₁ P a₂)
        clash (inr nfi) = lower (nfi _ b₁)

refines→diagonal : ∀ {w u₁ v₁ u₂ v₂} {s₁ : Split3 u₁ v₁ w} {s₂ : Split3 u₂ v₂ w}
        → (r : Refines u₁ v₁ u₂ v₂) → IsNil (r .fst)
        → Diagonal (refines→refinement {s₁ = s₁} {s₂ = s₂} r)
refines→diagonal {s₁ = s₁} {s₂} r@(t , P , Q) z = rows , cols
  where
  rows : DiagonalRows (refines→refinement {s₁ = s₁} {s₂ = s₂} r)
  rows true  = Eq.refl
  rows false = s3nilL (s3coe (isNilEq t z) Eq.refl Eq.refl Q)
  cols : DiagonalCols (refines→refinement {s₁ = s₁} {s₂ = s₂} r)
  cols true  = s3nilR (s3coe Eq.refl (isNilEq t z) Eq.refl P)
  cols false = Eq.refl

strNonOverlap : (A B : Gr) → A ⊛ B
              → NonOverlap appHom strRefinable (λ i → if i then A else B)
strNonOverlap A B su w (u₁ , v₁ , s₁) (u₂ , v₂ , s₂) x y = go (levi s₁ s₂)
  where
  go : (d : Refines u₁ v₁ u₂ v₂ ⊎ Refines u₂ v₂ u₁ v₁)
     → Diagonal (refinesOr→refinement {s₁ = s₁} {s₂ = s₂} d)
  go (inl (t , P , Q)) =
    refines→diagonal (t , P , Q) (noMiddle su (x true) (x false) (y true) (y false) P Q)
  go (inr (t , P , Q)) =
    diagTranspose (refines→refinement (t , P , Q))
      (refines→diagonal (t , P , Q) (noMiddle su (y true) (y false) (x true) (x false) P Q))

-- the generic conclusion ...
strSameParts : (A B : Gr) → A ⊛ B
             → (w : String) (p q : SplitH appHom w)
             → ((i : Bool) → (if i then A else B) (partsH appHom w p i))
             → ((i : Bool) → (if i then A else B) (partsH appHom w q i))
             → (i : Bool) → partsH appHom w p i Eq.≡ partsH appHom w q i
strSameParts A B su =
  nonOverlap→sameParts appHom strRefinable (λ i → if i then A else B)
                       (strNonOverlap A B su)

-- ... AT EACH SLOT.  The payload families are named here rather than
-- written as extended lambdas at each use, because two extended lambdas
-- are never convertible (CONVENTIONS) and the three lemmas below have to
-- share one.
sameSlot : (A B : Gr) → A ⊛ B
         → ∀ {u₁ v₁ u₂ v₂ w} (s₁ : Split3 u₁ v₁ w) (s₂ : Split3 u₂ v₂ w)
         → A u₁ → B v₁ → A u₂ → B v₂
         → (i : Bool) → partsH appHom _ (u₁ , v₁ , s₁) i
                        Eq.≡ partsH appHom _ (u₂ , v₂ , s₂) i
sameSlot A B su {u₁} {v₁} {u₂} {v₂} {w} s₁ s₂ a₁ b₁ a₂ b₂ =
  strSameParts A B su w (u₁ , v₁ , s₁) (u₂ , v₂ , s₂)
    (λ { true → a₁ ; false → b₁ }) (λ { true → a₂ ; false → b₂ })

-- the two halves of `SeqUnambig.sameParts`, each on its own
recoversˡ : {A B : Gr} → A ⊛ B
          → ∀ {u₁ v₁ u₂ v₂ w} → Split3 u₁ v₁ w → Split3 u₂ v₂ w
          → A u₁ → B v₁ → A u₂ → B v₂ → u₁ Eq.≡ u₂
recoversˡ {A} {B} su s₁ s₂ a₁ b₁ a₂ b₂ =
  sameSlot A B su s₁ s₂ a₁ b₁ a₂ b₂ true

recoversʳ : {A B : Gr} → A ⊛ B
          → ∀ {u₁ v₁ u₂ v₂ w} → Split3 u₁ v₁ w → Split3 u₂ v₂ w
          → A u₁ → B v₁ → A u₂ → B v₂ → v₁ Eq.≡ v₂
recoversʳ {A} {B} su s₁ s₂ a₁ b₁ a₂ b₂ =
  sameSlot A B su s₁ s₂ a₁ b₁ a₂ b₂ false

-- ... and their pairing IS `SeqUnambig.sameParts`, whose statement is
-- the conjunction.  Kept only to witness that coincidence: prefer
-- `recoversˡ`/`recoversʳ`.
recovers : {A B : Gr} → A ⊛ B
         → ∀ {u₁ v₁ u₂ v₂ w} → Split3 u₁ v₁ w → Split3 u₂ v₂ w
         → A u₁ → B v₁ → A u₂ → B v₂ → (u₁ Eq.≡ u₂) × (v₁ Eq.≡ v₂)
recovers su s₁ s₂ a₁ b₁ a₂ b₂ =
    recoversˡ su s₁ s₂ a₁ b₁ a₂ b₂
  , recoversʳ su s₁ s₂ a₁ b₁ a₂ b₂

-- ==================================================================
-- 4.  It computes.  Two splittings of `a ∷ b ∷ []` -- the empty cut and
-- the full cut -- refine with lower-left cell `a ∷ b ∷ []` and the
-- other three empty.
-- ==================================================================

private
  module _ (a b : Char) where
    w₂ : String
    w₂ = a ∷ b ∷ []

    pL : SplitH appHom w₂
    pL = [] , w₂ , nil

    pR : SplitH appHom w₂
    pR = w₂ , [] , splitRefl w₂

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
