{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{- TWO THEORIES ON ONE CARRIER: concatenation and interleaving on `List A`. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Strings.Shuffle (A : Type₀) where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.List
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Theories.Monoid
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib
open import TheoryGrammar.Splitting
open import TheoryGrammar.Refinement
open import TheoryGrammar.Precision

import TheoryGrammar.Instances.Strings.Base as StB
module S = StB A
import TheoryGrammar.Instances.Bags.Base as BgB
module B = BgB A
import TheoryGrammar.Instances.Bags.Refinement as BgR
module BR = BgR A
import TheoryGrammar.Instances.Strings.Recompose as Rc
module Rec = Rc A
import TheoryGrammar.Instances.Strings.Levi as SLv
module SL = SLv A

-- ONE CARRIER, TWO SPLITTINGS.  Note what is NOT written: an equation
-- between two carriers.  `splittingOf` forgets each `Fibered`'s carrier
-- and `⊎Spl` puts the remainders side by side.

bothSpl : Splitting (monoidSig ⊎Sig monoidSig) (λ _ → List A) ℓ-zero
bothSpl = splittingOf S.strFib ⊎Spl splittingOf B.bagFib

bothFib : Fibered (monoidSig ⊎Sig monoidSig) ℓ-zero ℓ-zero
bothFib = ⟪ (λ _ → List A) , bothSpl ⟫

module M = RulesF bothFib

Gr : Type₁
Gr = M.TheoryTy ℓ-zero tt

-- a slot family must be NAMED, never an extended lambda
pair : Gr → Gr → (a : MonAr appop) → Gr
pair P Q true  = P
pair P Q false = Q

infixr 20 _⊗ᵒ_ _⊗ᶜ_

-- the ordered tensor ...
_⊗ᵒ_ : Gr → Gr → Gr
P ⊗ᵒ Q = M.⊗ˢ (inl appop) (pair P Q)

-- ... and the commutative one, over the very same grammars
_⊗ᶜ_ : Gr → Gr → Gr
P ⊗ᶜ Q = M.⊗ˢ (inr appop) (pair P Q)

-- THE COMPARISON.

-- DERIVABLE, not primitive: `Bags/Base.ilvApp u v : Ilv u v (u ++ v)`
-- at `u = []` already is this, since `[] ++ v` reduces to `v`.
ilvNilL : (v : List A) → B.Ilv [] v v
ilvNilL = B.ilvApp []

-- PRIMITIVE.  Every ordered splitting IS an interleaving -- take every
-- step from the left, then the rest from the right.
ordIlv : {u v w : List A} → S.Split3 u v w → B.Ilv u v w
ordIlv S.nil      = ilvNilL _
ordIlv (S.cons p) = B.left (ordIlv p)

-- THE TERM.  The payload is handed over untouched: both theories read
-- `parts appop w (u , v , _)` as `if _ then u else v`, so the slots
-- already hold what the target expects.  Only the splitting moves.
shuffle : (P Q : Gr) → (P ⊗ᵒ Q) M.⊢ (P ⊗ᶜ Q)
shuffle P Q w ((u , v , p) , h) = (u , v , ordIlv p) , h

-- ... AND IT HAS NO INVERSE, so the two operations are distinct.

private
  hd : A → List A → A
  hd d []      = d
  hd d (c ∷ _) = c

-- PRIMITIVE.  `x ∷ y ∷ []` does not split as `y ∷ []` before `x ∷ []`,
-- unless the two letters agree.  Via recomposition, so no head is ever
-- unified -- the trap `SeqUnambig` documents.
noSwap : (x y : A) → (x Eq.≡ y → ⊥)
       → S.Split3 (y ∷ []) (x ∷ []) (x ∷ y ∷ []) → ⊥
noSwap x y ne p = ne (Eq.ap (hd x) (Rec.recompose p))

module _ (x y : A) (ne : x Eq.≡ y → ⊥) where

  private
    w2 : List A
    w2 = x ∷ y ∷ []

    -- `y` first and `x` second IS an interleaving of `x ∷ y ∷ []` ...
    swapped : (M.⌈ y ∷ [] ⌉ ⊗ᶜ M.⌈ x ∷ [] ⌉) w2
    swapped = ((y ∷ []) , (x ∷ []) , B.right (B.left B.nil)) , payload
      where
      payload : (a : MonAr appop)
              → pair (M.⌈ y ∷ [] ⌉) (M.⌈ x ∷ [] ⌉) a
                  (bothFib .parts (inr appop) w2
                     ((y ∷ []) , (x ∷ []) , B.right (B.left B.nil)) a)
      payload true  = Eq.refl
      payload false = Eq.refl

  -- ... and no term can turn it back into a concatenation.
  noUnshuffle : ((P Q : Gr) → (P ⊗ᶜ Q) M.⊢ (P ⊗ᵒ Q)) → ⊥
  noUnshuffle unsh with unsh (M.⌈ y ∷ [] ⌉) (M.⌈ x ∷ [] ⌉) w2 swapped
  ... | (u , v , p) , h = go (h true) (h false) p
    where
    go : u Eq.≡ (y ∷ []) → v Eq.≡ (x ∷ []) → S.Split3 u v w2 → ⊥
    go Eq.refl Eq.refl q = noSwap x y ne q

-- TESTS.  The comparison computes: an ordered cut becomes the
-- corresponding interleaving, on the nose.

module _ (x y : A) where

  private
    w2 : List A
    w2 = x ∷ y ∷ []

    ordered : (M.⌈ x ∷ [] ⌉ ⊗ᵒ M.⌈ y ∷ [] ⌉) w2
    ordered = ((x ∷ []) , (y ∷ []) , S.cons S.nil) , payload
      where
      payload : (a : MonAr appop)
              → pair (M.⌈ x ∷ [] ⌉) (M.⌈ y ∷ [] ⌉) a
                  (bothFib .parts (inl appop) w2
                     ((x ∷ []) , (y ∷ []) , S.cons S.nil) a)
      payload true  = Eq.refl
      payload false = Eq.refl

    shuffled : (M.⌈ x ∷ [] ⌉ ⊗ᶜ M.⌈ y ∷ [] ⌉) w2
    shuffled = shuffle (M.⌈ x ∷ [] ⌉) (M.⌈ y ∷ [] ⌉) w2 ordered

  _ : shuffled .fst .fst ≡ x ∷ []
  _ = refl

  _ : shuffled .fst .snd .fst ≡ y ∷ []
  _ = refl

  -- the interleaving really is the left-then-right one
  _ : shuffled .fst .snd .snd ≡ B.left (B.right B.nil)
  _ = refl

-- THE TENSOR OF THE TWO THEORIES. `Refinement.Refinable o o'` is the
-- interchange law between two operations on one carrier -- the 2x2 matrix
-- whose rows recompose to one splitting's parts and whose columns to the
-- other's.

module R  = Refine bothFib
module RB = Refine B.bagFib
module RS = Refine S.strFib

ordOp : R.HomOp tt
ordOp .R.op⋆    = inl appop
ordOp .R.resH   = Eq.refl
ordOp .R.argH _ = Eq.refl

comOp : R.HomOp tt
comOp .R.op⋆    = inr appop
comOp .R.resH   = Eq.refl
comOp .R.argH _ = Eq.refl

-- the matrix, before it is packaged: four cells, the two row
-- interleavings and the two column cuts
record Cross (u₁ u₂ v₁ v₂ : List A) : Type₀ where
  constructor mkCross
  field
    c₁₁ c₁₂ c₂₁ c₂₂ : List A
    row₁ : B.Ilv c₁₁ c₁₂ u₁
    row₂ : B.Ilv c₂₁ c₂₂ u₂
    col₁ : S.Split3 c₁₁ c₂₁ v₁
    col₂ : S.Split3 c₁₂ c₂₂ v₂

open Cross

-- PRIMITIVE.  The cross-split itself.  Three clauses: the cut is at the
-- very start, or the head belongs to the cut's left block and then goes
-- to whichever block the interleaving sends it.
cross : {u₁ u₂ v₁ v₂ w : List A}
      → S.Split3 u₁ u₂ w → B.Ilv v₁ v₂ w → Cross u₁ u₂ v₁ v₂
cross S.nil        q            = mkCross [] [] _ _ B.nil q S.nil S.nil
cross (S.cons p) (B.left  q) =
  let X = cross p q
  in mkCross (_ ∷ X .c₁₁) (X .c₁₂) (X .c₂₁) (X .c₂₂)
       (B.left (X .row₁)) (X .row₂) (S.cons (X .col₁)) (X .col₂)
cross (S.cons p) (B.right q) =
  let X = cross p q
  in mkCross (X .c₁₁) (_ ∷ X .c₁₂) (X .c₂₁) (X .c₂₂)
       (B.right (X .row₁)) (X .row₂) (X .col₁) (S.cons (X .col₂))

-- ... and the interchange law.  Every cell equation is `Eq.refl`,
-- because a splitting IS its parts here: `rowSplit` is built holding
-- exactly the cells the equation asks about.
mixedRefinable : R.Refinable ordOp comOp
mixedRefinable w (u₁ , u₂ , p) (v₁ , v₂ , q) = res
  where
  X : Cross u₁ u₂ v₁ v₂
  X = cross p q

  cl : Bool → Bool → List A
  cl true  true  = X .c₁₁
  cl true  false = X .c₁₂
  cl false true  = X .c₂₁
  cl false false = X .c₂₂

  res : R.Refinement ordOp comOp w (u₁ , u₂ , p) (v₁ , v₂ , q)
  res .R.cell               = cl
  res .R.rowSplit true      = X .c₁₁ , X .c₁₂ , X .row₁
  res .R.rowSplit false     = X .c₂₁ , X .c₂₂ , X .row₂
  res .R.rowCell true  true  = Eq.refl
  res .R.rowCell true  false = Eq.refl
  res .R.rowCell false true  = Eq.refl
  res .R.rowCell false false = Eq.refl
  res .R.colSplit true      = X .c₁₁ , X .c₂₁ , X .col₁
  res .R.colSplit false     = X .c₁₂ , X .c₂₂ , X .col₂
  res .R.colCell true  true  = Eq.refl
  res .R.colCell true  false = Eq.refl
  res .R.colCell false true  = Eq.refl
  res .R.colCell false false = Eq.refl

-- The COMMUTATIVE homogeneous law, transported from `Bags/Refinement`.
comRefinable : R.Refinable comOp comOp
comRefinable w p q = res
  where
  Z = BR.bagRefinable w p q

  res : R.Refinement comOp comOp w p q
  res .R.cell     = Z .RB.cell
  res .R.rowSplit = Z .RB.rowSplit
  res .R.rowCell  = Z .RB.rowCell
  res .R.colSplit = Z .RB.colSplit
  res .R.colCell  = Z .RB.colCell

-- The ORDERED homogeneous law, transported from `Strings/Levi` the same
-- way.
ordRefinable : R.Refinable ordOp ordOp
ordRefinable w p q = res
  where
  Z = SL.strRefinable w p q

  res : R.Refinement ordOp ordOp w p q
  res .R.cell     = Z .RS.cell
  res .R.rowSplit = Z .RS.rowSplit
  res .R.rowCell  = Z .RS.rowCell
  res .R.colSplit = Z .RS.colSplit
  res .R.colCell  = Z .RS.colCell

-- PRECISION SEPARATES THE TWO THEORIES. `Refinable` above says the two
-- operations INTERCHANGE.

module P = Prec bothFib

-- (`appCancel` and `ordDetermines` are in `Strings/Recompose`.)

-- POSITIVE: every representable is precise for CONCATENATION.

ordPrecise : (r : List A) → P.PreciseI ℓ-zero (inl appop) true (M.⌈ r ⌉)
ordPrecise r Bs Cs m ((( u₁ , v₁ , p) , Eq.refl , h₁)
                     , ((.u₁ , v₂ , q) , Eq.refl , h₂)) =
  (u₁ , v₁ , p) , Eq.refl , k
  where
  same : v₁ Eq.≡ v₂
  same = Rec.ordDetermines p q

  k : (a : MonAr appop)
    → (Bs a M.& Cs a) (bothFib .parts (inl appop) m (u₁ , v₁ , p) a)
  k true  = h₁ true  , h₂ true
  k false = h₁ false , coeEq (Cs false) (Eq.sym same) (h₂ false)

-- NEGATIVE: it fails for INTERLEAVING.  `x ∷ y ∷ x ∷ []` shuffles with
-- `x ∷ []` removed in two places, and the two remainders are different
-- LISTS -- which is exactly what a cut cannot do.

module _ (x y : A) (ne : x Eq.≡ y → ⊥) where

  private
    m3 : List A
    m3 = x ∷ y ∷ x ∷ []

    Bs Cs : (a : MonAr appop) → Gr
    Bs true  = M.⊤G
    Bs false = M.⌈ y ∷ x ∷ [] ⌉
    Cs true  = M.⊤G
    Cs false = M.⌈ x ∷ y ∷ [] ⌉

    -- drop the FIRST x ...
    first : P.⊗at (inr appop) true (M.⌈ x ∷ [] ⌉) Bs m3
    first = ((x ∷ []) , (y ∷ x ∷ []) , B.left (B.right (B.right B.nil)))
          , Eq.refl , pay
      where
      pay : (a : MonAr appop) → Bs a _
      pay true  = tt
      pay false = Eq.refl

    -- ... or the LAST one
    last : P.⊗at (inr appop) true (M.⌈ x ∷ [] ⌉) Cs m3
    last = ((x ∷ []) , (x ∷ y ∷ []) , B.right (B.right (B.left B.nil)))
         , Eq.refl , pay
      where
      pay : (a : MonAr appop) → Cs a _
      pay true  = tt
      pay false = Eq.refl

  comNotPrecise : P.PreciseI ℓ-zero (inr appop) true (M.⌈ x ∷ [] ⌉) → ⊥
  comNotPrecise pr with pr Bs Cs m3 (first , last)
  ... | _ , _ , k = ne (Eq.sym (Eq.ap (hd x) (Eq.sym (k false .fst)
                                               Eq.∙ k false .snd)))

-- THE SAME FACT IN THE SUBSTRATE'S OWN VOCABULARY.

module _ (x y : A) (ne : x Eq.≡ y → ⊥) where

  private
    m3′ : List A
    m3′ = x ∷ y ∷ x ∷ []

    sp₁ sp₂ : bothFib .Split (inr appop) m3′
    sp₁ = (x ∷ []) , (y ∷ x ∷ []) , B.left (B.right (B.right B.nil))
    sp₂ = (x ∷ []) , (x ∷ y ∷ []) , B.right (B.right (B.left B.nil))

  comNotSlotDet : P.SlotDet (inr appop) true → ⊥
  comNotSlotDet det =
    ne (Eq.sym (Eq.ap (hd x) (det m3′ sp₁ sp₂ Eq.refl false)))
