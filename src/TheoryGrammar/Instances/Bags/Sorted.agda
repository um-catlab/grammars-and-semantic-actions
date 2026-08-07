{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Mergesort, fully intrinsic: the output is a SORTED permutation of the
   input, both halves carried by the type.

     mergesortS : ⊤ ⊢ SortedOf      SortedOf m = Σ[out] (Sorted out × Perm out m)

   The permutation half is free, as before -- `_⊢_` preserves the index.
   The sorted half is not, and is what the order hypotheses below buy. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Bags.Sorted (A : Type₀) where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.List
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded

open import TheoryGrammar.Instances.Bags.Mergesort A public

module Sortedness (le : A → A → Bool)
                  (leTotal : (x y : A) → le x y Eq.≡ false → le y x Eq.≡ true)
                  (leTrans : (x y z : A) → le x y Eq.≡ true → le y z Eq.≡ true
                           → le x z Eq.≡ true)
                  where

  open Sort   le leTotal leTrans
  open MSort  le
  open MSortV le

  -- ================================================================
  -- Sortedness.
  -- ================================================================

  -- `merge` keeps a common lower bound.  As with `mergePerm`, the two
  -- recursive results are ARGUMENTS so the descent stays visible.
  belowMerge : ∀ {z} (a b : Bag) → Below z a → Below z b → Below z (merge a b)
  belowMerge []      b  pa       pb = pb
  belowMerge (x ∷ a) [] pa       pb = pa
  belowMerge {z} (x ∷ a) (y ∷ b) (px ∷ᵇ pa) (py ∷ᵇ pb) =
    go (le x y) (belowMerge a (y ∷ b) pa (py ∷ᵇ pb))
                (belowMerge (x ∷ a) b (px ∷ᵇ pa) pb)
    where
      go : (bl : Bool)
         → Below z (merge a (y ∷ b)) → Below z (merge (x ∷ a) b)
         → Below z (if bl then x ∷ merge a (y ∷ b) else y ∷ merge (x ∷ a) b)
      go true  p q = px ∷ᵇ p
      go false p q = py ∷ᵇ q

  mergeSorted : (a b : Bag) → Sorted a → Sorted b → Sorted (merge a b)
  mergeSorted []      b  sa sb = sb
  mergeSorted (x ∷ a) [] sa sb = sa
  mergeSorted (x ∷ a) (y ∷ b) (consˢ bx sa) (consˢ by sb) =
    go (le x y) Eq.refl
       (mergeSorted a (y ∷ b) sa (consˢ by sb))
       (mergeSorted (x ∷ a) b (consˢ bx sa) sb)
    where
      go : (bl : Bool) → le x y Eq.≡ bl
         → Sorted (merge a (y ∷ b)) → Sorted (merge (x ∷ a) b)
         → Sorted (if bl then x ∷ merge a (y ∷ b) else y ∷ merge (x ∷ a) b)
      go true  e p q =
        consˢ (belowMerge a (y ∷ b) bx (e ∷ᵇ belowTrans e by)) p
      go false e p q =
        consˢ (belowMerge (x ∷ a) b
                (leTotal x y e ∷ᵇ belowTrans (leTotal x y e) bx) by) q

  -- ================================================================
  -- ... and the sorter, as a term.
  -- ================================================================

  SortedOf : Gr
  SortedOf m = Σ[ out ∈ Bag ] (Sorted out × Perm out m)

  SortedIx : Ix → Type₀
  SortedIx i = SortedOf (i .snd)

  mergeSortedAt : ∀ {u v w} → Ilv u v w → SortedOf u → SortedOf v → SortedOf w
  mergeSortedAt s (a , sa , pa) (b , sb , pb) =
    merge a b , mergeSorted a b sa sb
              , permTrans (mergePerm a b) (permMerge pa pb s)

  -- PRIMITIVE (phase 1): the internal term.  It matches the splitting;
  -- downstream this is composed, never re-opened.
  mergeS : (SortedOf ⊗' SortedOf) ⊢ SortedOf
  mergeS w ((u , v , s) , h) = mergeSortedAt s (h true) (h false)

  -- the base case reads the INTERNAL `Small`: empty, or one atom
  smallSorted : (w : Bag) → Small w → SortedOf w
  smallSorted .([])      (inl Eq.refl)       = [] , []ˢ , nil
  smallSorted .(x ∷ [])  (inr (x , Eq.refl)) =
    (x ∷ []) , consˢ []ᵇ []ˢ , cons nil (left nil)

  malgS : AlgC MF SortedIx
  malgS tt =
    ⊕ᴰ-E λ { true  → λ w sm → smallSorted w (lower sm)
           ; false → λ w t →
               ⊗E {P = λ _ → ⟦ MHalf ⟧c SortedIx} {w = w}
                  (λ u v s l r → mergeSortedAt s (l true) (r true)) t }

  -- MERGESORT: a sorted permutation of the input, by type
  mergesortS : ⊤G ⊢ SortedOf
  mergesortS m _ = hyloC mfGuarded mcoalg malgS (tt , m) tt

  -- ================================================================
  -- QUICKSORT, sorted.
  --
  -- Nothing here re-derives an ordering fact: `partitionOrd` already
  -- put `Above piv lo` and `Below piv hi` into the description's slots,
  -- and the only step is to move them off the INPUT parts onto the
  -- SORTED OUTPUTS, which differ from them by a permutation.  That move
  -- is `abovePerm` / `belowPerm`, and it is the reason those two lemmas
  -- exist.  The coalgebra is untouched -- it was already supplying the
  -- witnesses, for the plain sort to ignore.
  -- ================================================================

  sortedNil : {w : Bag} → w Eq.≡ [] → SortedOf w
  sortedNil Eq.refl = [] , []ˢ , nil

  joinS : (piv : A) {lo rest w p1 hi : Bag}
        → Ilv lo rest w → Ilv p1 hi rest → p1 Eq.≡ piv ∷ []
        → SortedOf lo → Above piv lo
        → SortedOf hi → Below piv hi
        → SortedOf w
  joinS piv e1 e2 Eq.refl (loOut , sl , pl) aa (hiOut , sh , ph) bb =
      (loOut ++ (piv ∷ hiOut))
    , sortedApp sl (abovePerm pl aa) (belowPerm ph bb) sh
    , permMerge pl (cons ph e2) e1

  qalgS : AlgC QF SortedIx
  qalgS tt =
    ⊕ᴰ-E λ { true  → λ w e → sortedNil (lower e)
           ; false → ⊕ᴰ-E λ piv → λ w t →
               ⊗E {P = λ a → ⟦ QG piv a ⟧c SortedIx} {w = w}
                  (λ lo rest e1 sLo inner →
                     ⊗E {P = λ a → ⟦ QG' piv a ⟧c SortedIx}
                        (λ p1 hi e2 pf sHi →
                           joinS piv e1 e2 (lower pf)
                                 (sLo true) (lower (sLo false))
                                 (sHi true) (lower (sHi false)))
                        inner) t }

  -- INTRINSICALLY VERIFIED QUICKSORT: a sorted permutation of the
  -- input, by type, from the SAME coalgebra as the plain one.
  quicksortS : ⊤G ⊢ SortedOf
  quicksortS m _ = hyloC qfGuarded qcoalg qalgS (tt , m) tt
