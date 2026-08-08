{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Mergesort, fully intrinsic: the output is a SORTED permutation of the
   input, both halves carried by the type. mergesortS : ⊤ ⊢ SortedOf
   SortedOf m = Σ[out] (Sorted out × Perm out m) The permutation half is
   free, as before -- `_⊢_` preserves the index. -}
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

  -- Sortedness.

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

  -- ... and the sorter, as a term.

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

  -- the base case, at the two representables `Small` is built from
  smallSorted : Small ⊢ SortedOf
  smallSorted =
    ⊕-E (⌈⌉-E ([] , []ˢ , nil))
        (⊕ᴰ-E λ x → ⌈⌉-E ((x ∷ []) , consˢ []ᵇ []ˢ , permRefl (x ∷ [])))

  malgS : Algᴳ MF (λ _ → SortedOf)
  malgS tt =
    ⊕ᴰ-E λ { true  → smallSorted ∘g lowerg
           ; false → mergeS ∘g dropNT (λ _ → SortedOf) ∘g outM (λ _ → SortedOf) }

  -- MERGESORT: a sorted permutation of the input, by type
  mergesortS : ⊤G ⊢ SortedOf
  mergesortS = hyloᴳ mfGuarded mcoalg malgS tt

  -- QUICKSORT, sorted. `partitionOrd` already put `Above piv lo` and
  -- `Below piv hi` into the description's slots; the only step is to move
  -- them off the INPUT parts onto the SORTED OUTPUTS, which differ by a
  -- permutation -- `abovePerm` / `belowPerm`.

  sortedNil : ⌈ [] ⌉ ⊢ SortedOf
  sortedNil = ⌈⌉-E ([] , []ˢ , nil)

  joinSortedAt : (piv : A) {lo rest w p1 hi : Bag}
               → Ilv lo rest w → Ilv p1 hi rest → p1 Eq.≡ piv ∷ []
               → (SortedOf & Liftg (Above piv)) lo
               → (SortedOf & Liftg (Below piv)) hi
               → SortedOf w
  joinSortedAt piv e1 e2 Eq.refl ((loOut , sl , pl) , aa) ((hiOut , sh , ph) , bb) =
      (loOut ++ (piv ∷ hiOut))
    , sortedApp sl (abovePerm pl (lower aa)) (belowPerm ph (lower bb)) sh
    , permMerge pl (cons ph e2) e1

  -- PRIMITIVE (phase 1): the join, and the only order-theoretic content
  -- in quicksort's sortedness.  `appendSpec` is its permutation half.
  joinSorted : (piv : A)
             → ((SortedOf & Liftg (Above piv))
                  ⊗' (⌈ piv ∷ [] ⌉ ⊗' (SortedOf & Liftg (Below piv))))
             ⊢ SortedOf
  joinSorted piv w ((lo , rest , e1) , h) = go (h false)
    where
      go : (⌈ piv ∷ [] ⌉ ⊗' (SortedOf & Liftg (Below piv))) rest → SortedOf w
      go ((p1 , hi , e2) , g) = joinSortedAt piv e1 e2 (g true) (h true) (g false)

  qalgS : Algᴳ QF (λ _ → SortedOf)
  qalgS tt =
    ⊕ᴰ-E λ { true  → sortedNil ∘g lowerg
           ; false → ⊕ᴰ-E λ piv → joinSorted piv ∘g outQ (λ _ → SortedOf) piv }

  -- INTRINSICALLY VERIFIED QUICKSORT: a sorted permutation of the
  -- input, by type, from the SAME coalgebra as the plain one.
  quicksortS : ⊤G ⊢ SortedOf
  quicksortS = hyloᴳ qfGuarded qcoalg qalgS tt
