{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Order structure on bags: bounds, sortedness, and how they travel
   along a splitting and along a permutation.

   Placed before the sorters in the chain because BOTH need it --
   mergesort to state `mergeSorted`, and quicksort to carry the pivot
   bounds through its description.  `belowPerm` is the one that matters
   for quicksort: the ordering facts are about the INPUT parts, while
   sortedness is about the sorted OUTPUTS, and those differ by a
   permutation. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Bags.Order (A : Type₀) where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.List
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered

open import TheoryGrammar.Instances.Bags.Permutation A public

module Ord (le : A → A → Bool)
           (leTrans : (x y z : A) → le x y Eq.≡ true → le y z Eq.≡ true
                    → le x z Eq.≡ true)
           where

  -- `Below x m` : x bounds m from below.  `Above x m` : from above.
  data Below (x : A) : Bag → Type₀ where
    []ᵇ  : Below x []
    _∷ᵇ_ : ∀ {y m} → le x y Eq.≡ true → Below x m → Below x (y ∷ m)

  data Above (x : A) : Bag → Type₀ where
    []ᵃ  : Above x []
    _∷ᵃ_ : ∀ {y m} → le y x Eq.≡ true → Above x m → Above x (y ∷ m)

  data Sorted : Bag → Type₀ where
    []ˢ   : Sorted []
    consˢ : ∀ {x m} → Below x m → Sorted m → Sorted (x ∷ m)

  belowTrans : ∀ {x y m} → le x y Eq.≡ true → Below y m → Below x m
  belowTrans p []ᵇ       = []ᵇ
  belowTrans p (q ∷ᵇ bs) = leTrans _ _ _ p q ∷ᵇ belowTrans p bs

  -- a bound on the whole bounds both parts of a splitting
  belowIlv : ∀ {x u v w} → Ilv u v w → Below x w → Below x u × Below x v
  belowIlv nil       b         = []ᵇ , []ᵇ
  belowIlv (left s)  (p ∷ᵇ b)  = let (bu , bv) = belowIlv s b in p ∷ᵇ bu , bv
  belowIlv (right s) (p ∷ᵇ b)  = let (bu , bv) = belowIlv s b in bu , p ∷ᵇ bv

  aboveIlv : ∀ {x u v w} → Ilv u v w → Above x w → Above x u × Above x v
  aboveIlv nil       b         = []ᵃ , []ᵃ
  aboveIlv (left s)  (p ∷ᵃ b)  = let (bu , bv) = aboveIlv s b in p ∷ᵃ bu , bv
  aboveIlv (right s) (p ∷ᵃ b)  = let (bu , bv) = aboveIlv s b in bu , p ∷ᵃ bv

  -- ... and hence along a permutation, since permutation is built from
  -- insertions, which are splittings
  belowPerm : ∀ {x a b} → Perm a b → Below x b → Below x a
  belowPerm nil        bw = []ᵇ
  belowPerm (cons p i) bw =
    let (by , bv) = belowIlv i bw
    in headOf by ∷ᵇ belowPerm p bv
    where headOf : ∀ {x y} → Below x (y ∷ []) → le x y Eq.≡ true
          headOf (p ∷ᵇ _) = p

  -- the quicksort join: `lo ++ piv ∷ hi` is sorted as soon as the two
  -- halves are and the pivot separates them.  This is the ONLY genuinely
  -- order-theoretic content in quicksort's sortedness; everything else
  -- is bookkeeping that the description carries for us.
  belowApp : ∀ {x p a b} → Below x a → le x p Eq.≡ true → Below x b
           → Below x (a ++ p ∷ b)
  belowApp []ᵇ       q bb = q ∷ᵇ bb
  belowApp (r ∷ᵇ ba) q bb = r ∷ᵇ belowApp ba q bb

  sortedApp : ∀ {p a b} → Sorted a → Above p a → Below p b → Sorted b
            → Sorted (a ++ p ∷ b)
  sortedApp []ˢ            []ᵃ       bb sb = consˢ bb sb
  sortedApp (consˢ bx sa) (q ∷ᵃ aa)  bb sb =
    consˢ (belowApp bx q (belowTrans q bb)) (sortedApp sa aa bb sb)

  abovePerm : ∀ {x a b} → Perm a b → Above x b → Above x a
  abovePerm nil        bw = []ᵃ
  abovePerm (cons p i) bw =
    let (by , bv) = aboveIlv i bw
    in headOf by ∷ᵃ abovePerm p bv
    where headOf : ∀ {x y} → Above x (y ∷ []) → le y x Eq.≡ true
          headOf (p ∷ᵃ _) = p
