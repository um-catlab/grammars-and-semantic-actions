{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Sorting at ℕ: quicksort, its intrinsically-verified form, and mergesort. -}
module TheoryGrammar.Instances.Bags.Examples where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
open import Cubical.Data.Nat
open import Cubical.Data.List
import Cubical.Data.Equality as Eq
open import Cubical.Data.Maybe using (Maybe; just; nothing)

open import TheoryGrammar.Instances.Bags.Sorted ℕ

leℕ : ℕ → ℕ → Bool
leℕ zero    _       = true
leℕ (suc m) zero    = false
leℕ (suc m) (suc n) = leℕ m n

open Sort  leℕ
open MSort leℕ

_ : quicksort [] ≡ []
_ = refl

_ : quicksort (1 ∷ []) ≡ (1 ∷ [])
_ = refl

_ : quicksort (2 ∷ 1 ∷ []) ≡ (1 ∷ 2 ∷ [])
_ = refl

_ : quicksort (5 ∷ 3 ∷ 4 ∷ 1 ∷ 2 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
_ = refl

-- _ : quicksort (5 ∷ 3 ∷ 4 ∷ 1 ∷ 2 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
-- _ = refl


-- The verified version computes to the same answer, and its second
-- component is the permutation proof, produced by construction.  It is
-- a MAP OUT OF TOP, so it is read out by the generic interface --
-- `qsortV = observe quicksortC (tagA Bag)` -- rather than by projecting
-- `.fst` at the use site.
_ : qsortV (5 ∷ 3 ∷ 4 ∷ 1 ∷ 2 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
_ = refl

_ : qsortV (2 ∷ 2 ∷ 1 ∷ []) ≡ (1 ∷ 2 ∷ 2 ∷ [])
_ = refl

_ : mergesort (5 ∷ 3 ∷ 4 ∷ 1 ∷ 2 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
_ = refl

_ : mergesort (2 ∷ 2 ∷ 1 ∷ []) ≡ (1 ∷ 2 ∷ 2 ∷ [])
_ = refl

-- ==================================================================
-- `bagCase`, the view the sorters are built on, is itself a map out of
-- `⊤` -- a `Cover (⌈ [] ⌉ ⊕ ⊕ᴰ A …)`, i.e. a `Result` -- so it is read
-- by the same interface.  Its right branch is a `⊕ᴰ` over the element
-- pulled off, so `tagA` recovers that element.
-- ==================================================================

empty? : List ℕ → Bool
empty? = accepts? ⌈ [] ⌉ (⊕ᴰ ℕ (λ x → ⌈ x ∷ [] ⌉ ⊗' ⊤G)) bagCase

-- the element `bagCase` chose, read out by the generic `tagA`
someElem : List ℕ → Maybe ℕ
someElem = observe bagCase
             (caseA (pureA (Maybe ℕ) nothing) (mapA just (tagA ℕ)))

_ : empty? []            ≡ true
_ = refl

_ : empty? (3 ∷ [])      ≡ false
_ = refl

_ : someElem []          ≡ nothing
_ = refl

_ : someElem (3 ∷ 1 ∷ []) ≡ just 3
_ = refl

-- ==================================================================
-- Fully intrinsic mergesort: a SORTED PERMUTATION by type.
-- ==================================================================

leTotalℕ : (x y : ℕ) → leℕ x y Eq.≡ false → leℕ y x Eq.≡ true
leTotalℕ zero    y       ()
leTotalℕ (suc m) zero    e = Eq.refl
leTotalℕ (suc m) (suc n) e = leTotalℕ m n e

leTransℕ : (x y z : ℕ) → leℕ x y Eq.≡ true → leℕ y z Eq.≡ true
         → leℕ x z Eq.≡ true
leTransℕ zero    y       z       p q = Eq.refl
leTransℕ (suc m) zero    z       () q
leTransℕ (suc m) (suc n) zero    p ()
leTransℕ (suc m) (suc n) (suc k) p q = leTransℕ m n k p q

module S = Sortedness leℕ leTotalℕ leTransℕ

_ : S.mergesortS (5 ∷ 3 ∷ 4 ∷ 1 ∷ 2 ∷ []) tt .fst ≡ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
_ = refl

_ : S.mergesortS (2 ∷ 2 ∷ 1 ∷ []) tt .fst ≡ (1 ∷ 2 ∷ 2 ∷ [])
_ = refl
