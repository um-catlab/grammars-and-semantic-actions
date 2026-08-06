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
open import TheoryGrammar.SemanticAction using (passes; _↦_; _at_)

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
-- `qsortV = tagA Bag ∘g quicksortC`, a TERM `⊤G ⊢ Δ Bag` -- rather than
-- by projecting `.fst` at the use site.  `run` appears only here.
_ : passes (run qsortV at
             ( (5 ∷ 3 ∷ 4 ∷ 1 ∷ 2 ∷ []) ↦ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
             ∷ (2 ∷ 2 ∷ 1 ∷ [])         ↦ (1 ∷ 2 ∷ 2 ∷ [])
             ∷ [] ))
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

empty? : ⊤G ⊢ Δ Bool
empty? = okA ⌈ [] ⌉ (⊕ᴰ ℕ (λ x → ⌈ x ∷ [] ⌉ ⊗' ⊤G)) ∘g bagCase

-- the element `bagCase` chose, read out by the generic `tagA`
someElem : ⊤G ⊢ Δ (Maybe ℕ)
someElem = caseA (pureA (Maybe ℕ) nothing) (mapA just (tagA ℕ)) ∘g bagCase

_ : passes (run empty? at ([] ↦ true ∷ (3 ∷ []) ↦ false ∷ []))
_ = refl

_ : passes (run someElem at ([] ↦ nothing ∷ (3 ∷ 1 ∷ []) ↦ just 3 ∷ []))
_ = refl
