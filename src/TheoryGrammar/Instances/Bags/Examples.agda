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

open import TheoryGrammar.Instances.Bags.Automata ℕ

leℕ : ℕ → ℕ → Bool
leℕ zero    _       = true
leℕ (suc m) zero    = false
leℕ (suc m) (suc n) = leℕ m n

leTotalℕ : (x y : ℕ) → leℕ x y Eq.≡ false → leℕ y x Eq.≡ true
leTotalℕ zero    y       ()
leTotalℕ (suc x) zero    e = Eq.refl
leTotalℕ (suc x) (suc y) e = leTotalℕ x y e

leTransℕ : (x y z : ℕ) → leℕ x y Eq.≡ true → leℕ y z Eq.≡ true
         → leℕ x z Eq.≡ true
leTransℕ zero    y       z       p q = Eq.refl
leTransℕ (suc x) zero    z       () q
leTransℕ (suc x) (suc y) zero    p ()
leTransℕ (suc x) (suc y) (suc z) p q = leTransℕ x y z p q

open Sort  leℕ leTotalℕ leTransℕ
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

-- ==================================================================
-- ... and the FULLY intrinsic sorters: the output is a sorted
-- permutation of the input by TYPE, so these `passes` checks are
-- confirming that it computes, not that it is correct.  Both are read
-- by the same generic `tagA`, since `SortedOf` is a `⊕ᴰ` over the
-- output bag just as `SpecG` was.
-- ==================================================================

open Sortedness leℕ leTotalℕ leTransℕ

qsortS : ⊤G ⊢ Δ Bag
qsortS = tagA Bag ∘g quicksortS

msortS : ⊤G ⊢ Δ Bag
msortS = tagA Bag ∘g mergesortS

_ : passes (run qsortS at
      ([] ↦ [] ∷ (5 ∷ 3 ∷ 4 ∷ 1 ∷ 2 ∷ []) ↦ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) ∷ []))
_ = refl

_ : passes (run msortS at
      ([] ↦ [] ∷ (5 ∷ 3 ∷ 4 ∷ 1 ∷ 2 ∷ []) ↦ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []) ∷ []))
_ = refl

-- ==================================================================
-- AUTOMATA over a commutative theory.  Same generic `Automaton` /
-- `Scanner` / `runAut` as the string instance -- only the description
-- and the decomposition axiom differ.
--
-- Both algebras below are commutative, which is what makes the answer
-- independent of the order `bagCase` happens to pull elements out in.
-- ==================================================================

module Sum  = Fold ℕ 0 _+_
module Size = Fold ℕ 0 (λ _ n → suc n)

_ : Sum.runFold (3 ∷ 1 ∷ 2 ∷ []) tt ≡ 6
_ = refl

_ : Sum.runFold [] tt ≡ 0
_ = refl

_ : Size.runFold (3 ∷ 1 ∷ 2 ∷ []) tt ≡ 3
_ = refl
