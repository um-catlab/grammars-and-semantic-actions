{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Sorting at ℕ. Six sorters -- quicksort and mergesort, each plain,
   permutation-verified and sorted-verified -- every one a term `⊤G ⊢ Δ
   Bag` observed by `run` inside a `passes` line. -}
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

open Sort   leℕ leTotalℕ leTransℕ
open MSort  leℕ using (msortP)     -- the plain mergesort ...
open MSortV leℕ                    -- ... and the certified one

-- `quicksortC`/`mergesortV` land in `SpecG` = `Bagged`, a `⊕ᴰ` over
-- the output bag, so reading that bag off is the generic `tagA` and the
-- certificate survives right up to `run`.

msortV : ⊤G ⊢ Δ Bag
msortV = tagA Bag ∘g mergesortV

_ : passes (run qsortV at
             ( []                        ↦ []
             ∷ (1 ∷ [])                  ↦ (1 ∷ [])
             ∷ (2 ∷ 1 ∷ [])              ↦ (1 ∷ 2 ∷ [])
             ∷ (5 ∷ 3 ∷ 4 ∷ 1 ∷ 2 ∷ []) ↦ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
             ∷ (2 ∷ 2 ∷ 1 ∷ [])         ↦ (1 ∷ 2 ∷ 2 ∷ [])
             ∷ [] ))
_ = refl

_ : passes (run msortV at
             ( (5 ∷ 3 ∷ 4 ∷ 1 ∷ 2 ∷ []) ↦ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
             ∷ (2 ∷ 2 ∷ 1 ∷ [])         ↦ (1 ∷ 2 ∷ 2 ∷ [])
             ∷ [] ))
_ = refl

-- ... and the PLAIN sorters: same coalgebra, same answers, no
-- certificate.  What they lack is in the CARRIER, not in how they are
-- observed.
_ : passes (run qsortP at
             ( []                        ↦ []
             ∷ (2 ∷ 1 ∷ [])              ↦ (1 ∷ 2 ∷ [])
             ∷ (5 ∷ 3 ∷ 4 ∷ 1 ∷ 2 ∷ []) ↦ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
             ∷ [] ))
_ = refl

_ : passes (run msortP at
             ( (5 ∷ 3 ∷ 4 ∷ 1 ∷ 2 ∷ []) ↦ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
             ∷ (2 ∷ 2 ∷ 1 ∷ [])         ↦ (1 ∷ 2 ∷ 2 ∷ [])
             ∷ [] ))
_ = refl

-- `bagCase` is itself a map out of `⊤`, so the same interface reads it.
empty? : ⊤G ⊢ Δ Bool
empty? = okA ⌈ [] ⌉ NonTrivial ∘g bagCase

-- the element `bagCase` chose, read out by the generic `tagA`
someElem : ⊤G ⊢ Δ (Maybe ℕ)
someElem = caseA (pureA (Maybe ℕ) nothing) (mapA just (tagA ℕ)) ∘g bagCase

_ : passes (run empty? at ([] ↦ true ∷ (3 ∷ []) ↦ false ∷ []))
_ = refl

_ : passes (run someElem at ([] ↦ nothing ∷ (3 ∷ 1 ∷ []) ↦ just 3 ∷ []))
_ = refl

-- The `↦ false` above is not the whole content of that case: the error
-- grammar is a POSITIVE complement, so `refute` turns the same `refl`
-- into the decomposition itself.
notEmpty : (m : Bag) → run empty? m ≡ false → NonTrivial m
notEmpty = refute ⌈ [] ⌉ NonTrivial bagCase

nonTrivial-3 : NonTrivial (3 ∷ [])
nonTrivial-3 = notEmpty (3 ∷ []) refl

-- The FULLY intrinsic sorters: sorted permutation by TYPE, so these
-- `passes` checks confirm that it computes, not that it is correct.

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

-- AUTOMATA: same generic `Automaton`/`Scanner`/`runAut` as the string
-- instance.  Both algebras below are commutative, which is what makes
-- the answer independent of the order `bagCase` pulls elements out in.

module Sum  = Fold ℕ 0 _+_
module Size = Fold ℕ 0 (λ _ n → suc n)

-- both folds are terms `⊤G ⊢ Δ ℕ`, observed by `run` and nothing else
_ : passes (run Sum.foldA at ((3 ∷ 1 ∷ 2 ∷ []) ↦ 6 ∷ [] ↦ 0 ∷ []))
_ = refl

_ : passes (run Size.foldA at ((3 ∷ 1 ∷ 2 ∷ []) ↦ 3 ∷ []))
_ = refl
