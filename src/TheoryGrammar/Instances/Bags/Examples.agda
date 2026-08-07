{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Sorting at ℕ.  Four sorters -- quicksort and mergesort, each plain and
   intrinsically verified -- and every one of them is a term `⊤G ⊢ Δ Bag`
   observed by `run` inside a `passes` line.  The plain/verified split is
   in the ALGEBRA's carrier, never in how the program is read. -}
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

-- ==================================================================
-- Every sorter below is observed the same way, and it is the only way
-- available: the program is a TERM `⊤G ⊢ Δ Bag`, and `run` appears
-- exclusively inside a `passes` line.  Naming the sorters at `Bag →
-- Bag` -- which is what these tests used to do -- externalises them in
-- a definition, and then the permutation certificate has already been
-- thrown away before anything is observed.
--
-- `quicksortC`/`mergesortV` land in `SpecG`/`Bagged`, both of which are
-- `⊕ᴰ Bag (λ out m → Perm out m)`, so reading the output bag off them
-- is the generic `tagA` and the certificate survives right up to `run`.
-- ==================================================================

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

-- ... and the PLAIN sorters, whose algebras have the constant carrier
-- `λ _ → Bag`.  Same coalgebra, same answers, no certificate -- which
-- is the measurement `qalg`/`qalgV` was written to make.  They are
-- still terms `⊤G ⊢ Δ Bag`; what they lack is in the CARRIER, not in
-- how they are observed.
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

-- ==================================================================
-- `bagCase`, the view the sorters are built on, is itself a map out of
-- `⊤` -- a `Cover (⌈ [] ⌉ ⊕ ⊕ᴰ A …)`, i.e. a `Result` -- so it is read
-- by the same interface.  Its right branch is a `⊕ᴰ` over the element
-- pulled off, so `tagA` recovers that element.
-- ==================================================================

-- `NonTrivial` (from `Bags.Graded`) IS `⊕ᴰ ℕ (λ x → ⌈ x ∷ [] ⌉ ⊗' ⊤G)`,
-- and naming it that way is what lets `refute` below be stated.
empty? : ⊤G ⊢ Δ Bool
empty? = okA ⌈ [] ⌉ NonTrivial ∘g bagCase

-- the element `bagCase` chose, read out by the generic `tagA`
someElem : ⊤G ⊢ Δ (Maybe ℕ)
someElem = caseA (pureA (Maybe ℕ) nothing) (mapA just (tagA ℕ)) ∘g bagCase

_ : passes (run empty? at ([] ↦ true ∷ (3 ∷ []) ↦ false ∷ []))
_ = refl

_ : passes (run someElem at ([] ↦ nothing ∷ (3 ∷ 1 ∷ []) ↦ just 3 ∷ []))
_ = refl

-- ... and the `↦ false` above is not the whole content of that case.
-- `bagCase`'s error grammar is `NonTrivial`, a POSITIVE complement, so
-- the same `refl` that observes `false` hands back the decomposition --
-- `refute` is what turns the observation into the branch content, and
-- it is uniform in the error grammar (`SemanticAction`).
notEmpty : (m : Bag) → run empty? m ≡ false → NonTrivial m
notEmpty = refute ⌈ [] ⌉ NonTrivial bagCase

nonTrivial-3 : NonTrivial (3 ∷ [])
nonTrivial-3 = notEmpty (3 ∷ []) refl

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

-- both folds are terms `⊤G ⊢ Δ ℕ`, observed by `run` and nothing else
_ : passes (run Sum.foldA at ((3 ∷ 1 ∷ 2 ∷ []) ↦ 6 ∷ [] ↦ 0 ∷ []))
_ = refl

_ : passes (run Size.foldA at ((3 ∷ 1 ∷ 2 ∷ []) ↦ 3 ∷ []))
_ = refl
