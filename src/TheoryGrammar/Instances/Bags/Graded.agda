{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The grading: deg = length, a slot is proper when its complement is nonempty. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Bags.Graded (A : Type₀) where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.List
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded

open import TheoryGrammar.Instances.Bags.Commutativity A public

ilvLenL : ∀ {u v w} → Ilv u v w → length u ≤ length w
ilvLenL nil       = ≤-refl
ilvLenL (left s)  = suc-≤-suc (ilvLenL s)
ilvLenL (right s) = ≤-suc (ilvLenL s)

ilvLenR : ∀ {u v w} → Ilv u v w → length v ≤ length w
ilvLenR nil       = ≤-refl
ilvLenR (left s)  = ≤-suc (ilvLenR s)
ilvLenR (right s) = suc-≤-suc (ilvLenR s)

-- a nonempty COMPLEMENT makes the slot strictly smaller
ilvLenL< : ∀ {u v w} → Ilv u v w → 0 < length v → length u < length w
ilvLenL< nil       pr = E.rec (¬-<-zero pr)
ilvLenL< (left s)  pr = suc-≤-suc (ilvLenL< s pr)
ilvLenL< (right s) pr = suc-≤-suc (ilvLenL s)

ilvLenR< : ∀ {u v w} → Ilv u v w → 0 < length u → length v < length w
ilvLenR< nil       pr = E.rec (¬-<-zero pr)
ilvLenR< (left s)  pr = suc-≤-suc (ilvLenR s)
ilvLenR< (right s) pr = suc-≤-suc (ilvLenR< s pr)

-- The promodel.


-- THE RESOURCE PREDICATE, internally: `m` is non-trivial when it
-- decomposes with an ATOM on the left.  Built from `⌈_⌉`, `⊗`, `⊕ᴰ` and
-- `⊤` only -- no length -- so it makes sense at any promodel with atoms.
-- This is exactly what `bagCase` produces.
NonTrivial : Gr
NonTrivial = ⊕ᴰ A (λ x → ⌈ x ∷ [] ⌉ ⊗' ⊤G)

-- PRIMITIVE (phase 1).  The one bridge from the internal predicate to
-- the grading, confined to where the grading is defined.
ntLen : {v : Bag} → NonTrivial v → 0 < length v
ntLen {v} (x , (u , v' , ilv) , h) = go (h true) ilv
  where go : u Eq.≡ x ∷ [] → Ilv u v' v → 0 < length v
        go Eq.refl s = ilvLenL s

Proper' : (o : MonOp) (m : Bag) → MonSplit o m → MonAr o → Type₀
Proper' nilop m sp ()
Proper' appop m (u , v , _) b = NonTrivial (if b then v else u)

bagGraded : GradedFib monoidSig ℓ-zero ℓ-zero
bagGraded .fib    = bagFib
bagGraded .deg _  = length
bagGraded .Proper = Proper'
bagGraded .deg≤ nilop m sp ()
bagGraded .deg≤ appop m (u , v , s) true  = ilvLenL s
bagGraded .deg≤ appop m (u , v , s) false = ilvLenR s
bagGraded .deg< nilop m sp ()
bagGraded .deg< appop m (u , v , s) true  pr = ilvLenL< s (ntLen pr)
bagGraded .deg< appop m (u , v , s) false pr = ilvLenR< s (ntLen pr)

-- QUICKSORT'S FUNCTOR, and why its recursion is guarded.
--
--     H X b  =  (b is empty)  ⊕  Σ[piv] X lo ⊗ ⌈piv⌉ ⊗ X hi
--
-- The two recursive slots are discharged DIFFERENTLY, which is the
-- whole reason `⊗-guard` takes a per-slot certificate:
--
--   * `lo` shrinks because its COMPLEMENT (piv ∷ hi) is nonempty --
--     `slotProper`.  The pivot is the witness.
--   * `hi` does NOT shrink for that reason: its sibling `lo` may be
--     empty.  It shrinks because the pivot sits INSIDE its own factor,
--     so that factor is already guarded -- `slotGuarded`.
--
-- This is the agent's finding made mechanical: the decrease comes from
-- the pivot, not from the partition.  A bare `b = lo ⊎ hi` in a
-- commutative monoid does not decrease at all.

open Guard bagGraded ℓ-zero Unit (λ _ → tt) public
