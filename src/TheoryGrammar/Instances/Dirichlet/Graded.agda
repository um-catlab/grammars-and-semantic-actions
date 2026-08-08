{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- THE GRADING: deg n = n itself. This is the crux of the instance, and it
   is the place where multiplication is BETTER behaved than concatenation
   rather than worse. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Dirichlet.Graded where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded

open import TheoryGrammar.Instances.Dirichlet.Connectives public

-- Four facts about `_·_`.  This is the whole arithmetic of the file;
-- everything else is bookkeeping.

-- a factor never exceeds the product ...
mulLeL : (d e' : ℕ) → d ≤ d · suc e'
mulLeL d e' = subst (d ≤_) (·-comm (suc e') d) ≤SumLeft

mulLeR : (d' e : ℕ) → e ≤ suc d' · e
mulLeR d' e = ≤SumLeft

-- ... and is strictly smaller as soon as the cofactor is ≥ 2.
mulLtL : (d'' e'' : ℕ) → suc d'' < suc d'' · suc (suc e'')
mulLtL d'' e'' = subst (suc d'' <_) (·-comm (suc (suc e'')) (suc d'')) <SumLeft

mulLtR : (d'' e'' : ℕ) → suc e'' < suc (suc d'') · suc e''
mulLtR d'' e'' = <SumLeft

-- The same four, transported across `Times`.  `timesPath` is used here
-- and nowhere else: this is the single crossing of the barrier between
-- the `Fibered`'s inductive splittings and ordinary arithmetic.

degLeL : (d e n : ℕ₊) → Times (val d) (val e) (val n) → val d ≤ val n
degLeL d (zero , ())
degLeL d (suc e' , _) n t = subst (val d ≤_) (timesPath t) (mulLeL (val d) e')

degLeR : (d e n : ℕ₊) → Times (val d) (val e) (val n) → val e ≤ val n
degLeR (zero , ())
degLeR (suc d' , _) e n t = subst (val e ≤_) (timesPath t) (mulLeR d' (val e))

degLtL : (d e n : ℕ₊) → Times (val d) (val e) (val n) → 2 ≤ val e → val d < val n
degLtL (zero , ())
degLtL (suc d'' , _) (zero , ())
degLtL (suc d'' , _) (suc zero , _)        n t ge2 = E.rec (¬m<m ge2)
degLtL (suc d'' , _) (suc (suc e'') , _) n t ge2 =
  subst (suc d'' <_) (timesPath t) (mulLtL d'' e'')

degLtR : (d e n : ℕ₊) → Times (val d) (val e) (val n) → 2 ≤ val d → val e < val n
degLtR (zero , ())
degLtR (suc zero , _)        e n t ge2 = E.rec (¬m<m ge2)
degLtR (suc (suc d'') , _) (zero , ())
degLtR (suc (suc d'') , _) (suc e'' , _) n t ge2 =
  subst (suc e'' <_) (timesPath t) (mulLtR d'' e'')

-- THE RESOURCE PREDICATE, internally.  `n` is a non-unit when it
-- decomposes with a factor ≥ 2 on the left.  Nothing about the ordering
-- of ℕ appears in the statement; it is ⊕ᴰ, ⌈_⌉, ⊗ and ⊤ only.

NonUnit : Gr
NonUnit = ⊕ᴰ ℕ (λ k → ⌈ 2+ k ⌉ ⊗' ⊤')

-- PRIMITIVE (phase 1).  The ONE bridge from the internal predicate to
-- the grading, confined to the file where the grading is defined.
nuGe2 : {n : ℕ₊} → NonUnit n → 2 ≤ val n
nuGe2 {n} (k , (d , e , t) , h) = go (h true) t
  where
    go : d Eq.≡ 2+ k → Times (val d) (val e) (val n) → 2 ≤ val n
    go Eq.refl t' = ≤-trans (suc-≤-suc (suc-≤-suc zero-≤)) (degLeL (2+ k) e n t')

-- ... and its converse, which is what a guardedness proof needs: a
-- number that is ≥ 2 is a non-unit, witnessed by n = n · 1.
ge2NU : (p : ℕ₊) → 2 ≤ val p → NonUnit p
ge2NU (zero , ())
ge2NU (suc zero , _)        ge = E.rec (¬m<m ge)
ge2NU (suc (suc k) , _) _ = k , ⊗-mk (2+ k) one₊ (times1R (suc (suc k))) Eq.refl tt

-- The graded `Fibered`.

DirProper : (o : DirOp) (n : ℕ₊) → DirSplit o n → DirAr o → Type₀
DirProper oneop n sp ()
DirProper mulop n (d , e , _) b = NonUnit (if b then e else d)

dirGraded : GradedFib dirSig ℓ-zero ℓ-zero
dirGraded .fib    = dirFib
dirGraded .deg _  = val
dirGraded .Proper = DirProper
dirGraded .deg≤ oneop n sp ()
dirGraded .deg≤ mulop n (d , e , t) true  = degLeL d e n t
dirGraded .deg≤ mulop n (d , e , t) false = degLeR d e n t
dirGraded .deg< oneop n sp ()
dirGraded .deg< mulop n (d , e , t) true  pr = degLtL d e n t (nuGe2 pr)
dirGraded .deg< mulop n (d , e , t) false pr = degLtR d e n t (nuGe2 pr)

-- Nonterminals are indexed by ℕ -- the least prime a factorisation may
-- still use.  See Factorization.
open Guard dirGraded ℓ-zero ℕ (λ _ → tt) public
