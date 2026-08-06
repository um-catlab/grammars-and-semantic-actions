{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE GRADING: deg n = n itself.

  This is the crux of the instance, and it is the place where
  multiplication is BETTER behaved than concatenation rather than worse.

  For strings the degree is `length`, a map OUT of the carrier into a
  separate well-founded order; the connection between the two has to be
  maintained by hand (`split3LenL`, `split3LenR`, ...).  Here the carrier
  already IS the order.  `deg n = n`, and the framework's Löb recursion
  over `_≺_` -- "strictly smaller degree" -- restricted along the
  splittings of the substrate, is exactly

      strong induction on the DIVISORS of n.

  So a `hyloC` at this substrate is precisely a recursion allowed to call
  itself at any proper divisor, and nothing had to be invented to say so:
  `GradedSubstrate` asks for `deg≤` and `deg<`, which unfold to the two
  facts

      d · e = n , e ≥ 1  ⟹  d ≤ n
      d · e = n , e ≥ 2  ⟹  d < n

  and their mirror images.  That is the entire arithmetic content of the
  file.  Note where positivity is used: `deg≤` needs the OTHER factor to
  be ≥ 1, which is exactly the carrier's standing hypothesis, and `deg<`
  needs it ≥ 2, which is `Proper`.  If 0 were in the carrier both would
  be false at n = 0.

  ------------------------------------------------------------------
  PROPERNESS, internally.
  ------------------------------------------------------------------

  As everywhere else in this development, a slot is proper when its
  COMPLEMENT is non-trivial, and non-triviality is stated in the calculus
  rather than in the metalanguage:

      NonTrivial w  =  ⊕ᴰ[ c : Char ] ⌈ c ⌉    ⊗ ⊤      (w contains a letter)
      NonUnit    n  =  ⊕ᴰ[ k : ℕ    ] ⌈ k + 2 ⌉ ⊗ ⊤     (n has a factor ≥ 2)

  Both are `⊕ᴰ`, `⌈_⌉`, `⊗` and `⊤` only, so both make sense at any
  substrate with atoms; the index type is the type of atoms, which for
  strings is `Char` and here is "the numbers ≥ 2", presented proof-free
  as ℕ via `2+_`.  Exactly one primitive, `nuGe2`, bridges the internal
  predicate to the grading, and it is confined to this file.

  Observe what `NonUnit` does NOT say: nothing about primality.  Any
  factor ≥ 2 forces n ≥ 2, which is all a grading can want.  Primality is
  a property of a GRAMMAR -- it is what makes the factorisation grammar
  in `Factorization.agda` unambiguous -- and not of the substrate.  The
  substrate is happy with any well-founded notion of "proper divisor".

  ------------------------------------------------------------------
  Downstream, `Guard` is opened at X = ℕ, i.e. nonterminals of the
  generic `μ` are indexed by a NUMBER.  That number is the lower bound
  on the primes a factorisation is allowed to use; see Factorization.
-}
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
open import TheoryGrammar.Substrate
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded

open import TheoryGrammar.Instances.Dirichlet.Connectives public

-- ==================================================================
-- Four facts about `_·_`.  This is the whole arithmetic of the file;
-- everything else is bookkeeping.
-- ==================================================================

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

-- ==================================================================
-- The same four, transported across `Times`.  `timesPath` is used here
-- and nowhere else: this is the single crossing of the barrier between
-- the substrate's inductive splittings and ordinary arithmetic.
-- ==================================================================

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

-- ==================================================================
-- THE RESOURCE PREDICATE, internally.  `n` is a non-unit when it
-- decomposes with a factor ≥ 2 on the left.  Nothing about the ordering
-- of ℕ appears in the statement; it is ⊕ᴰ, ⌈_⌉, ⊗ and ⊤ only.
-- ==================================================================

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

-- ==================================================================
-- The graded substrate.
-- ==================================================================

DirProper : (o : DirOp) (n : ℕ₊) → DirSplit o n → DirAr o → Type₀
DirProper oneop n sp ()
DirProper mulop n (d , e , _) b = NonUnit (if b then e else d)

dirGraded : GradedSubstrate dirSig ℓ-zero ℓ-zero
dirGraded .sub    = dirSub
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
