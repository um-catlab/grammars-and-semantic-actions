{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE GRADING AT (ℕ, +): deg = the identity.

  For strings the degree is `length`, and one has to prove that a
  splitting does not increase it.  Here the degree IS the carrier, so the
  three obligations of `GradedFib` degenerate to arithmetic on
  `Add3`:

      deg n   =  n
      deg≤    =  i ≤ n  and  j ≤ n  whenever  Add3 i j n
      deg<    =  the complementary slot being nonzero makes it strict

  which is worth saying out loud, because it is the reason `ℕ` is the
  RIGHT recipient of `length`: the string grading factors as

      String --length--> ℕ --deg=id--> ℕ

  so the well-founded order that drives `löb`/`hyloC` at strings is
  literally pulled back from the one here.  `Length.agda` upgrades that
  observation from "the degrees agree" to "the SPLITTINGS agree".

  As in `Strings/Graded.agda`, properness is stated INTERNALLY -- the
  complementary slot entails `NonTrivial`, a formula in `⌈_⌉`, `⊗` and
  `⊤` only -- and exactly one primitive (`ntDeg`) bridges that formula to
  the numeric order.  Since ℕ is the free monoid on ONE letter, the
  string instance's `⊕ᴰ Char (λ c → ⌈ c ∷ [] ⌉ ⊗ ⊤)` collapses to a
  single summand, `x ⊗' ⊤'`: "n is at least one".
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Nat.Graded where

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

open import TheoryGrammar.Instances.Nat.Connectives public

-- ==================================================================
-- Arithmetic of `Add3`.  The four lemmas of `Strings/Graded.agda`,
-- with `length` erased.
-- ==================================================================

add3L : ∀ {i j n} → Add3 i j n → i ≤ n
add3L z     = zero-≤
add3L (s a) = suc-≤-suc (add3L a)

add3R : ∀ {i j n} → Add3 i j n → j ≤ n
add3R z     = ≤-refl
add3R (s a) = ≤-suc (add3R a)

add3L< : ∀ {i j n} → Add3 i j n → 0 < j → i < n
add3L< z     pr = pr
add3L< (s a) pr = suc-≤-suc (add3L< a pr)

add3R< : ∀ {i j n} → Add3 i j n → 0 < i → j < n
add3R< z     pr = E.rec (¬-<-zero pr)
add3R< (s a) pr = suc-≤-suc (add3R a)

-- ==================================================================
-- THE RESOURCE PREDICATE, internally.  `n` is non-trivial when it
-- decomposes with the GENERATOR on the left.  Nothing about the numeric
-- order appears: this is `⌈_⌉`, `⊗` and `⊤` only.
-- ==================================================================

NonTrivial : Gr
NonTrivial = x ⊗' ⊤'

-- PRIMITIVE (phase 1).  The ONE bridge from the internal predicate to
-- the grading, confined to the file where the grading is defined.
ntDeg : {n : ℕ} → NonTrivial n → 0 < n
ntDeg {n} ((i , j , a) , h) = go (h true) a
  where go : i Eq.≡ 1 → Add3 i j n → 0 < n
        go Eq.refl a' = add3L a'

-- PRIMITIVE (phase 1): the converse, so that "0 < n" can be re-entered
-- into the calculus.  Used by `Species.agda` to certify guardedness of a
-- description whose left factor is the generator.
degNT : {n : ℕ} → n Eq.≡ 1 → NonTrivial n
degNT Eq.refl = ⊗-mk (s z) Eq.refl tt

NatProper : (o : MonOp) (n : ℕ) → MonSplit o n → MonAr o → Type₀
NatProper nilop n sp ()
NatProper appop n (i , j , _) b = NonTrivial (if b then j else i)

natGraded : GradedFib monoidSig ℓ-zero ℓ-zero
natGraded .fib    = natFib
natGraded .deg _  = λ n → n
natGraded .Proper = NatProper
natGraded .deg≤ nilop n sp ()
natGraded .deg≤ appop n (i , j , a) true  = add3L a
natGraded .deg≤ appop n (i , j , a) false = add3R a
natGraded .deg< nilop n sp ()
natGraded .deg< appop n (i , j , a) true  pr = add3L< a (ntDeg pr)
natGraded .deg< appop n (i , j , a) false pr = add3R< a (ntDeg pr)

open Guard natGraded ℓ-zero Unit (λ _ → tt) public
