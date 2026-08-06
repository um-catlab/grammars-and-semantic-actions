{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Quicksort's functor and its guardedness.  The two recursive slots are
   discharged differently: `lo` shrinks because its complement holds the
   pivot, `hi` because the pivot sits inside its own factor. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Bags.QuicksortFunctor (A : Type₀) where

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

open import TheoryGrammar.Instances.Bags.Order A public

-- The description is parameterised by the order, because its SLOTS
-- carry the pivot bounds: the `lo` slot is "a recursive subproblem AND
-- a proof that it lies below the pivot".  That is the whole redesign --
-- the ordering facts `partition` discovers are exactly the facts the
-- algebra needs, so they travel in the shape rather than being
-- rediscovered afterwards.
module QSF (le : A → A → Bool)
           (leTrans : (x y z : A) → le x y Eq.≡ true → le y z Eq.≡ true
                    → le x z Eq.≡ true)
           where

  open Ord le leTrans public

  -- `Var & ⌜bound⌝`, as a two-slot conjunction
  QLo : A → Bool → Functor tt
  QLo piv true  = Var tt
  QLo piv false = ⌜ Above piv ⌝

  QHi : A → Bool → Functor tt
  QHi piv true  = Var tt
  QHi piv false = ⌜ Below piv ⌝

  QG' : A → Bool → Functor tt
  QG' piv true  = ⌜ ⌈ piv ∷ [] ⌉ ⌝
  QG' piv false = &e Bool (QHi piv)

  QG : A → Bool → Functor tt
  QG piv true  = &e Bool (QLo piv)
  QG piv false = ⊗e appop (QG' piv)

  QAlt : Bool → Functor tt
  QAlt true  = ⌜ ⌈ [] ⌉ ⌝
  QAlt false = ⊕e A (λ piv → ⊗e appop (QG piv))

  QF : Unit → Functor tt
  QF _ = ⊕e Bool QAlt

  -- a bounded slot is still non-growing: the bound contributes no
  -- positions, so the conjunction descends exactly as `Var` did
  ≤QLo : (piv : A) → Guarded≤ (&e Bool (QLo piv))
  ≤QLo piv = ≤&e Bool _ λ { true → ≤Var tt ; false → ≤⌜⌝ _ }

  ≤QHi : (piv : A) → Guarded≤ (&e Bool (QHi piv))
  ≤QHi piv = ≤&e Bool _ λ { true → ≤Var tt ; false → ≤⌜⌝ _ }

  -- the pivot witnesses that the right factor is non-trivial -- and the
  -- witness IS the resource predicate, not a fact about length
  restNonEmpty : (piv : A) (rest : Bag)
               → Sh (⊗e appop (QG' piv)) rest → NonTrivial rest
  restNonEmpty piv rest ((p1 , hi , ilv) , sh') with lower (sh' true)
  ... | Eq.refl = piv , ⊗-mk ilv Eq.refl tt

  innerGuarded : (piv : A) → Guarded (⊗e appop (QG' piv))
  innerGuarded piv = ⊗-guard appop (QG' piv) go
    where
      go : (v : Bag) (sp' : MonSplit appop v)
           (sh' : (a : Bool) → Sh (QG' piv a) (MonParts appop v sp' a))
           (a : Bool) (p : Pos (QG' piv a) _ (sh' a))
         → degIx (nx (QG' piv a) _ (sh' a) p) < length v
      go v sp' sh' true ()
      go v (p1 , hi , ilv) sh' false p with lower (sh' true)
      ... | Eq.refl =
        slotProper appop v (p1 , hi , ilv) false (≤QHi piv)
                   (piv , ⊗-mk (left nil) Eq.refl tt) (sh' false) p

  qfGuarded : (x : Unit) → Guarded (QF x)
  qfGuarded tt = <⊕e Bool _ alt
    where
      go : (piv : A) (m : Bag) (sp : MonSplit appop m)
           (sh : (a : Bool) → Sh (QG piv a) (MonParts appop m sp a))
           (a : Bool) (p : Pos (QG piv a) _ (sh a))
         → degIx (nx (QG piv a) _ (sh a) p) < length m
      go piv m (lo , rest , ilv) sh true p =
        slotProper appop m (lo , rest , ilv) true (≤QLo piv)
                   (restNonEmpty piv rest (sh false)) (sh true) p
      go piv m sp sh false p =
        slotGuarded appop m sp false (innerGuarded piv) (sh false) p

      alt : (b : Bool) → Guarded (QAlt b)
      alt true  = <⌜⌝ ⌈ [] ⌉
      alt false = <⊕e A _ (λ piv → ⊗-guard appop (QG piv) (go piv))

-- QUICKSORT, as a hylomorphism.  The coalgebra partitions, the
-- algebra concatenates, and `hylo` (TheoryGrammar.Graded) supplies the
-- recursion from `qfGuarded` alone.  No `with`, no explicit
-- well-founded recursion at the use site: the termination certificate
-- IS the guardedness of the description.
