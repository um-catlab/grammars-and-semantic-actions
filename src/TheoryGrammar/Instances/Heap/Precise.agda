{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  NON-DUPLICATION FOR EVERY PRECISE, NONEMPTY PREDICATE.

  `apart-self` says a single points-to cannot be duplicated.  That is the
  singleton case of a textbook separation-logic fact, and the general one
  needs exactly the modality this development already has a name for:

      Pins A   =   A u → A v → u ≡ v        ("A pins its heap")

  which is the `pin` half of `Ring/Distributivity`'s `Precise`.  The
  convergence is worth stating, because the two uses look unrelated and
  are not.  There, precision was what REPAIRED a non-linear law: `distrib`
  is invertible exactly on precise arguments.  Here it is what makes a
  predicate NON-DUPLICABLE.  Both are the same condition -- "A is
  subterminal in the slice over its index" -- read once covariantly and
  once contravariantly.

  Only the `pin` half is needed here, so only that half is assumed;
  `Precise`'s `single` field (an `isProp` on the payload) is not used.
  And `Pins` mentions nothing about heaps -- it is generic in the carrier,
  which is the case for lifting BOTH it and `Precise` into the core.
  Recorded as an upstream item rather than acted on, since `Precise`
  currently lives in an instance directory.

  THE SHAPE OF THE ARGUMENT.  `A ∗ A` at `h` gives a disjoint split
  `u`,`v` with `A u` and `A v`; `Pins` collapses them to one heap; and a
  heap is never disjoint from itself unless it is empty.  So a precise
  predicate that owns anything cannot be duplicated.
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Heap.Precise where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Empty as E using (⊥; ⊥*)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib

open import TheoryGrammar.Instances.Heap.Linear public

-- ==================================================================
-- Precision, and nonemptiness.
-- ==================================================================

-- The `pin` half of `Ring/Distributivity`'s `Precise`.  Generic in the
-- carrier; BELONGS UPSTREAM together with that record.
Pins : Gr → Type₀
Pins A = {u v : Heap} → A u → A v → u ≡ v

-- PRIMITIVE (phase 1): recursive predicate, as `IsNil` is.
NonEmp : Gr
NonEmp []      = ⊥
NonEmp (_ ∷ _) = Unit

-- PRIMITIVE (phase 1): a heap is apart from itself only if empty.
-- `#-self` in `Base` is this at a singleton; the general case is the
-- same one line, because `((l , x) ∷ t) # ((l , x) ∷ t)` unfolds to a
-- product whose first component is `Diff l l`.
#-irrefl : (u : Heap) → NonEmp u → u # u → ⊥
#-irrefl []            ne d             = ne
#-irrefl ((l , _) ∷ _) _  ((dll , _) , _) = diff-irrefl l dll

-- ==================================================================
-- THE THEOREM.  Internal: `⊗ˢ-E` supplies the split, `Pins` collapses
-- it, `#-Eq` transports disjointness onto the diagonal, `#-irrefl`
-- refutes it.  Nothing is matched here.
-- ==================================================================

precise-no-dup : (A : Gr) → Pins A → (A ⊢ NonEmp) → (A ∗ A) ⊢ ⊥G
precise-no-dup A pins ne =
  ⊗ˢ-E appop {A = boolΠ A A}
    (λ h sp k →
       E.rec (#-irrefl _ (ne _ (k true))
                (#-Eq Eq.refl
                      (Eq.pathToEq (sym (pins (k true) (k false))))
                      (split-# h sp))))

-- ==================================================================
-- ... and `apart-self` is the singleton instance of it.
-- ==================================================================

-- PRIMITIVE (phase 1): a representable pins its heap -- the Yoneda fact,
-- at `Eq`.
⌈⌉Pins : (s : Heap) → Pins ⌈ s ⌉
⌈⌉Pins s Eq.refl Eq.refl = refl

-- PRIMITIVE (phase 1): a singleton heap is nonempty.
singleNonEmp : (l : Loc) (x : Val) → ⌈ single l x ⌉ ⊢ NonEmp
singleNonEmp l x _ Eq.refl = tt

-- THEOREM (phase 2): the toy result, recovered as a corollary.
apart-self' : (l : Loc) (x : Val)
            → (⌈ single l x ⌉ ∗ ⌈ single l x ⌉) ⊢ ⊥G
apart-self' l x =
  precise-no-dup ⌈ single l x ⌉ (⌈⌉Pins (single l x)) (singleNonEmp l x)

-- ... and therefore the whole no-point argument runs off the general
-- theorem too: `noHeapPoint` used `apart-self`, and this is the same
-- statement, so nothing downstream has to change.
