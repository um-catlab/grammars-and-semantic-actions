{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  REGRESSION TESTS FOR THE RESULTS `Tests.agda` DOES NOT COVER.

  `Tests.agda` exercises the connectives and precision at concrete heaps.
  This file covers the four things added since, which are theorems rather
  than computations and would therefore break SILENTLY:

    1. the guarded `μ` actually builds and unrolls  (`Array`)
    2. `NonEmp` is load-bearing in `precise-no-dup`  (`emp` IS duplicable)
    3. `no-dup` and `cell-no-apart` still typecheck at concrete arguments
    4. the heap/cell contrast is still a contrast

  For (1) the test is a round trip: build `Array 0 2` with the surface
  constructors, unroll it, and check by `refl` that the cell comes back.
  That is the check most likely to break under a change to `arrF` or to
  `heapGrading`, and it is the one nothing else makes.
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Heap.ArrayTests where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib

open import TheoryGrammar.SemanticAction using (Case; passes; _↦_; _at_)

open import TheoryGrammar.Instances.Heap.Array public

-- ==================================================================
-- 1.  THE GUARDED μ BUILDS, AND UNROLLS BACK.
-- ==================================================================

private
  c0 c1 : Heap
  c0 = single 0 v0
  c1 = single 1 v1

  hh : Heap
  hh = (0 , v0) ∷ (1 , v1) ∷ []

  -- `Array 2 0` at the empty heap: the `emp` base case.
  a0 : Array 2 0 []
  a0 = array-nil 2 [] (tt , λ ())

  -- `Array 1 1` at the one-cell heap `c1`, split as `c1 ⊎ []`.
  a1 : Array 1 1 c1
  a1 = array-cons 1 0 c1
         ( ⊗ˢ-I appop {A = boolΠ {M = λ _ → Gr} (Cellv 1) (Array 2 0)} c1
             (c1 , [] , ilv-nilR c1 , #-nil c1)
             (boolΠ {M = λ a → boolΠ {M = λ _ → Gr} (Cellv 1) (Array 2 0) a
                                 (heapFib .parts appop c1
                                    (c1 , [] , ilv-nilR c1 , #-nil c1) a)}
                    (v1 , Eq.refl) a0) )

  -- ... and `Array 0 2` at `hh`, split as `c0 ⊎ c1`.
  a2 : Array 0 2 hh
  a2 = array-cons 0 1 hh
         ( ⊗ˢ-I appop {A = boolΠ {M = λ _ → Gr} (Cellv 0) (Array 1 1)} hh
             (c0 , c1 , ilv-app c0 c1 , ((tt , tt) , tt))
             (boolΠ {M = λ a → boolΠ {M = λ _ → Gr} (Cellv 0) (Array 1 1) a
                                 (heapFib .parts appop hh
                                    (c0 , c1 , ilv-app c0 c1 , ((tt , tt) , tt)) a)}
                    (v0 , Eq.refl) a1) )

  -- THE ROUND TRIP, as a suite: the term under test is written ONCE and
  -- the cases are the two slots.  One `refl` proves both.
  _ : passes ((λ b → heapFib .parts appop hh (array-unrollS 0 1 hh a2 .fst) b) at
               ( true  ↦ c0
               ∷ false ↦ c1
               ∷ [] ))
  _ = refl

-- ==================================================================
-- 2.  `NonEmp` IS LOAD-BEARING.
--
-- `emp` is precise -- it pins the heap to `[]` -- so if `precise-no-dup`
-- needed only precision it would refute `emp ∗ emp`.  It does not, and
-- here is the witness: the empty heap splits as `[] ⊎ []`, disjointly.
-- So the `A ⊢ NonEmp` hypothesis is exactly what excludes the unit, and
-- is not decoration.
-- ==================================================================

private
  empPins : Pins emp
  empPins {[]} {[]} _ _ = refl

  emp-dup : (emp ∗ emp) []
  emp-dup =
    ⊗ˢ-I appop {A = boolΠ {M = λ _ → Gr} emp emp} []
      ([] , [] , nil , tt)
      (boolΠ {M = λ a → boolΠ {M = λ _ → Gr} emp emp a
                          (heapFib .parts appop [] ([] , [] , nil , tt) a)}
             (tt , λ ()) (tt , λ ()))

-- ==================================================================
-- 3.  THE REFUTATIONS STILL APPLY.  Typechecking IS the test: these are
-- metatheorems, so instantiating them at concrete arguments is all the
-- coverage there is.
-- ==================================================================

private
  _ : (⌈ single 0 v0 ⌉ ⊢ (⌈ single 0 v0 ⌉ ∗ ⌈ single 0 v0 ⌉)) → ⊥
  _ = no-dup 0 v0

  _ : LaxPoint heapFib → ⊥
  _ = noHeapPoint

  -- ... and the general theorem specialises to the singleton one
  _ : (⌈ single 0 v0 ⌉ ∗ ⌈ single 0 v0 ⌉) ⊢ ⊥G
  _ = apart-self' 0 v0

-- ==================================================================
-- 4.  THE CONTRAST IS STILL A CONTRAST.  Same carrier, same `parts`,
-- same `Ilv`; one conjunct apart.  Heaps refute the separation
-- statement's negation; cells refute the separation statement itself.
-- ==================================================================

private
  _ : ((C.⌈ single 0 v0 ⌉ ∗c C.⌈ single 0 v0 ⌉) C.⊢ C.⊥G) → ⊥
  _ = cell-no-apart 0 v0
