{-
  THE HEAP INSTANCE: THE CANONICAL PARTIAL COMMUTATIVE MONOID.

  `Field` shows a partiality located at a SLOT -- one bad element, `inv`
  at zero.  A heap shows the other shape, the one every PCM has: no
  element is bad, only certain PAIRS are, because joining requires
  disjoint domains.  That is the case `Fibered`'s header names, and it
  is what the split from `LaxPoint` was for.

    Base         `Loc`/`Val`/`Cell`, `Diff`/`Fresh`/`_#_`, `Ilv`,
                 `heapFib` -- and `cellFib`/`cellPoint`, the SAME
                 promodel with the `u # v` conjunct deleted
    Connectives  `∗ = ⊗ˢ appop`, `emp = ⊗ˢ nilop`, `─∗ = ⊸ᶠ` at
                 `heapFocus`, the frame rule, `apart-self`, and
                 `noHeapPoint : LaxPoint heapFib → ⊥`
    Linear       a points-to cannot be duplicated
    Graded       the degree is the cell count, so `μ`/`löb` survive
    Emp          `emp` is the representable `⌈ [] ⌉`; unit laws,
                 commutativity, `_↦_`
    Adjunction   BI's `(P ∗ Q ⊢ R) ≅ (Q ⊢ P ─∗ R)`, and WHERE THE
                 FRAMEWORK'S TWO UNIVERSAL PROPERTIES STOP SHORT
    Located      the obstruction, twice localised, and the proof that
                 `Domˢ`/`Imgˢ` cannot see it
    Precise      non-duplication for every pinning, nonempty predicate
    Precision    separation-logic precision vs `splitProp`
    Tests        `refl` at two-cell heaps

  THE TWO MEASUREMENTS, since neither is guessable:

    `⊸ᶠ` at `heapFocus` IS the textbook wand -- `Adjunction.wandIso`,
    both round trips `refl`.  But `⊗ˢ-UP` and `⊸ᶠ-UP` classify
    `MultiHomˢ` and `FocusedHom`, which are DIFFERENT hom-sets, so BI's
    adjunction is their composite only through `refocus`.  Measured:
    `∗-η` is `refl`, `∗-β` costs exactly one `funExt`, and the cause is
    that `MonAr appop = Bool` is `data` and so has no η.

    The partiality is JOINT, so `Domain.no-point` is inapplicable --
    `Located.no-slotwise-L/R` prove no refutation of its shape exists.
    `Connectives.Generic.no-tuple-point` is the form that works: a
    tensor of REPRESENTABLES rather than of `⊤`.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Heap where

open import TheoryGrammar.Instances.Heap.Base
open import TheoryGrammar.Instances.Heap.Connectives
open import TheoryGrammar.Instances.Heap.Linear
open import TheoryGrammar.Instances.Heap.Graded
open import TheoryGrammar.Instances.Heap.Emp
open import TheoryGrammar.Instances.Heap.Adjunction
open import TheoryGrammar.Instances.Heap.Located
open import TheoryGrammar.Instances.Heap.Precise
open import TheoryGrammar.Instances.Heap.Precision
open import TheoryGrammar.Instances.Heap.Tests
