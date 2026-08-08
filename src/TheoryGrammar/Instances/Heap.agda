{- THE HEAP INSTANCE: THE CANONICAL PARTIAL COMMUTATIVE MONOID. -}
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
open import TheoryGrammar.Instances.Heap.Refinement
open import TheoryGrammar.Instances.Heap.Joint
open import TheoryGrammar.Instances.Heap.Hoare
open import TheoryGrammar.Instances.Heap.Array
open import TheoryGrammar.Instances.Heap.ArrayTests
open import TheoryGrammar.Instances.Heap.Tests

-- parameterised by the tape alphabet, so it cannot be opened here
import TheoryGrammar.Instances.Heap.WithInput
