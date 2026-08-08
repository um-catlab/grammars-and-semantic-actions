{- INDEX for the PARTIALLY COMMUTATIVE MONOID (Mazurkiewicz traces): the
   free monoid on Σ modulo `ab = ba` at a symmetric irreflexive
   INDEPENDENCE relation `I`. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Traces where

-- The first eight are PARAMETERISED -- by the alphabet, and most of them
-- by the independence relation -- so they are imported rather than
-- opened: unapplied, their names would only shadow one another.
import TheoryGrammar.Instances.Traces.Shuffle
import TheoryGrammar.Instances.Traces.Base
import TheoryGrammar.Instances.Traces.Ordered
import TheoryGrammar.Instances.Traces.Commutative
import TheoryGrammar.Instances.Traces.Refinement
import TheoryGrammar.Instances.Traces.Enumeration
import TheoryGrammar.Instances.Traces.Decidable
import TheoryGrammar.Instances.Traces.Mode

-- ... and the two closed ones, which pick an alphabet and run.
open import TheoryGrammar.Instances.Traces.Examples
open import TheoryGrammar.Instances.Traces.ModeTests
