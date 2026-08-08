{- Optimisation passes over the lambda AST. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Passes.All where

open import TheoryGrammar.Instances.Lambda.Passes.Framework public
open import TheoryGrammar.Instances.Lambda.Passes.Decide    public
open import TheoryGrammar.Instances.Lambda.Passes.Eta       public
open import TheoryGrammar.Instances.Lambda.Passes.Dead      public
open import TheoryGrammar.Instances.Lambda.Passes.Inline    public
open import TheoryGrammar.Instances.Lambda.Passes.Affine    public
open import TheoryGrammar.Instances.Lambda.Passes.Rename    public
open import TheoryGrammar.Instances.Lambda.Passes.Tests
