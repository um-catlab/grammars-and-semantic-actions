{- The simply-typed instance: a THREE-sorted theory (`nm`, `tm`, `ty`) over
   the `TheoryGrammar` calculus, with a bidirectional typechecker. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.SimplyTyped where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary.Base using (Discrete)

open import TheoryGrammar.Instances.SimplyTyped.Signature  public
open import TheoryGrammar.Instances.SimplyTyped.Fibered  public
open import TheoryGrammar.Instances.SimplyTyped.Base
open import TheoryGrammar.Instances.SimplyTyped.Grading
open import TheoryGrammar.Instances.SimplyTyped.Readable
open import TheoryGrammar.Instances.SimplyTyped.Types
open import TheoryGrammar.Instances.SimplyTyped.Context
open import TheoryGrammar.Instances.SimplyTyped.Dependent
open import TheoryGrammar.Instances.SimplyTyped.Judgments
open import TheoryGrammar.Instances.SimplyTyped.Unique
open import TheoryGrammar.Instances.SimplyTyped.Check

-- everything at one alphabet of names, in one open
module SimplyTyped (Name : Type₀) (_≟_ : Discrete Name) where
  open StBase      Name      public
  open Grading     Name      public
  open StReadable  Name      public
  open StTypes     Name      public
  open StContext   Name _≟_  public
  open StDependent Name      public
  open Judgments   Name _≟_  public
  open StUnique    Name _≟_  public
  open StCheck     Name _≟_  public
