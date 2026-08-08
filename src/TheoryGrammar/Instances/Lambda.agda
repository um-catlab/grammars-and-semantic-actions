{- The lambda instance: a two-sorted theory (`nm`, `tm`). -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary.Base using (Discrete)

open import TheoryGrammar.Instances.Lambda.Signature  public
open import TheoryGrammar.Instances.Lambda.Fibered
open import TheoryGrammar.Instances.Lambda.Base
open import TheoryGrammar.Instances.Lambda.Residuals
open import TheoryGrammar.Instances.Lambda.Adjunctions
open import TheoryGrammar.Instances.Lambda.Grading
open import TheoryGrammar.Instances.Lambda.Readable
open import TheoryGrammar.Instances.Lambda.Precision
open import TheoryGrammar.Instances.Lambda.Binder
open import TheoryGrammar.Instances.Lambda.Scoped
open import TheoryGrammar.Instances.Lambda.DeBruijn
open import TheoryGrammar.Instances.Lambda.ScopeCheck

-- everything at one alphabet of names, in one open
module Lambda (Name : Type₀) (_≟_ : Discrete Name) where
  open LamBase    Name     public
  open Residuals   Name    public
  open Adjunctions Name    public
  open Grading    Name     public
  open Readable   Name     public
  open LamPrecision Name   public
  open Binder     Name     public
  open Wellscoped Name     public
  open DeBruijn   Name     public
  open ScopeCheck Name _≟_ public
