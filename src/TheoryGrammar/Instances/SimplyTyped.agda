{-
  The simply-typed instance: a THREE-sorted theory (`nm`, `tm`, `ty`)
  over the `TheoryGrammar` calculus, with a bidirectional typechecker.
  This module is only the index; each piece lives in
  `Instances/SimplyTyped/`.

    Signature   three sorts, six operations, two result sorts
    Fibered   raw annotated terms and simple types; splittings, and
                the `unsplit` law the representables need
    Base        the connectives, and the generic combinator layer
    Grading     every splitting is proper -- at BOTH result sorts
    Readable    the `DecReadable`, `⌈⌉`-iso and `⊗-merge` this owes
    Types       equality of types, decided by the tensor rule at `ty`
    Context     contexts as name grammars; `Look` and its uniqueness
    Dependent   the dependent lam/ann tensors and their decisions
    Judgments   `Infer`/`Check` as ONE μ with two nonterminals
    Unique      the subsingleton theorem, by the generic fold
    Check       the typechecker; `dec-at` takes uniqueness as an input

  `SimplyTyped/Tests.agda` checks that the whole pipeline reduces, and
  `SimplyTyped/Laws.agda` records which laws are `refl` and which need
  `funExt`.  Both import this module, so neither is re-exported here.
-}
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
