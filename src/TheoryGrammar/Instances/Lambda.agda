{-
  The lambda instance: a two-sorted theory (`nm`, `tm`) over the
  `TheoryGrammar` calculus.  This module is only the index; each piece
  lives in `Instances/Lambda/`.

    Signature   two sorts, three operations, mixed-sort arity
    Substrate   raw terms; splittings as output-indexed data
    Base        the connectives, and the generic combinator layer
    Residuals   one per (operation, slot)
    Adjunctions the tensor/residual adjunction, and what it costs
    Grading     every splitting is proper; the recursor that buys
    Readable    the `DecReadable` this instance owes `Decidable`
    Binder      Yoneda for the binder: the dependent lam tensor
    Scoped      well-scoped terms, as the generic μ
    DeBruijn    elaboration, as the generic fold
    ScopeCheck  the checker: ⊤ ⊢ &ᴰ Scope (λ Δ → Scoped Δ ⊕ ¬G Scoped Δ)

  `Lambda/Tests.agda` checks that the whole pipeline reduces.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary.Base using (Discrete)

open import TheoryGrammar.Instances.Lambda.Signature  public
open import TheoryGrammar.Instances.Lambda.Substrate
open import TheoryGrammar.Instances.Lambda.Base
open import TheoryGrammar.Instances.Lambda.Residuals
open import TheoryGrammar.Instances.Lambda.Adjunctions
open import TheoryGrammar.Instances.Lambda.Grading
open import TheoryGrammar.Instances.Lambda.Readable
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
  open Binder     Name     public
  open Wellscoped Name     public
  open DeBruijn   Name     public
  open ScopeCheck Name _≟_ public
