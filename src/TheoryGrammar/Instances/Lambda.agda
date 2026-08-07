{-
  The lambda instance: a two-sorted theory (`nm`, `tm`).  This module is
  only the index; each piece lives in `Instances/Lambda/`.

    Signature   two sorts, three operations, mixed-sort arity
    Fibered     raw terms; splittings as output-indexed data
    Base        the connectives, and the generic combinator layer
    Residuals   one per (operation, slot)
    Adjunctions the tensor/residual adjunction, and what it costs
    Grading     every splitting is proper; the recursor that buys
    Readable    the `DecReadable` this instance owes `Decidable`
    Precision   ... and what that hypothesis is, in separation-logic terms
    Binder      Yoneda for the binder: the dependent lam tensor
    Scoped      well-scoped terms, as the generic μ
    DeBruijn    elaboration, as the generic fold
    ScopeCheck  the checker: ⊤ ⊢ &ᴰ Scope (λ Δ → Scoped Δ ⊕ ¬G Scoped Δ)

  `Lambda/Tests.agda` checks that the whole pipeline reduces.  `Initial`,
  `Modes/` and `Passes/` are deliberately NOT re-exported here: each
  re-instantiates the generic `Ind`, so opening them alongside `Scoped`
  would make `μ` and its rules ambiguous.

  HOW THINGS ARE NAMED here.  Two spellings coexist and they mean
  different things, so neither is a lapse:

    dec-X    the decision RULE for a former X   dec-⌈⌉ dec-In dec-lamᵈ
    X?       a named predicate, DECIDED         closed? scoped? isVar?
    X!       the same, OBSERVED into a `Δ`      closed! isOp! size!
    X-P      X has property P (stdlib)          Split-isProp var-β ⟜-η
    X⁻       the inverse of X                   ⟦Sc⟧⁻ lam-collapse⁻
    λX, λ-X  this instance's witness for a
             generic interface                  λSig λFib λDR λ-unsplit
    X-at     X, given the witness X quantifies
             over                               dec-lamᵈ-at
-}
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
