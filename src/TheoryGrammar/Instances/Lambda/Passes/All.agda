{-
  Optimisation passes over the lambda AST.  Index module.

  The headline is NEGATIVE, and it is stated in `Framework`: the output
  type `Out Γ = ⊕ᴰ Raw (λ t _ → Scoped Γ t)` is constant in the index, so
  the mergesort-style freebie -- "`⊢` preserves the index, so a pass can
  only rearrange" -- does not apply here.  `Rename` locates the one
  exception: the only pass free by transport is the identity.

    Framework  what a pass IS, the rebuilding rules, `runPass` (the
               generic `fold`), and `tryEmit` (the shared scope move,
               which CARRIES the derivation its decision produces)
    Decide     the two internal decisions a rewriting pass needs
    Eta        PASS 1: η-contraction        (rewrites `lamOp`)
    Dead       PASS 2: dead-binding elim    (rewrites `appOp`)
    Inline     PASS 3: substitution         (rewrites `varOp`) --
               additively free, multiplicatively failing at `varOp`
               alone, in both directions
    Affine     what `A ⊗ B ⊢ A` costs: a carrier map that neither
               preserves nor reflects splittings
    Rename     the free case, and how small it is
    Tests      every pass computes on closed terms

  The generic half is `TheoryGrammar.CarrierMap`.
-}
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
