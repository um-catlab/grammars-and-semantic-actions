{-
  Optimisation passes over the lambda AST, and what the calculus gives
  a pass for free.  Index module.

    Framework  what a pass IS: `Out Γ = ⊕ᴰ Raw (Scoped Γ)`, the
               rebuilding rules, and `runPass` (the generic `fold`)
    Decide     the two internal decisions a rewriting pass needs
    Eta        PASS 1: η-contraction        (rewrites `lamOp`)
    Dead       PASS 2: dead-binding elim    (rewrites `appOp`)
    Inline     PASS 3: substitution         (rewrites `varOp`) --
               the NEGATIVE result: additively free, multiplicatively
               it neither preserves nor reflects splittings
    Affine     what `A ⊗ B ⊢ A` costs: a carrier map, and a proof that
               that carrier map is not split-preserving
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
