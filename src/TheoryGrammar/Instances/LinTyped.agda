{- The LINEARLY typed instance: a THREE-sorted theory (`nm`, `tm`, `ty`)
   over the `TheoryGrammar` calculus, with a bidirectional typechecker. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.LinTyped where

open import TheoryGrammar.Instances.LinTyped.Signature  public
open import TheoryGrammar.Instances.LinTyped.Fibered    public
open import TheoryGrammar.Instances.LinTyped.Base       public
open import TheoryGrammar.Instances.LinTyped.Grading    public
open import TheoryGrammar.Instances.LinTyped.Readable   public
open import TheoryGrammar.Instances.LinTyped.Types      public
open import TheoryGrammar.Instances.LinTyped.Context    public
open import TheoryGrammar.Instances.LinTyped.Judgments  public
open import TheoryGrammar.Instances.LinTyped.Unique     public
open import TheoryGrammar.Instances.LinTyped.Check      public
