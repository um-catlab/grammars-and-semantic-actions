{-
  Decidability, internally and generic in the theory.  Index module.

    Additive     needs only a `Model`: `¬G`, `Dec⟨_⟩`, complements,
                 `dist&`, `deMorgan`, closure under `⊕`, `&`, `⊤`, `⊥`
    Tensor       `⊗-miss`, `⊗-refute`, and `dec-⊗` from unique readability
    Splittings   the INTERFACE `DecSplittings`, with two routes into it:
                 `fromReadable` (unique readability) and `fromEnumerable`
                 (the splittings are listable -- what resource promodels
                 need, since `splitProp` is false for them)
    Representable  `dec-⌈⌉`, decidability of a representable

  A decision is a map `⊤ ⊢ A ⊕ A'` plus `(A & A') ⊢ ⊥`, never a
  metalanguage `Dec`.
-}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Decidable where

open import TheoryGrammar.Decidable.Additive     public
open import TheoryGrammar.Decidable.Tensor       public
open import TheoryGrammar.Decidable.Splittings   public
open import TheoryGrammar.Decidable.Representable public
