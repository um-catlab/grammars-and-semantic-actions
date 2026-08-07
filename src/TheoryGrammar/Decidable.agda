{-
  Decidability, internally and generic in the theory.  Index module.

    Additive     needs only a `Model`: `¬G`, `Dec⟨_⟩`, complements,
                 `dist&`, `deMorgan`, closure under `⊕`, `&`, `⊤`, `⊥`
    Listable     the INDEXED additives, `dec-⊕ᴰ` / `dec-&ᴰ`, which need
                 the tag type listable -- what makes a decision over a
                 description (`Inductive.Functor`) a `⊢`-composite
    Tensor       `⊗-miss`, `⊗-refute`, and `dec-⊗` from unique readability
    Splittings   the INTERFACE `DecSplittings`, with two routes into it:
                 `fromReadable` (unique readability) and `fromEnumerable`
                 (the splittings are listable -- what resource promodels
                 need, since `splitProp` is false for them)
    Representable `dec-⌈⌉`, decidability of a representable

  A decision is a map `⊤ ⊢ A ⊕ A'` plus `(A & A') ⊢ ⊥`, never a
  metalanguage `Dec`.

  `Decidable/{Enumerated,Guarded,Rule}` are NOT re-exported here, and
  cannot be as things stand: `Rule.fromEnumerable` would collide with
  `Splittings.fromEnumerable` (they are the same theorem twice -- see
  `Splittings`), and instances routinely shadow `Enumerated.enumSplit`.
-}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Decidable where

open import TheoryGrammar.Decidable.Additive     public
open import TheoryGrammar.Decidable.Listable     public
open import TheoryGrammar.Decidable.Tensor       public
open import TheoryGrammar.Decidable.Splittings   public
open import TheoryGrammar.Decidable.Representable public
