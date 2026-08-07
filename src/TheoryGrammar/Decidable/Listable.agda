{-
  DECIDING THE INDEXED ADDITIVES.

  `dec-⊕` and `dec-&` (Decidable.Additive) are combinator composites and
  need no hypothesis, because a binary sum has two summands and both are
  in hand.  Their INDEXED forms cannot be: to affirm `⊕ᴰ Y A` one must
  produce a tag, and to refute it one must refute every tag, so the index
  has to be searched.  Finiteness of `Y` is exactly what makes that
  possible, and it is the only hypothesis here.

  Both lemmas are stated as maps of the calculus,

      dec-⊕ᴰ : &ᴰ Y (λ y → Dec⟨ A y ⟩)  ⊢  Dec⟨ ⊕ᴰ Y A ⟩
      dec-&ᴰ : &ᴰ Bool (λ b → Dec⟨ A b ⟩) ⊢ Dec⟨ &ᴰ Bool A ⟩

  -- "a decision at every tag decides the sum" -- so a decision procedure
  over a description (`Inductive.Functor`) is a composite of `⊢`-terms:
  `⟦ ⊕e Y G ⟧c` IS `⊕ᴰ Y`, and `⟦ &e Y G ⟧c` IS `&ᴰ Y`, definitionally.

  Only the CARRIER is needed, exactly as for `DecAdd` -- searching a tag
  type never touches the operations.  The search itself is `Enumerable`'s
  `decΣ` / `decΠBool`; neither is re-derived.
-}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Decidable.Listable where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.List

open import TheoryGrammar.Base
open import TheoryGrammar.Enumerable
open import TheoryGrammar.Decidable.Additive

private variable ℓS ℓX ℓA ℓY : Level

module DecList {S : Type ℓS} (Car : S → Type ℓX) where

  open DecAdd Car

  private variable s : S

  -- ================================================================
  -- The indexed SUM, over a listable tag type.
  --
  -- `Listable` is not a record here on purpose: the two components are
  -- exactly what `decΣ` consumes, and bundling them would force every
  -- instance to build a record for what is already a list plus a lemma
  -- (`Spans.Base.allCuts` / `allCutsComplete`).
  -- ================================================================

  dec-⊕ᴰ : (Y : Type ℓY) (A : Y → TheoryTy ℓA s)
           (ys : List Y) → ((y : Y) → y ∈L ys)
         → &ᴰ Y (λ y → Dec⟨ A y ⟩) ⊢ Dec⟨ ⊕ᴰ Y A ⟩
  dec-⊕ᴰ Y A ys complete m d = decΣ ys complete d

  -- ================================================================
  -- The indexed PRODUCT, at the arity `Bool`.
  --
  -- Stated at `Bool` rather than at a listable `Y` because that is what
  -- the binary arities need and because the general form would have to
  -- carry `AllYes`-style bookkeeping for no present customer.  The two
  -- slots of a binary operation, and the two components of a
  -- "nonterminal together with its resource certificate", are both this.
  -- ================================================================

  dec-&ᴰ : (A : Bool → TheoryTy ℓA s)
         → &ᴰ Bool (λ b → Dec⟨ A b ⟩) ⊢ Dec⟨ &ᴰ Bool A ⟩
  dec-&ᴰ A m d = decΠBool (d true) (d false)

  -- ... and the indexed PRODUCT at a listable index.  `findΠ` returns
  -- the OFFENDING tag, which is what turns "this component fails" into
  -- a refutation of the product.
  dec-&ᴰL : (Y : Type ℓY) (A : Y → TheoryTy ℓA s)
            (ys : List Y) → ((y : Y) → y ∈L ys)
          → &ᴰ Y (λ y → Dec⟨ A y ⟩) ⊢ Dec⟨ &ᴰ Y A ⟩
  dec-&ᴰL Y A ys complete m d = out (findΠ ys complete d)
    where out : _ → Dec⟨ &ᴰ Y A ⟩ m
          out (inl h)       = inl h
          out (inr (y , k)) = inr λ f → k (f y)
