{-
  REPRESENTABLES ARE THE TENSORS OF REPRESENTABLES.

      ⌈ op o m⃗ ⌉  ≅  ⊗ˢ o (λ a → ⌈ m⃗ a ⌉)

  `Fibered` says every tuple splits its own composite (`parts-split`).
  The converse -- reassembling a splitting's parts gives the whole back
  -- is NOT a field, and it is exactly what this iso's `from` direction
  needs, so it is taken as a parameter (`unsplit`).  For a syntax
  promodel every clause of it is `Eq.refl`.

  Two consequences, both used to decide equality of a carrier without
  ever leaving the calculus:

    * a representable at a composite is a tensor, so `dec-⊗` decides it;
    * the operations are INJECTIVE (`op-inj`), given unique readability.

  So `Discrete` on a sort is not an input to an instance -- it is the
  decidability of `⌈_⌉`, and it is built by the generic tensor rule.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Representable where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered

private variable ℓS ℓ ℓ' ℓX ℓP : Level

module Repr {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (Fib : Fibered σ ℓX ℓP)
            (P : LaxPoint Fib)
            (unsplit : (o : σ .ops) (m : Fib .carrier (σ .resultSort o))
                       (sp : Fib .Split o m)
                     → P .op o (Fib .parts o m sp) Eq.≡ m)
  where

  open FibNotation Fib

  module _ (o : σ .ops)
           (m⃗ : (a : σ .arities o) → Fib .carrier (σ .sortOf o a)) where

    -- PRIMITIVE (one `Eq.refl` match): the canonical splitting is the
    -- one the tuple makes, and `parts-split` says it has the right parts.
    ⌈⌉-into : ⌈ P .op o m⃗ ⌉ ⊢ ⊗ˢ o (λ a → ⌈ m⃗ a ⌉)
    ⌈⌉-into .(_) Eq.refl =
      P .split o m⃗ , λ a → Eq.pathToEq (funExt⁻ (P .parts-split o m⃗) a)

    -- no match at all: `unsplit` plus congruence
    ⌈⌉-from : ⊗ˢ o (λ a → ⌈ m⃗ a ⌉) ⊢ ⌈ P .op o m⃗ ⌉
    ⌈⌉-from m (sp , h) =
      Eq.pathToEq (sym (Eq.eqToPath (unsplit o m sp))
                   ∙ cong (P .op o) (funExt λ a → Eq.eqToPath (h a)))

  -- ================================================================
  -- Unique readability makes the operations injective.
  -- ================================================================

  module _ (splitProp : (o : σ .ops) (m : Fib .carrier (σ .resultSort o))
                        (p q : Fib .Split o m) → p ≡ q) where

    op-inj : (o : σ .ops)
             (m⃗ m⃗' : (a : σ .arities o) → Fib .carrier (σ .sortOf o a))
           → P .op o m⃗ Eq.≡ P .op o m⃗' → m⃗ ≡ m⃗'
    op-inj o m⃗ m⃗' e =
        sym (P .parts-split o m⃗)
      ∙ cong (Fib .parts o (P .op o m⃗))
             (splitProp o (P .op o m⃗) (P .split o m⃗) (sp .fst))
      ∙ funExt (λ a → Eq.eqToPath (sp .snd a))
      where
      sp : ⊗ˢ o (λ a → ⌈ m⃗' a ⌉) (P .op o m⃗)
      sp = ⌈⌉-into o m⃗' (P .op o m⃗) e
