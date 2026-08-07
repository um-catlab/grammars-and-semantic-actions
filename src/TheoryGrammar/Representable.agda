{-
  A REPRESENTABLE AT A COMPOSITE IS THE TENSOR OF REPRESENTABLES.

      ⌈ op o m⃗ ⌉  ⊣⊢  ⊗ˢ o (λ a → ⌈ m⃗ a ⌉)

  Both directions -- `⌈⌉-into` and `⌈⌉-from` -- but NOT an `Iso`: the
  round trips are not proved here, and no consumer has needed them.

  `Fibered` gives `parts-split`: every tuple splits its own composite.
  The converse -- a splitting's parts reassemble to the whole -- is what
  the `from` direction needs and is NOT a field (it is refuted for
  quotient substrates), so it is a module parameter, `unsplit`; for a
  syntax promodel every clause of it is `Eq.refl`.

  Two consequences, both used to decide equality of a carrier without
  leaving the calculus: `dec-⊗` decides a representable through the iso,
  and the operations are INJECTIVE (`op-inj`) given unique readability.
  So `Discrete` on a sort is not an input to an instance -- it is
  decidability of `⌈_⌉`, built by the generic tensor rule.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Representable where

open import Cubical.Foundations.Prelude
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Precision using (module Prec)

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

  module _ (splitProp : Prec.SplitProp Fib) where

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
