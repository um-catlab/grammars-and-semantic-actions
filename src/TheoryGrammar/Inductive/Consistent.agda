{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  T2.  A DERIVATION AND A REFUTATION CANNOT BOTH EXIST.

  `Inductive.Dual` proves the LAYERS are exclusive, structurally and with
  no hypothesis about the theory.  This file closes it under the fixed
  point, and the only thing it adds is `löb`:

      excl    : the layers exclude                 (Dual, no hypotheses)
      excl-μ  : μ F and μ⁻ F exclude               (here, needs guardedness)

  ==================================================================
  WHAT THIS IS AND IS NOT.

  It is the CONSISTENCY half of a decision, and it is deliberately
  separated from the completeness half (`Decidable.Inductive`) because it
  is far cheaper: no enumeration of splittings, no listed rule sets, no
  decidable constants.  Guardedness alone.  Anyone who wants "a parse and
  a refutation are incompatible" -- e.g. to know an error report is
  honest -- should depend on this file and not on the decision procedure.

  In the vocabulary of `View`/`Decidable.Additive`, this supplies
  `Decision`'s `exclude`; `Decidable.Inductive` supplies `decide`.  The
  pair is then a `Complete Bool` view, i.e. a genuine two-valued
  partition rather than merely a `Dec⟨_⟩`.

  Against Atkey's `Data Types with Negation`: his Chu objects carry no
  such condition ("we could also add `A⁺ × A⁻ → ⊥`, but will skip this
  for now"), and for good reason -- without stratification it can fail,
  and his `Liar ≅ (⊥ , ⊥)` is the third truth value appearing.  Our
  guardedness IS stratification, and this file is the payoff.

  ==================================================================
  GUARDEDNESS, TWICE.

  `GuardedD` is `Dual.Reaches` at `Ok j = degIx j < deg m`, and
  `GuardedD⁻` is `Reaches⁻` at the same.  They are SEPARATE hypotheses.
  The negative one is not implied by the positive: a refutation of a
  tensor picks one slot per splitting, and at a trivial splitting it could
  pick the slot that is all of `m`.  What rules that out is the ε-ban --
  the sibling grammar entails non-triviality, so the empty slot is the
  refuted one and it has strictly smaller degree.  See `Dual.Reaches⁻`.

  PRIMITIVE: none.
-}
module TheoryGrammar.Inductive.Consistent where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order using (_<_)
open import Cubical.Data.Empty as E using (⊥; ⊥*)

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded
open import TheoryGrammar.Grading
open import TheoryGrammar.Inductive.Dual

private variable ℓS ℓ ℓ' ℓX ℓP ℓA ℓV : Level

module Consistent {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
                  (GS : GradedFib σ ℓX ℓP) (ℓA : Level)
                  (X : Type ℓV) (xs : X → S) where

  -- the dual container is the primary export; the grading contributes
  -- only the order and its löb, so it is opened selectively to avoid
  -- re-exporting `Ind`'s names twice
  open Dual (GS .fib) ℓA X xs public
  open Grade GS ℓA X xs public
    using (degIx; _≺_; löb; löb-unfold; löb-unique) renaming (▷ to ▷g)

  private
    Car : (s : S) → Type ℓX
    Car = GS .fib .carrier

  -- GUARDEDNESS, as `Reaches` at the degree.  Nothing new is defined --
  -- these are instances of the abstract predicate in `Dual`, which is
  -- why that file never mentions a grading.

  GuardedD : {s : S} → Functor s → Car s → Type _
  GuardedD {s} F m = Reaches F m (λ j → degIx j < GS .deg s m)

  GuardedD⁻ : {s : S} → Functor s → Car s → Type _
  GuardedD⁻ {s} F m = Reaches⁻ F m (λ j → degIx j < GS .deg s m)

  -- T2.  One `löb` over `Dual.excl`, and nothing else happens.

  module _ {F : (x : X) → Functor (xs x)}
           (gF  : (x : X) (m : Car (xs x)) → GuardedD  (F x) m)
           (gF⁻ : (x : X) (m : Car (xs x)) → GuardedD⁻ (F x) m)
    where

    excl-μ : (i : Ix) → μ F i → μ⁻ F i → ⊥
    excl-μ = löb step
      where
        step : (i : Ix) → ▷g (λ j → μ F j → μ⁻ F j → ⊥) i
             → μ F i → μ⁻ F i → ⊥
        step (x , m) rec t u =
          excl rec (F x) m (gF x m) (gF⁻ x m) (unroll t) (unroll⁻ u)

    -- ... AS A MAP OF THE CALCULUS.  This is exactly `Decision`'s
    -- `exclude` field, so the pair `(μ F , μ⁻ F)` is half a decision the
    -- moment the description is guarded.
    excludeμ : (x : X) (m : Car (xs x))
             → μ F (x , m) × μ⁻ F (x , m) → ⊥* {ℓ-zero}
    excludeμ x m (t , u) = E.rec (excl-μ (x , m) t u)

  -- T3. THE NEGATIVE COMPONENT NEEDS NO COINDUCTION.
