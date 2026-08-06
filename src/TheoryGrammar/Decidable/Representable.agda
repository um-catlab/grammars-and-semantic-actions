{-
  DECIDING A REPRESENTABLE.

  `⌈ a ⌉` is the one grammar whose decision is a fact about the substrate
  and not about any connective, so it is the one place external
  decidability may enter.  The rule is the same as in
  `Lambda.ScopeCheck.dec-⌈⌉`: `Discrete` is used to BUILD an internal map,
  never to case-split on one.  Stated once, generically, so instances
  stop re-deriving it.
-}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Decidable.Representable where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty as E using (⊥)
open import Cubical.Relation.Nullary.Base using (yes; no; Discrete)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Decidable.Additive

private variable ℓS ℓ ℓ' ℓX : Level

module DecRep {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (M : Model σ ℓX) where

  open DecAdd M

  dec-⌈⌉ : {s : S} → Discrete (M .carrier s)
         → (a : M .carrier s) → ⊤G ⊢ Dec⟨ ⌈ a ⌉ ⟩
  dec-⌈⌉ {s = s} _≟_ a m _ with m ≟ a
  ... | yes p = dec-yes (⌈_⌉ {s = s} a) m (Eq.pathToEq p)
  ... | no ¬p = dec-no  (⌈_⌉ {s = s} a) m λ e → E.rec (¬p (Eq.eqToPath e))
