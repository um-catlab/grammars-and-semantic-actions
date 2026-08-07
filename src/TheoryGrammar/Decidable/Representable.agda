{-
  DECIDING A REPRESENTABLE.

  `⌈ a ⌉` is the one grammar whose decision is a fact about the promodel
  and not about any connective, so it is the one place external
  decidability may enter.  `Discrete` is used to BUILD an internal map,
  never to case-split on one: the metalanguage `Dec` is consumed by its
  OWN elimination rule, `decRec`, exactly as an internal `Dec⟨_⟩` is
  consumed by `dec-elim`.  No `with`, no `yes`/`no` pattern.

  Stated once, generically, so instances stop re-deriving it.
-}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Decidable.Representable where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty as E using (⊥)
open import Cubical.Relation.Nullary.Base using (Discrete; decRec)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Decidable.Additive

private variable ℓS ℓ ℓ' ℓX : Level

-- Only the CARRIER is needed, not the operations -- deciding a
-- representable is an additive fact.  This tracks `DecAdd`, which takes
-- a carrier for the same reason.
module DecRep {S : Type ℓS} (Car : S → Type ℓX) where

  open DecAdd Car

  dec-⌈⌉ : {s : S} → Discrete (Car s)
         → (a : Car s) → ⊤G ⊢ Dec⟨ ⌈ a ⌉ ⟩
  dec-⌈⌉ {s = s} _≟_ a m _ =
    decRec (λ p  → dec-yes (⌈_⌉ {s = s} a) m (Eq.pathToEq p))
           (λ ¬p → dec-no  (⌈_⌉ {s = s} a) m λ e → E.rec (¬p (Eq.eqToPath e)))
           (m ≟ a)
