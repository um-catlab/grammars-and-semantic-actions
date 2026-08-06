{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The derivative decider, end to end, at `Char := Bool`.

   `decδ⊗` decides a tensor with no enumeration of cuts, so the check
   that matters is not that it typechecks -- its type already forces
   evidence or refutation -- but that it REDUCES.  Both tests below are
   `refl`.

   Separate from `Strings/Examples` because that file chains through
   `CYK`, and reaching `Strings.Base Bool` down two different chains
   makes every shared name ambiguous. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Strings.DerivativeExamples where

open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.List
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Enumerable using (No)
open import TheoryGrammar.Instances.Strings.Derivative Bool

-- the one decision the grammar needs: is this word the literal `true`?
decLit : (w : List Bool) → (w Eq.≡ (true ∷ [])) ⊎ No (w Eq.≡ (true ∷ []))
decLit []             = inr λ ()
decLit (false ∷ _)    = inr λ ()
decLit (true ∷ [])    = inl Eq.refl
decLit (true ∷ _ ∷ _) = inr λ ()

-- "starts with `true`" : ⌈ true ⌉ ⊗ ⊤
Alit : (a : MonAr appop) → TheoryTy ℓ-zero tt
Alit true  = ⌈ true ∷ [] ⌉
Alit false = ⊤G

dlit : SlotDec Alit
dlit true  w = decLit w
dlit false w = inl tt

isYes : {X : Type₀} → X ⊎ No X → Bool
isYes (inl _) = true
isYes (inr _) = false

_ : isYes (decδ⊗ Alit dlit (true ∷ false ∷ [])) ≡ true
_ = refl

_ : isYes (decδ⊗ Alit dlit (false ∷ [])) ≡ false
_ = refl

_ : isYes (decδ⊗ Alit dlit []) ≡ false
_ = refl
