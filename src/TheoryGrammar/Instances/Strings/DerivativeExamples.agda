{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The derivative stack, end to end, at `Char := Bool`.

   Both `decδ⊗` and `decRE` decide a grammar rather than returning a
   `Bool` to be verified, so their types already force correctness.  The
   check that matters is that they REDUCE: everything below is `refl`.

   One import, not two: `RegExp` re-exports `Derivative`, and reaching
   `Strings.Base Bool` down two different chains would make every shared
   name ambiguous. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Strings.DerivativeExamples where

open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.List
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Enumerable using (No)

decBool : (a b : Bool) → (a Eq.≡ b) ⊎ No (a Eq.≡ b)
decBool true  true  = inl Eq.refl
decBool false false = inl Eq.refl
decBool true  false = inr λ ()
decBool false true  = inr λ ()

open import TheoryGrammar.Instances.Strings.RegExp Bool decBool

isYes : {X : Type₀} → X ⊎ No X → Bool
isYes (inl _) = true
isYes (inr _) = false

-- ==================================================================
-- 1.  `decδ⊗` -- deciding a tensor by differentiating, no enumeration.
--     The grammar is "starts with `true`" : ⌈ true ⌉ ⊗ ⊤.
-- ==================================================================

decLit : (w : List Bool) → (w Eq.≡ (true ∷ [])) ⊎ No (w Eq.≡ (true ∷ []))
decLit []             = inr λ ()
decLit (false ∷ _)    = inr λ ()
decLit (true ∷ [])    = inl Eq.refl
decLit (true ∷ _ ∷ _) = inr λ ()

Alit : (a : MonAr appop) → TheoryTy ℓ-zero tt
Alit true  = ⌈ true ∷ [] ⌉
Alit false = ⊤G

dlit : SlotDec Alit
dlit true  w = decLit w
dlit false w = inl tt

_ : isYes (decδ⊗ Alit dlit (true ∷ false ∷ [])) ≡ true
_ = refl

_ : isYes (decδ⊗ Alit dlit (false ∷ [])) ≡ false
_ = refl

_ : isYes (decδ⊗ Alit dlit []) ≡ false
_ = refl

-- ==================================================================
-- 2.  `decRE` -- Brzozowski matching.  `a ⋆ · b` with a = `true`,
--     b = `false`; note the star's body is `RegExp false`, so the
--     nullability index accepts it with nothing to check.
-- ==================================================================

a b : RegExp false
a = ⟨ true ⟩
b = ⟨ false ⟩

a⋆b : RegExp false
a⋆b = a ⋆ · b

_ : isYes (decRE a⋆b (false ∷ [])) ≡ true
_ = refl

_ : isYes (decRE a⋆b (true ∷ true ∷ false ∷ [])) ≡ true
_ = refl

_ : isYes (decRE a⋆b []) ≡ false
_ = refl

_ : isYes (decRE a⋆b (true ∷ true ∷ [])) ≡ false
_ = refl

_ : isYes (decRE a⋆b (false ∷ false ∷ [])) ≡ false
_ = refl

-- alternation, and a nullable regex: (a ∪ b) ⋆ accepts everything
allBits : RegExp true
allBits = (a ∪ b) ⋆

_ : isYes (decRE allBits []) ≡ true
_ = refl

_ : isYes (decRE allBits (true ∷ false ∷ true ∷ [])) ≡ true
_ = refl
