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
open import Cubical.Data.Nat using (ℕ; zero; suc)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Enumerable using (No)
open import TheoryGrammar.SemanticAction using (passes; _↦_; _at_)

decBool : (a b : Bool) → (a Eq.≡ b) ⊎ No (a Eq.≡ b)
decBool true  true  = inl Eq.refl
decBool false false = inl Eq.refl
decBool true  false = inr λ ()
decBool false true  = inr λ ()

open import TheoryGrammar.Instances.Strings.Automata Bool decBool

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

_ : passes ((λ w → isYes (decδ⊗ Alit dlit w)) at
             ( (true ∷ false ∷ []) ↦ true
             ∷ (false ∷ [])        ↦ false
             ∷ []                  ↦ false
             ∷ [] ))
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

_ : passes ((λ w → isYes (decRE a⋆b w)) at
             ( (false ∷ [])                 ↦ true
             ∷ (true ∷ true ∷ false ∷ [])   ↦ true
             ∷ []                           ↦ false
             ∷ (true ∷ true ∷ [])           ↦ false
             ∷ (false ∷ false ∷ [])         ↦ false
             ∷ [] ))
_ = refl

-- alternation, and a nullable regex: (a ∪ b) ⋆ accepts everything
allBits : RegExp true
allBits = (a ∪ b) ⋆

_ : passes ((λ w → isYes (decRE allBits w)) at
             ( []                          ↦ true
             ∷ (true ∷ false ∷ true ∷ [])  ↦ true
             ∷ [] ))
_ = refl

-- ==================================================================
-- 3.  AUTOMATA AS ALGEBRAS.  An automaton is an `AlgC (starF char) B`,
--     ⊤ carries the coalgebra, and running one is `hyloC`.  No
--     recursion is written in either example below.
-- ==================================================================

-- (a) a DFA: even number of `true`s.  The state is the parity so far.
module Parity = DFA Bool (λ q c → if c then not q else q) (λ q → q)

-- `Parity.accepts true` is ALREADY the program -- a term `⊤G ⊢ Δ Bool`.
-- Naming it at `List Bool → Bool` would externalise it in a definition;
-- `run` belongs in the `refl` line below and nowhere else.
evens : ⊤G ⊢ Δ Bool
evens = Parity.accepts true

_ : passes (run evens at
             ( []                                 ↦ true
             ∷ (true ∷ [])                        ↦ false
             ∷ (true ∷ true ∷ [])                 ↦ true
             ∷ (false ∷ true ∷ false ∷ true ∷ []) ↦ true
             ∷ [] ))
_ = refl

-- (b) NOT a DFA -- any algebra will do, which is the point of defining
--     an automaton as one.  This one has an infinite state space.
countAlg : Algᴳ ScanF (λ _ _ → ℕ)
countAlg tt =
  ⊕ᴰ-E λ { true  → λ _ _ → 0
         ; false → ⊗ˢ-E appop {A = λ a → ⟦ starSlot char a ⟧c (λ _ → ℕ)}
                              {B = λ _ → ℕ}
                              (λ _ _ h → suc (h false)) }

-- named at `Δ ℕ` for the same reason `evens` is named at `Δ Bool`
countA : ⊤G ⊢ Δ ℕ
countA m x = runAut scanLC scanCoalg countAlg tt m x , x

_ : passes (run countA at
             ( (true ∷ false ∷ true ∷ []) ↦ 3
             ∷ []                         ↦ 0
             ∷ [] ))
_ = refl
