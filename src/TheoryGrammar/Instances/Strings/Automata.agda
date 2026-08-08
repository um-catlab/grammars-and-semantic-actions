{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The string instance of the generic automaton interface. -}
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sum using (_⊎_; inl; inr)
import Cubical.Data.Equality as Eq
open import TheoryGrammar.Enumerable using (No)

module TheoryGrammar.Instances.Strings.Automata
  (Char : Type₀)
  (decChar : (a b : Char) → (a Eq.≡ b) ⊎ No (a Eq.≡ b))
  where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Unit
open import Cubical.Data.List

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded

open import TheoryGrammar.Instances.Strings.Greedy Char decChar public

-- (1) the functor, and (3) its guardedness

char : Gr
char = ⊕ᴰ Char literal

-- non-nullable, point-free: a sum of literals is a sum of the literals'
-- own non-nullability
charNN : NonNullable char
charNN = ⊕ᴰ-E literalNN

ScanF : Unit → Functor tt
ScanF = starF char

scanGuarded : (x : Unit) → Guarded (ScanF x)
scanGuarded = starGuarded char charNN

-- (2) ⊤'s own coalgebra.  This is `charCase` with its two branches
-- transported into the description's shape -- the only content is that
-- `⌈ [] ⌉` and `ε'` are two spellings of the unit.

scanCoalg : Scanner ScanF
scanCoalg tt m _ = go (charCase m tt)
  where
    go : (⌈ [] ⌉ ⊕ NonTrivial) m → ⟦ ScanF tt ⟧ᴳ (λ _ → ⊤ᴳ) m
    go (inl e) = true , lift (nilOf e)
      where nilOf : m Eq.≡ [] → ε' m
            nilOf Eq.refl = tt , λ ()
    go (inr (c , sp , h)) =
      false , sp , λ { true  → lift (c , h true) ; false → tt* }

-- guardedness is the easy sufficient criterion; what `runAut` wants is
-- the strength
scanLC : LocallyContractive ScanF
scanLC = guarded→LC scanGuarded

-- A DFA is ONE WAY TO BUILD such an algebra -- not a separate notion.

module DFA (Q : Type₀) (step : Q → Char → Q) (acc : Q → Bool) where

  Acceptance : Fam
  Acceptance _ _ = Q → Bool

  dfaAlg : Algᴳ ScanF Acceptance
  dfaAlg tt =
    ⊕ᴰ-E λ { true  → λ _ _ q → acc q
           ; false →
               ⊗ˢ-E appop {A = λ a → ⟦ starSlot char a ⟧c ⌞ Acceptance ⌟}
                          {B = λ _ → Q → Bool}
                          (λ _ _ h q → h false (step q (lower (h true) .fst))) }

  -- ... and the observable: run from a start state.
  accepts : Q → ⊤G ⊢ Δ Bool
  accepts q₀ = actΔ (λ f → f q₀) ∘g runAut scanLC scanCoalg dfaAlg tt
