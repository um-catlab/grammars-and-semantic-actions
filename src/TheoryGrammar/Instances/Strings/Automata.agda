{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The string instance of the generic automaton interface.

   `Automaton`, `Scanner` and `runAut` are theory-generic and live in
   `TheoryGrammar.Graded` -- an automaton is an ALGEBRA, ⊤ carries a
   COALGEBRA, and running one is the HYLOMORPHISM.  Nothing about
   strings appears there.

   All this file supplies is the three per-theory pieces:

   (1) THE FUNCTOR.  "Read one character, or stop" is `starF char` --
       `Strings/KleeneStar`'s star description at `char = ⊕ᴰ Char literal`.
       Nothing new is defined.

   (2) ⊤ IS A COALGEBRA FOR IT, MANIFESTLY.  `charCase` is already
       `Cover (⌈ [] ⌉ ⊕ NonTrivial)` -- i.e. `⊤ ⊢ ε ⊕ ⊕ᴰ Char (λ c → ⌈c⌉ ⊗ ⊤)`
       -- which IS the coalgebra structure.  This is the decomposition
       axiom, and it is the shape of ⊤ rather than a fact about automata.

   (3) THE FUNCTOR IS GUARDED (locally contractive): the recursive slot
       sits behind a proper splitting, since `char` is non-nullable.
       That is `starGuarded char charNN`, again already proved -- the
       star is guarded exactly when its body is non-nullable.

   So an AUTOMATON IS AN ALGEBRA `AlgC (starF char) B`, and running it on
   an input is `hyloC` at ⊤'s coalgebra.  A DFA is then one way to BUILD
   such an algebra, not a separate notion: `dfaAlg` below turns a
   transition function and an acceptance predicate into one, and the
   `run` it gets is the generic hylo. -}
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

-- ==================================================================
-- (1) the functor, and (3) its guardedness
-- ==================================================================

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

-- ==================================================================
-- (2) ⊤'s own coalgebra.  This is `charCase` with its two branches
-- transported into the description's shape -- the only content is that
-- `⌈ [] ⌉` and `ε'` are two spellings of the unit.
-- ==================================================================

scanCoalg : Scanner ScanF
scanCoalg tt m _ = go (charCase m tt)
  where
    go : (⌈ [] ⌉ ⊕ NonTrivial) m → ⟦ ScanF tt ⟧ᴳ (λ _ → ⊤ᴳ) m
    go (inl e) = true , lift (nilOf e)
      where nilOf : m Eq.≡ [] → ε' m
            nilOf Eq.refl = tt , λ ()
    go (inr (c , sp , h)) =
      false , sp , λ { true  → lift (c , h true) ; false → tt* }

-- The three pieces, bundled: this is what makes `ScanF` a decomposition
-- of the input rather than an arbitrary description.
charScan : Scan
charScan .desc       = ScanF
charScan .contractive = guarded→LC scanGuarded
charScan .decompose  = scanCoalg

-- ==================================================================
-- A DFA is ONE WAY TO BUILD such an algebra -- not a separate notion.
-- The carrier is "given a state, does the machine accept from here?",
-- so the ε-branch is the acceptance predicate and the character branch
-- is the transition.
-- ==================================================================

module DFA (Q : Type₀) (step : Q → Char → Q) (acc : Q → Bool) where

  Acceptance : Fam
  Acceptance _ _ = Q → Bool

  dfaAlg : Automaton charScan Acceptance
  dfaAlg tt =
    ⊕ᴰ-E λ { true  → λ _ _ q → acc q
           ; false →
               ⊗ˢ-E appop {A = λ a → ⟦ starSlot char a ⟧c ⌞ Acceptance ⌟}
                          {B = λ _ → Q → Bool}
                          (λ _ _ h q → h false (step q (lower (h true) .fst))) }

  -- ... and the observable: run from a start state
  accepts : Q → ⊤G ⊢ (λ _ → Bool)
  accepts q₀ m x = runAut⊤ {S = charScan} dfaAlg tt m x q₀
