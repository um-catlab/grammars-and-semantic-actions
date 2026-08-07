{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Automata, theory-generically.  See the note inside: an automaton is
   an algebra, ⊤ carries a coalgebra, and running one is the hylo. -}
module TheoryGrammar.Automaton where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Unit
open import Cubical.Induction.WellFounded

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
open import TheoryGrammar.Later
open import TheoryGrammar.Grading
open import TheoryGrammar.Hylo

private variable ℓS ℓ ℓ' ℓX ℓP ℓA ℓM ℓN ℓV : Level

-- `Guard` keeps its name and its parameters: it is what every instance
-- opens, and the split above is invisible to them.
module Guard {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
             (GS : GradedFib σ ℓX ℓP) (ℓA : Level)
             (X : Type ℓV) (xs : X → S) where

  open HyloM GS ℓA X xs public

  -- ================================================================
  -- AUTOMATA ARE ALGEBRAS, and running one is a hylomorphism.
  --
  -- This is theory-generic: nothing below mentions strings, characters,
  -- or even the signature's operations.  Three notions, all of which
  -- already exist:
  --
  --   * an AUTOMATON over a description is an ALGEBRA for it.  A DFA's
  --     transition table is one way to build such an algebra, not a
  --     separate notion -- and an algebra may have an infinite carrier,
  --     which a DFA may not.
  --
  --   * ⊤ carries a COALGEBRA for the description exactly when the
  --     theory can take its elements apart one step along it.  That is
  --     the DECOMPOSITION AXIOM (`charCase` for strings, `bagCase` for
  --     bags), and stating it as `Scanner` says what it actually is
  --     rather than leaving it an ad-hoc lemma.
  --
  --   * the description being GUARDED is local contractivity: each
  --     recursive position sits at a strictly smaller degree.
  --
  -- Given those, running the automaton on an input is `hyloC` and
  -- nothing else -- no recursion is written at the use site, and the
  -- termination certificate IS the guardedness.  Any theory with a
  -- decomposition axiom gets automata for free.
  -- ================================================================

  Automaton : ((x : X) → Functor (xs x)) → (Ix → Type ℓSh) → Type _
  Automaton F B = AlgC F B

  Scanner : ((x : X) → Functor (xs x)) → Type _
  Scanner F = CoalgC F (λ _ → Unit*)

  runAut : {F : (x : X) → Functor (xs x)} {B : Ix → Type ℓSh}
         → ((x : X) → Guarded (F x)) → Scanner F → Automaton F B
         → (i : Ix) → B i
  runAut g sc α i = hyloC g sc α i tt*
