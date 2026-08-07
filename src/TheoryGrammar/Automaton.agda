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
  open FibNotation (GS .fib)

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

  -- An automaton is an ALGEBRA -- as a term, `⟦F⟧ A ⊢ A`.
  Automaton : ((x : X) → Functor (xs x)) → Fam → Type _
  Automaton F A = Algᴳ F A

  -- ⊤ carries a COALGEBRA.  Carried by the terminal GRAMMAR `⊤ᴳ`, so
  -- this is a term `⊤ᴳ ⊢ ⟦F⟧ ⊤ᴳ` -- not a function out of a bare
  -- `Unit*`.  Supplying one is the theory's decomposition axiom.
  Scanner : ((x : X) → Functor (xs x)) → Type _
  Scanner F = Coalgᴳ F (λ _ → ⊤ᴳ)

  -- Running an automaton is the hylomorphism, and it is a TERM out of ⊤.
  runAut : {F : (x : X) → Functor (xs x)} {A : Fam}
         → ((x : X) → Guarded (F x)) → Scanner F → Automaton F A
         → (x : X) → ⊤ᴳ ⊢ A x
  runAut g sc α = hyloᴳ g sc α

  -- the same at the ℓ-zero terminal, which is what instances write
  runAut⊤ : {F : (x : X) → Functor (xs x)} {A : Fam}
          → ((x : X) → Guarded (F x)) → Scanner F → Automaton F A
          → (x : X) → ⊤G ⊢ A x
  runAut⊤ g sc α x = runAut g sc α x ∘⊢ ⊤ᴳ-I
