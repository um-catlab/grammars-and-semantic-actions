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

  -- ================================================================
  -- WHAT `F` IS.
  --
  -- Not any description.  An algebra for an arbitrary `F` is just an
  -- algebra -- it has no claim to be an automaton, and nothing lets you
  -- run it.  Running needs TWO further facts, and together they are
  -- exactly "F is a decreasing decomposition of the input":
  --
  --   decompose : ⊤ carries a coalgebra for F.  So F really does take
  --               an element apart -- it is the theory's decomposition
  --               axiom (`charCase`, `bagCase`), not a guess.
  --
  --   contractive : F is GUARDED -- every recursive position sits at a
  --               STRICTLY smaller degree.  This IS local contractivity,
  --               not an analogue of it: `mapGuarded` DERIVES ccl's
  --               `▷HomActionFam` strength `▷(A ⇒ B) → (H A ⇒ H B)` from
  --               it, which is the datum a locally contractive functor
  --               is defined by.  Guardedness is the syntactic form,
  --               local contractivity the semantic one.
  --
  -- Neither implies the other: `decompose` alone permits a step that
  -- consumes nothing and loops; `contractive` alone describes a shrinking
  -- process that need not be a decomposition of THIS input.  Bundling
  -- them is what deserves a name, so the bundle gets one and the
  -- automaton is an algebra FOR IT.
  -- ================================================================

  -- ⊤'s coalgebra for a description -- the theory's decomposition axiom.
  Scanner : ((x : X) → Functor (xs x)) → Type _
  Scanner F = Coalgᴳ F (λ _ → ⊤ᴳ)

  record Scan : Type (ℓ-max ℓS (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓV
                     (ℓ-max ℓX (ℓ-max (ℓ-suc ℓA) (ℓ-max ℓSh ℓPos))))))) where
    field
      desc       : (x : X) → Functor (xs x)
      contractive : (x : X) → Guarded (desc x)
      decompose  : Scanner desc

  open Scan public

  -- An automaton over a scan is an ALGEBRA for its description.
  Automaton : Scan → Fam → Type _
  Automaton S A = Algᴳ (S .desc) A

  -- ... and running it needs NOTHING FURTHER: the scan already carries
  -- the decomposition and the termination certificate.
  runAut : {S : Scan} {A : Fam} → Automaton S A → (x : X) → ⊤ᴳ ⊢ A x
  runAut {S = S} α = hyloᴳ (S .contractive) (S .decompose) α

  -- the same at the ℓ-zero terminal, which is what instances write
  runAut⊤ : {S : Scan} {A : Fam} → Automaton S A → (x : X) → ⊤G ⊢ A x
  runAut⊤ {S = S} α x = runAut {S = S} α x ∘⊢ ⊤ᴳ-I
