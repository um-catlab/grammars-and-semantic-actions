{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{-
  ACCUMULATING THE THEORY ALONG A PASS: THE PRODUCT IS TOO WEAK, AND
  THE CHAIN ALREADY KNEW WHAT THE FIX IS.

  THE PROPOSAL.  `Chain.Project`'s cascade projects a stage-n IR back to
  stage 0 by REBUILDING text, and `Chain.PrintTests` measures what that
  costs: names are invented (α), the tree shape is not recoverable (no
  parentheses), and the reparse of the renamed text does not terminate.
  Every one of those is a symptom of the same thing -- a pass REPLACES
  its theory, so the earlier index is gone and has to be guessed back.

  The proposal is to stop replacing.  If the chain runs over theories
  S, T, R then a pass should not go `T → S`; it should go into the
  PRODUCT, accumulating, so that nothing is ever lost and the backward
  projection is a projection rather than a reconstruction.

  THE CONSTRUCTION EXISTS.  `TheoryGrammar.Gluing.Product` is precisely
  that, and it is better than it needs to be: `π₁` and `π₂` are
  `Reindex`es preserving EVERY splitting definitionally (`homParts` is
  `Eq.refl`), so a projection out of an accumulated theory is a map of
  promodels and the whole additive fragment transports by `pullTerm`
  with no hypothesis at all.  That is exactly the `↘` of
  `Chain.Project`, upgraded from a metalanguage function to a term.

  ------------------------------------------------------------------
  AND YET THE PRODUCT DOES NOT WORK.  `notDetermined` BELOW.

  `Gluing`'s payoff condition is `Determined`: every splitting of the
  left factor lifts to one of the glue, hence "every program over `Fib`
  lifts".  Without it the accumulated theory has the right ELEMENTS and
  the wrong MULTIPLICATIVE STRUCTURE -- you may pair the two tapes, and
  you may not cut them.

  For the product of two string theories `Determined` is FALSE, and the
  refutation is two lines, at `nilop`.  `Split nilop w` is `IsNil w`, so
  the condition reads

      if the INPUT tape is empty then the OUTPUT tape is empty

  and a product imposes no relation between its factors, so `([] , c ∷
  [])` is an element and refutes it.  The same failure at `appop` is the
  one that matters in practice: knowing where the TOKEN stream splits
  tells you nothing about where the CHARACTER stream splits, because a
  product does not know that `λx.` is three characters.

  NOTE ALSO that `Gluing`'s own header asserts "Product: ... Both
  `Coherent` and `Determined` hold".  `module Product` proves
  `coherent` and does not prove `Determined`, which is just as well,
  since it is refutable.  Another stale header of the kind the audit
  keeps finding.

  ------------------------------------------------------------------
  THE FIX IS THE COMMA OBJECT, AND IT IS ALREADY BUILT.

  What makes the two tapes cut together is an ALIGNMENT, and
  `Instances/Strings/Aligned` is the glue along it:

      alignedDetermined = pullbackDetermined LI.lenPres LO.lenReflects

  -- "cutting the input tape cuts the output tape AT THE MATCHING
  POSITION".  So the accumulation the chain wants is not `Fib × Fib'`
  but the comma object over a common measure, and the discrete Conduché
  half (`lenReflects`) is what pays for it.

  THE RETROSPECTIVE POINT, and the reason this is worth writing down:

      `Chain.Lex`'s  `LTok = Tok × ℕ`  IS THE ALIGNMENT DATUM,
      HAND-ROLLED.

  The offset threaded through the lexer's state is exactly what a
  product could not supply and what `Aligned` supplies structurally.
  `Chain.Pipeline` §6 already uses it for the one backward projection it
  has, and calls it "retention".  It is the comma object, discovered by
  need and built by hand -- which is the same discovery
  `Chain.Unparse` made about `skel`/`eraseS`, one theory further down.
-}
open import Cubical.Foundations.Prelude

module Chain.Accumulate (In Out : Type₀) (c : Out) where

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty as E using (⊥)
open import Cubical.Data.List using (List; []; _∷_)

open import TheoryGrammar.Base
open import TheoryGrammar.Theories.Monoid
open import TheoryGrammar.Fibered
open import TheoryGrammar.CarrierMap
open import TheoryGrammar.Gluing

import TheoryGrammar.Instances.Strings.Base as StB
module I = StB In
module O = StB Out

-- ==================================================================
-- §1  THE ACCUMULATED THEORY, as the proposal asks for it: the pass
-- keeps its source alongside its target.
-- ==================================================================

open Product I.strFib O.strFib public

-- ==================================================================
-- §2  THE PROJECTIONS ARE EXACT -- this half of the proposal is right,
-- and it is free.
--
-- `π₂` recovers the retained tape ON THE NOSE.  Compare
-- `Chain.Unparse.unSkel`, which had to invent names to get back to the
-- token stream: here there is nothing to invent, because nothing was
-- dropped.  `π₂-pres` says more -- the projection carries splittings
-- too, with `homParts` an `Eq.refl`.
-- ==================================================================

retained : glue .carrier tt → O.String
retained = π₂ .hom tt

exactly : (w : I.String) (v : O.String) → retained (w , v , tt) ≡ v
exactly _ _ = refl

-- ==================================================================
-- §3  ... AND THE MULTIPLICATIVE STRUCTURE IS NOT.  `Determined` fails.
--
-- An empty input tape beside a nonempty output tape is an element of
-- the product, and `Split nilop` is `IsNil`, so the lift it demands is
-- an inhabitant of `⊥`.
-- ==================================================================

bad : glue .carrier tt
bad = [] , (c ∷ []) , tt

notDetermined : Determined → ⊥
notDetermined d = d nilop bad tt .fst

-- ... so `π₁` does not reflect splittings either, since `Determined` is
-- exactly that (`determined→reflects`), and the left factor's
-- multiplicative fragment does NOT transport into the product.
notReflects : ((o : MonOp) → Reflects₁ o) → ⊥
notReflects r = r nilop bad tt .fst .snd .fst
