{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE OTHER END OF THE CHAIN ACCUMULATES TOO, AND IT COSTS NOTHING.

  `Chain.Aligned` accumulates the LEXER: characters and tokens, glued
  along the invariant "this cut falls at a token boundary".  Getting
  there took a restriction (`Sub`), a transducer law, and a splitting
  lemma.  This file does the CODE GENERATOR, and the whole construction
  is four lines, because `LinLam.Codegen` had already proved both
  halves for its own reasons:

      layPres : (o : MonOp) → SplitPresAt layoutMap o     -- no aliasing
      layRefl : (o : MonOp) → A.ReflectsSplitAt o         -- readback

  Those are exactly `pullbackDetermined`'s two arguments.  So the
  accumulated theory -- a linear context together with the heap it lays
  out to -- is an instantiation and not a construction.

  THIS IS THE POINT OF THE FILE.  One worked instance is an anecdote;
  the value of `Chain.Aligned` was in doubt until a second pass, at the
  far end of the chain and over a completely different pair of theories,
  fell out of machinery that was written before anyone was thinking
  about accumulation.  `layPres` was proved to say "the code emitted for
  the two premises of an application does not alias".  That it is also
  the condition under which the pass may accumulate is not a
  coincidence: both say the pass respects the decomposition, which is
  what `SplitPresAt` means.

  ------------------------------------------------------------------
  WHAT THE ACCUMULATION SAYS HERE.

  `Determined` gives, by `Gluing.determined→reflects`, that `π₁`
  reflects splittings -- so `Along.pull⊗` applies and the LINEAR
  theory's whole multiplicative fragment transports into the glue.
  Every program over `linFib` lifts to one that carries its heap.

  And the transported splitting IS the no-aliasing theorem, now as a
  computation rather than a lemma: §3 cuts a three-variable context with
  a dead middle, and the two heaps that come back are disjoint, with the
  disjointness witness produced by the transport.

  ------------------------------------------------------------------
  WHAT IT DOES NOT SAY, and this bound is the same one `Chain.Accumulate`
  records.  Accumulation retains INDICES, not DERIVATIONS.  The usage is
  now carried into the target theory; the TERM still is not, so
  `Compile.Semantics.Simulation.noBlindBackend` -- two distinct terms,
  one usage, one program -- is untouched by any of this.  The heap
  backends stay blind however many theories they carry.
-}
open import Cubical.Foundations.Prelude

module Chain.AlignedCodegen where

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.List using (List; []; _∷_)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Theories.Monoid
open import TheoryGrammar.Fibered
open import TheoryGrammar.CarrierMap
open import TheoryGrammar.Gluing

import TheoryGrammar.Instances.LinLam.Context as CX
import TheoryGrammar.Instances.LinLam.Codegen as CG
import TheoryGrammar.Instances.Heap.Base      as H

-- ==================================================================
-- §1  THE ACCUMULATED THEORY.  Four lines.
-- ==================================================================

-- the identity right leg, which reflects splittings trivially
idRe : Reindex H.heapFib H.heapFib
idRe .hom _ h = h

idReflects : (o : MonOp) → Along.ReflectsSplitAt idRe o
idReflects o m sp' = sp' , λ _ → Eq.refl

-- a linear context together with the heap it lays out to
module PB = Pullback CX.linFib H.heapFib CG.layoutMap idRe

-- THE PAYOFF, by instantiation: `layPres` is the preservation half,
-- already proved as the no-aliasing theorem; the identity leg supplies
-- the reflection half.
determined : PB.Determined
determined = PB.pullbackDetermined CG.layPres idReflects

-- ... and hence `π₁` reflects splittings, so every linear program lifts
reflects : (o : MonOp) → PB.Reflects₁ o
reflects = PB.determined→reflects determined

-- ==================================================================
-- §2  THE PROJECTIONS.  Exact, and maps of promodels.
-- ==================================================================

usageOf : PB.glue .carrier tt → CX.Usage
usageOf g = g .fst

heapOf : PB.glue .carrier tt → H.Heap
heapOf g = g .snd .fst

-- ==================================================================
-- §3  IT EVALUATES.  The three-variable context with a DEAD MIDDLE --
-- `Compile.Showcase`'s `ugap`, whose address gap is the visible content
-- of "positions are addresses".
-- ==================================================================

ugap : CX.Usage
ugap = true ∷ false ∷ true ∷ []

_ : CG.layout ugap ≡ (0 , H.v1) ∷ (2 , H.v1) ∷ []
_ = refl

-- the accumulated element: the usage, its heap, and the proof they
-- correspond -- which is `Eq.refl`, because the heap IS the layout
elt : PB.glue .carrier tt
elt = ugap , CG.layout ugap , Eq.refl

_ : usageOf elt ≡ true ∷ false ∷ true ∷ []
_ = refl

_ : heapOf elt ≡ (0 , H.v1) ∷ (2 , H.v1) ∷ []
_ = refl

-- ------------------------------------------------------------------
-- 3.1  A CONTEXT SPLIT, TRANSPORTED -- and the transport IS the
-- no-aliasing theorem.  Variable 0 goes left, variable 2 goes right,
-- and the dead middle is skipped by both.
-- ------------------------------------------------------------------

cut : CX.linFib .Split appop ugap
cut = (true ∷ false ∷ false ∷ [])
    , (false ∷ false ∷ true ∷ [])
    , CX.uleft (CX.uskip (CX.uright CX.unil))

lifted : PB.Splitᴰ appop ugap (CG.layout ugap) cut
lifted = determined appop elt cut

heapCut : H.heapFib .Split appop (CG.layout ugap)
heapCut = lifted .fst

-- the two emitted regions ...
_ : heapCut .fst ≡ (0 , H.v1) ∷ []
_ = refl

_ : heapCut .snd .fst ≡ (2 , H.v1) ∷ []
_ = refl

-- ... AND THEY ARE DISJOINT.  `heapCut .snd .snd .snd` is the `_#_`
-- witness, and nobody wrote it: it came out of the transport, which is
-- `LinLam/Codegen`'s claim that the source's MISSING `(true,true)`
-- constructor manufactures the target's disjointness conjunct.
noAlias : heapCut .fst H.# heapCut .snd .fst
noAlias = heapCut .snd .snd .snd

-- ------------------------------------------------------------------
-- 3.2  The whole context, exhausted: `nilop` accumulates too.
-- ------------------------------------------------------------------

dead : CX.Usage
dead = false ∷ false ∷ []

eltNil : PB.glue .carrier tt
eltNil = dead , CG.layout dead , Eq.refl

_ : heapOf eltNil ≡ []
_ = refl

liftedNil : PB.Splitᴰ nilop dead (CG.layout dead) tt
liftedNil = determined nilop eltNil tt
