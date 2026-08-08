{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE INTRINSIC SOUNDNESS THEOREM OF AN ISA, AS A FIRST-CLASS PASS.

  ------------------------------------------------------------------
  WHAT AN ISA INSTANTIATION OWES, AND WHERE IT WAS STATED BEFORE
  ------------------------------------------------------------------

  `ISA.Interp` says it in prose and proves it: an ISA is TWO promodels
  over the monoid signature and a homomorphism between them.

      PROGRAM TEXT    `Strings` at the instruction alphabet.
                      `Split appop p` is a way of writing `p = p₁ ++ p₂`,
                      so `⊗ˢ appop` IS sequential composition.

      MACHINE COMMAND `ISA.Machine.cmdFib` over an arbitrary resource
                      promodel.  `Split appop c` is a lax factorisation
                      `c ⊑ c₁ ⨟ c₂`.

  and the soundness condition is that `sem` PRESERVES SPLITTINGS:

      sem r  ⊑  sem r₁ ⨟ sem r₂      whenever  r  splits as  r₁ · r₂

  That is the whole obligation.  Hoare sequencing, the empty program,
  consequence and framing are corollaries, derived once in `ISA.Interp`
  for every instruction set and every resource model simultaneously, and
  `ISA.Program.homSplit3` discharges the obligation in two clauses -- a
  unit law and an associativity.

  ------------------------------------------------------------------
  WHY IT COULD NOT BE SAID AS A `Pass`, AND WHY IT NOW CAN
  ------------------------------------------------------------------

  `ISA.Interp`'s header records the obstruction:

      "The record from `CarrierMap` is not literally instantiated
       because `Reindex` forces both promodels into the SAME universe
       levels, and `Cmd = Res → Res → Type₀` sits one level above
       `Res`.  The obstruction is bookkeeping, not mathematics."

  So `Interp` was a bespoke record that HAPPENED to be `SplitPresAt`,
  with a comment saying so.  `TheoryGrammar.Reindex.Base`'s `Over`
  layer removes exactly that: `ReindexOver` and `SplitPresAtOver` are
  HETEROGENEOUS in the two promodels' levels, and `Reindex.Pass.Pass`
  is heterogeneous in both theories'.  So the identification `Interp`
  asserted in prose is now a definition, and `semPass` below IS the
  soundness theorem -- not a record shaped like it.

  What that buys is not tidiness.  A `Pass` COMPOSES (`_⨟P_`), chains
  of them are `Chain`, and `composite` collapses a chain to a single
  pass.  Putting the ISA's soundness in that currency is what lets a
  compiler be one object with one theorem rather than a sequence of
  separately-stated lemmas glued by hand.

  ------------------------------------------------------------------
  WHAT IS STILL OWED, AND IT IS NOT NOTHING
  ------------------------------------------------------------------

  This file makes `text → command` a pass.  A COMPILER needs the other
  link, `source → text`, and that one is NOT free -- in fact it is
  false as stated.  `Compile.LinToISA.NoTextPres` proves that
  `compileU` does not preserve splittings into this `asmTheory`, for a
  reason that is about the target and not the compiler:

      A HEAP SPLITTING IS UNORDERED.  CONCATENATION IS ORDERED.

  and that is exactly what forces assembly to carry a MEMORY MODEL --
  the equation "instructions with disjoint footprints commute" -- rather
  than being the bare free monoid this file uses.  So `asmTheory` below
  is the RIGID version, correct for the semantics and too rigid to be a
  compiler target; read it together with that file.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 2 apart from the match on `MonOp`, which is the arity dispatch
  every promodel construction in this tree performs (`nilop` and `appop`
  have different `Split` types, so there is nothing to factor through).
-}
open import Cubical.Foundations.Prelude

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Theories.Monoid
import ISA.Machine

module ISA.Pass (Fib   : Fibered monoidSig ℓ-zero ℓ-zero)
                (Instr : Type₀)
                (step  : Instr → ISA.Machine.Cmd Fib) where

open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Reindex.Base
open import TheoryGrammar.Reindex.Pass

-- the ISA layer: `Cmd`, `cmdFib`, `sem`, `strInterp`, and the three
-- homomorphism lemmas
open import ISA.Program Fib Instr step public

-- ==================================================================
-- §1  THE TWO THEORIES, BUNDLED.
--
-- Same signature, different promodels, DIFFERENT LEVELS -- which is
-- the point.  `cmdTheory` sits one universe above `asmTheory`, and
-- nothing below has to apologise for it.
-- ==================================================================

asmTheory : Theory ℓ-zero ℓ-zero ℓ-zero ℓ-zero ℓ-zero
asmTheory = theory monoidSig PT.strFib

cmdTheory : Theory ℓ-zero ℓ-zero ℓ-zero (ℓ-suc ℓ-zero) (ℓ-suc ℓ-zero)
cmdTheory = theory monoidSig cmdFib

-- ==================================================================
-- §2  THE CARRIER MAP.  `sem`, and nothing else.
-- ==================================================================

semOver : ReindexOver (idSigMor monoidSig) PT.strFib cmdFib
semOver .homO _ p = sem p

-- ==================================================================
-- §3  PRESERVATION AT EVERY OPERATION.
--
-- Both fields at `appop` are `ISA.Interp`'s lemmas VERBATIM -- the
-- generalisation over the signature morphism added no coercion,
-- because `idSigMor`'s `resEq` and `sortEq` are `Eq.refl`.  At `nilop`
-- the arity is `⊥`, so `homPartsO` has nothing to prove.
-- ==================================================================

semPresO : (o : MonOp) → SplitPresAtOver semOver o
semPresO appop .homSplitO m sp   = homSplit strInterp m sp
semPresO appop .homPartsO m sp b = homParts strInterp m sp b
semPresO nilop .homSplitO m sp   = homNilSplit strInterp m sp
semPresO nilop .homPartsO m sp ()

-- ==================================================================
-- §4  THE THEOREM.
--
-- "The semantics of an instruction set is sound" IS "the semantics is
-- a pass".  Everything on the right-hand side was already proved; what
-- is new is that the statement is now in the currency chains are built
-- from.
-- ==================================================================

semPass : Pass asmTheory cmdTheory
semPass .sigOf  = idSigMor monoidSig
semPass .mapOf  = semOver
semPass .presOf = semPresO

-- ... and it is a chain of length one, so it composes with anything
-- landing in `asmTheory`
semChain : Chain asmTheory asmTheory
semChain = done
