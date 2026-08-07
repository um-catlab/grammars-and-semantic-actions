{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  PROGRAM TEXT IS THE FREE MONOID ON THE INSTRUCTION SET.

  `ISA.Interp` derived the Hoare rules from an abstract splitting-
  preserving interpretation.  This file supplies the standard one: take
  program text to be the FREE monoid `List Instr`, which is
  `TheoryGrammar.Instances.Strings` at an alphabet of instructions, and
  extend a per-instruction semantics `step : Instr → Cmd` along the
  universal property.

  Nothing about `Strings` is re-derived.  `PT.strFib` already has

      Split appop p = Σ u, Σ v, Split3 u v p

  -- "the ways of writing `p` as `u ++ v`" -- and `Split3` is exactly the
  inductive family a proof about concatenation wants to recurse on.  So
  `⊗ˢ appop` at `PT.strFib` IS sequential composition of program text,
  and the Hoare rule for it is `ISA.Interp.seq`.

  ------------------------------------------------------------------
  THE ONE INDUCTION IN THE DEVELOPMENT
  ------------------------------------------------------------------

  `homSplit3` is it:

      Split3 p q r  →  ⟦ r ⟧ ⊑ ⟦ p ⟧ ⨟ ⟦ q ⟧

  two clauses, each a rebracketing of a Σ.  It says precisely that
  `⟦_⟧` is a monoid homomorphism, and it is the ONLY thing this file
  owes `ISA.Interp`.  Everything Hoare-shaped -- sequencing, the empty
  program, consequence, framing -- comes back for free.

  It is worth stating the accounting explicitly, because it is the point
  of the exercise:

      Hoare sequencing rule proved by hand:      0 lines
      monoid homomorphism proved by induction:   2 clauses
      rule derived from the homomorphism:        1 composite (ISA.Interp.seq)

  The `nil` clause is `⟦ v ⟧ ⊑ skip ⨟ ⟦ v ⟧` -- a unit law.  The `cons`
  clause is `(step c ⨟ ⟦ w ⟧) ⊑ ((step c ⨟ ⟦ u ⟧) ⨟ ⟦ v ⟧)` -- an
  associativity.  So even the induction is not about Hoare logic; it is
  the two monoid laws, once each.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1: `sem` (structural recursion over the free monoid, i.e. the
  universal property), `homSplit3`, `semNil`.  All three are marked.
  Everything after `strInterp` is a composite.
-}
open import Cubical.Foundations.Prelude

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Theories.Monoid
import ISA.Machine

module ISA.Program (Fib   : Fibered monoidSig ℓ-zero ℓ-zero)
                   (Instr : Type₀)
                   (step  : Instr → ISA.Machine.Cmd Fib) where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit
open import Cubical.Data.List using (List; []; _∷_; _++_)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

import TheoryGrammar.Instances.Strings.Base
module PT = TheoryGrammar.Instances.Strings.Base Instr

open import ISA.Interp Fib PT.strFib public

-- ==================================================================
-- Program text.
-- ==================================================================

Program : Type₀
Program = PT.String                       -- = List Instr

-- PRIMITIVE (phase 1): the extension of `step` along the universal
-- property of the free monoid.  This is the ONLY recursion over a
-- program in the development.
sem : Program → Cmd
sem []      = skip
sem (i ∷ p) = step i ⨟ sem p

-- ==================================================================
-- PRIMITIVE (phase 1): `sem` IS A MONOID HOMOMORPHISM.
--
-- `nil`  is the left unit law of `⨟`;
-- `cons` is its associativity.
--
-- Nothing about weakest preconditions, assertions or Hoare triples
-- appears -- and this is the whole of what `ISA.Interp` asks for.
-- ==================================================================

homSplit3 : {p q r : Program} → PT.Split3 p q r → sem r ⊑ sem p ⨟ sem q
homSplit3 PT.nil        h h'  d                = h , Eq.refl , d
homSplit3 (PT.cons s) h h'' (h₁ , sc , rest) =
  ih .fst , (h₁ , sc , ih .snd .fst) , ih .snd .snd
  where ih = homSplit3 s h₁ h'' rest

-- PRIMITIVE (phase 1): ... and it sends the unit to the unit.
semNil : (r : Program) → PT.IsNil r → sem r ⊑ skip
semNil []      _  h h' e = e
semNil (i ∷ p) ()

-- ==================================================================
-- The interpretation, packaged.  `left· r (u , v , s)` reduces to `u`
-- and `right·` to `v`, so the fields are the two lemmas verbatim.
-- ==================================================================

strInterp : Interp
Interp.⟦_⟧    strInterp             = sem
Interp.⟦⟧-⨟   strInterp r (u , v , s) = homSplit3 s
Interp.⟦⟧-nil strInterp r sp        = semNil r sp

-- EVERY HOARE RULE, for free.
open Rules strInterp public

-- ==================================================================
-- The list-shaped spellings of the rules.  Each is `seq` at a chosen
-- splitting -- `splitAll p q : Split3 p q (p ++ q)` is the canonical one.
-- ==================================================================

sem-++ : (p q : Program) → sem (p ++ q) ⊑ sem p ⨟ sem q
sem-++ p q = homSplit3 (PT.splitAll p q)

seq++ : {P R Q : Gr} (p q : Program)
      → ⟪ P ⟫ p ⟪ R ⟫ᵖ → ⟪ R ⟫ q ⟪ Q ⟫ᵖ → ⟪ P ⟫ p ++ q ⟪ Q ⟫ᵖ
seq++ p q = seq (p ++ q) (p , q , PT.splitAll p q)

-- the head/tail form, which is what a program is actually written in
seq∷ : {P R Q : Gr} (i : Instr) (p : Program)
     → ⟪ P ⟫ i ∷ [] ⟪ R ⟫ᵖ → ⟪ R ⟫ p ⟪ Q ⟫ᵖ → ⟪ P ⟫ i ∷ p ⟪ Q ⟫ᵖ
seq∷ i p = seq++ (i ∷ []) p

-- a one-instruction program is its instruction (`sem (i ∷ []) = step i ⨟ skip`)
instrRule : {P Q : Gr} (i : Instr) → ⟪ P ⟫ step i ⟪ Q ⟫ → ⟪ P ⟫ i ∷ [] ⟪ Q ⟫ᵖ
instrRule {Q = Q} i t = seqCmd (step i) skip t (skipRule Q)

emptyRule : (Q : Gr) → ⟪ Q ⟫ [] ⟪ Q ⟫ᵖ
emptyRule Q = nilRule Q [] tt

-- ==================================================================
-- LOCALITY IS COMPOSITIONAL: if every instruction is local then every
-- program is, by the same two monoid laws.  So the frame rule for
-- programs needs a hypothesis only at the instruction set.
-- ==================================================================

local-sem : ((i : Instr) → Local (step i)) → (p : Program) → Local (sem p)
local-sem ls []      = local-skip
local-sem ls (i ∷ p) = local-⨟ (step i) (sem p) (ls i) (local-sem ls p)
