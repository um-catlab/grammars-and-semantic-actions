{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  IS A CONTROL-FLOW GRAPH A PROMODEL?

  `ISA.Control.Base` put `if` and `while` in the COMMAND monoid.  That
  leaves the question the ISA layer actually cares about: what happens to
  PROGRAM TEXT?  `ISA.Program` makes it the free monoid on the
  instruction set, and a free monoid has no branching.  So does control
  flow force program text out of `Strings`, i.e. off the promodel?

  ANSWER, and it is sharper than expected:

      STRUCTURED control flow does NOT leave the free monoid.
      It enlarges the ALPHABET by a fixed point.

  ------------------------------------------------------------------
  THE FIXED POINT
  ------------------------------------------------------------------

      Atom  ≅  Instr ⊎ (Test × Block × Block) ⊎ (Test × Block)
      Block =  List Atom

  `Block` is `List Atom`, so it is `TheoryGrammar.Instances.Strings` at
  the alphabet `Atom`, so `⊗ˢ appop` at it IS still sequential
  composition, and `ISA.Program` applies VERBATIM -- it is instantiated
  below, not re-derived.  `seq`, `seq++`, `seq∷`, `nilRule`,
  `consequenceᵖ`, `frameRule`, `local-sem` all arrive unchanged, and the
  one induction the whole ISA layer owes (`homSplit3`) is the one
  `ISA.Program` already did.

  What IS new is only that `Atom` is defined by a fixed point that
  mentions `Block`, so `semAtom`/`semBlock` are MUTUAL.  That is the
  entire cost, and it buys `ifRule` and `whileRuleB` below, which are
  `instrRule` composed with `ISA.Control.Base`'s `condRule` /
  `whileRuleInd`.  A one-atom program is an instruction: the rule for a
  compound statement is the rule for a LETTER.

  This is the structured program theorem, read as a statement about
  alphabets: `while`/`if`/`;` suffice because they close the alphabet
  under a functor whose fixed point exists.

  ------------------------------------------------------------------
  AND WHERE IT STOPS: A GENERAL CFG IS NOT ONE OF THESE
  ------------------------------------------------------------------

  The construction above is not "a CFG is a promodel"; it is "the
  REDUCIBLE, single-entry-single-exit ones are, because they are a free
  monoid on SESE regions".  The obstruction for the rest is exactly
  localisable, and it is worth stating because it is the same fact that
  made `while` need `löb`:

      `⊗ˢ appop` at a free monoid says the cut between the two factors
      is crossed EXACTLY ONCE.

  A splitting `Split appop p` of program text is `p = p₁ ++ p₂`, and the
  Hoare rule it induces (`ISA.Interp.seq`) threads a SINGLE midcondition
  `R` through a SINGLE crossing.  A back edge from inside `p₂` into `p₁`
  crosses that cut once per iteration.  So:

    * a loop is precisely a piece of program text that is NOT a
      splitting -- which is why `ifC` (one crossing, two alternatives)
      is free from the additives while `While` needs a fixed point;

    * a graph with two entries into a loop body (an irreducible CFG, e.g.
      a jump into the middle of a block) has no cut that is crossed once
      at all, so it is not `p₁ ++ p₂` for ANY `p₁`, `p₂`, for ANY
      definition of `++` -- there is no candidate `Split` to propose.

  The honest formulation is therefore NEGATIVE, and it is a statement
  about the INTERPRETATION rather than about the carrier.  Any type
  whatever is a promodel over `monoidSig` (take `Split o m = ⊥`), so
  "are CFGs a promodel?" is vacuous; the content is in
  `ISA.Interp.Interp`, which demands

      ⟦ p ⟧  ⊑  ⟦ p₁ ⟧ ⨟ ⟦ p₂ ⟧

  and THAT is what a back edge across the cut refutes: a run of `p` may
  re-enter `p₁`, and no element of `⟦ p₁ ⟧ ⨟ ⟦ p₂ ⟧` does.  So the
  negative result is: for an irreducible CFG there is no nontrivial
  splitting-preserving interpretation, and hence no Hoare sequencing
  rule -- which is precisely why compilers reduce irreducible graphs
  (node splitting) before reasoning about them, and why the structured
  fragment below is the one that fits.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1: the `Atom`/`Block` fixed point and the mutual `semAtom` /
  `semBlock` -- the machine's definition, exactly as `ISA.Toy.toyStep`
  is.  Everything else is a composite, and every Hoare rule is imported
  rather than proved.
-}
open import Cubical.Foundations.Prelude

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Theories.Monoid
import ISA.Machine
import ISA.Control.Base

module ISA.Control.Blocks (Fib   : Fibered monoidSig ℓ-zero ℓ-zero)
                          (Instr : Type₀)
                          (step  : Instr → ISA.Machine.Cmd Fib) where

open import Cubical.Data.List using (List; []; _∷_; _++_)
open import Cubical.Data.Bool using (Bool; true; false)

-- the control-flow layer, QUALIFIED: it re-exports `ISA.Machine`, and so
-- does `ISA.Program` below, so exactly one of them may be opened.
private module C = ISA.Control.Base Fib

-- ==================================================================
-- THE ALPHABET, AS A FIXED POINT.  PRIMITIVE (phase 1).
-- ==================================================================

data Atom : Type₀

Block : Type₀
Block = List Atom

data Atom where
  instr : Instr → Atom
  ifA   : C.Test → Block → Block → Atom
  whA   : C.Test → Block → Atom

-- ==================================================================
-- THE MACHINE.  PRIMITIVE (phase 1): mutual, because the alphabet is.
-- `semBlock` has EXACTLY the two clauses of `ISA.Program.sem`, which is
-- what makes the instantiation below legitimate.
-- ==================================================================

semAtom  : Atom  → ISA.Machine.Cmd Fib
semBlock : Block → ISA.Machine.Cmd Fib

semAtom (instr i)     = step i
semAtom (ifA t b₁ b₂) = C.ifC t (semBlock b₁) (semBlock b₂)
semAtom (whA t b)     = C.While t (semBlock b)

semBlock []      = C.skip
semBlock (a ∷ b) = C._⨟_ (semAtom a) (semBlock b)

-- ==================================================================
-- ... AND THE FREE-MONOID LAYER, INSTANTIATED.  Not re-derived: every
-- Hoare rule about sequencing, the empty program, consequence and
-- framing arrives from `ISA.Program` at the alphabet `Atom`.
-- ==================================================================

open import ISA.Program Fib Atom semAtom public

-- `sem` (from `ISA.Program`) and `semBlock` are the same two clauses, so
-- they agree on every block; on a CONCRETE block both sides reduce and
-- the identification is `refl`.  The general statement is the same
-- two-clause induction, stated here once so no use site repeats it.
sem≡ : (b : Block) → sem b ⊑ semBlock b
sem≡ []      h h' r = r
sem≡ (a ∷ b) h h' (h₁ , ra , rb) = h₁ , ra , sem≡ b h₁ h' rb

sem≡' : (b : Block) → semBlock b ⊑ sem b
sem≡' []      h h' r = r
sem≡' (a ∷ b) h h' (h₁ , ra , rb) = h₁ , ra , sem≡' b h₁ h' rb

-- ==================================================================
-- THE CONTROL-FLOW VOCABULARY, re-exported.  None of these names is
-- exported by `ISA.Program`, so this is unambiguous.
-- ==================================================================

open C public
  using ( Test; Tst; assume; sumC; _⊔c_; ifBody; ifC; While
        ; wh-stop; wh-step; while-fold; while-unfold
        ; testFires; decideT; wp-sum→; wp-sum←; wp-assume→; wp-assume←
        ; choiceRule; condRule; whileRuleInd; noDescent )

-- the variant layer (route B) is a module, so it is re-exported as one
module Variant = C.Variant

-- ==================================================================
-- THE RULES FOR A COMPOUND STATEMENT.
--
-- Both are `instrRule` -- the rule for a one-LETTER program -- composed
-- with the command-level rule.  There is nothing else in them, and that
-- is the point: a compound statement is a letter.
-- ==================================================================

ifRule : {P Q : Gr} (t : Test) (b₁ b₂ : Block)
       → ⟪ P & Tst t true  ⟫ semBlock b₁ ⟪ Q ⟫
       → ⟪ P & Tst t false ⟫ semBlock b₂ ⟪ Q ⟫
       → ⟪ P ⟫ ifA t b₁ b₂ ∷ [] ⟪ Q ⟫ᵖ
ifRule t b₁ b₂ t₁ t₂ =
  instrRule (ifA t b₁ b₂) (condRule t (semBlock b₁) (semBlock b₂) t₁ t₂)

whileRuleB : (Inv : Gr) (t : Test) (b : Block)
           → ⟪ Inv & Tst t true ⟫ semBlock b ⟪ Inv ⟫
           → ⟪ Inv ⟫ whA t b ∷ [] ⟪ Inv & Tst t false ⟫ᵖ
whileRuleB Inv t b bt =
  instrRule (whA t b) (whileRuleInd t (semBlock b) Inv bt)

-- and the rule for a plain instruction is `instrRule` with nothing
-- around it, since `semAtom (instr i) = step i` definitionally
atomRule : {P Q : Gr} (i : Instr) → ⟪ P ⟫ step i ⟪ Q ⟫ → ⟪ P ⟫ instr i ∷ [] ⟪ Q ⟫ᵖ
atomRule i = instrRule (instr i)
