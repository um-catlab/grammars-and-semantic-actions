{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE HOMOMORPHISM, AND THE HOARE RULES THAT FALL OUT OF IT.

  This is the file the whole exercise is about, and it contains no
  induction, no list, no instruction and no heap.  It takes

    * a RESOURCE promodel `Fib`   (machine state, splitting disjointly)
    * a PROGRAM-TEXT promodel `PFib`  (program text, splitting as
      concatenation -- for the free monoid this is `Strings`, but nothing
      below knows that)
    * an interpretation `⟦_⟧ : Prog → Cmd` PRESERVING SPLITTINGS,

  and derives the Hoare rules for sequencing, for the empty program and
  for framing.

  ------------------------------------------------------------------
  WHAT "PRESERVING SPLITTINGS" MEANS HERE
  ------------------------------------------------------------------

  `ISA.Machine.cmdFib` makes commands a promodel whose `appop`-splittings
  are lax factorisations `c ⊑ c₁ ⨟ c₂`.  A map of promodels over the
  monoid signature is `TheoryGrammar.CarrierMap.Reindex` together with
  `SplitPresAt` at each operation:

      homSplit : Split o m → Split' o (⟦ m ⟧)
      homParts : parts' o ⟦ m ⟧ (homSplit sp) a  Eq.≡  ⟦ parts o m sp a ⟧

  Read at `PFib → cmdFib` and `o = appop`, that is exactly

      ⟦ r ⟧  ⊑  ⟦ r₁ ⟧ ⨟ ⟦ r₂ ⟧      whenever r splits as r₁ · r₂,

  i.e. `⟦_⟧` IS A MONOID HOMOMORPHISM (laxly, which is all a promodel
  ever asserts).  `Interp` below takes that as its field, and
  `asSplitPres` then rebuilds the literal `homSplit`/`homParts` pair, with
  `homParts` proved by `boolΠ Eq.refl Eq.refl` -- so the identification
  is definitional up to the arity's missing η, and nothing else.

  (The record from `CarrierMap` is not literally instantiated because
  `Reindex` forces both promodels into the SAME universe levels, and
  `Cmd = Res → Res → Type₀` sits one level above `Res`.  The obstruction
  is bookkeeping, not mathematics.)

  ------------------------------------------------------------------
  AND THEN THE RULE
  ------------------------------------------------------------------

      seq = wp-⊑ (⟦⟧-⨟ r sp) Q ∘g seqCmd ⟦ r₁ ⟧ ⟦ r₂ ⟧ t₁ t₂

  Unfolded: `seqCmd` is `wp` being a monoid antihomomorphism
  (`wp (c ⨟ d) ≅ wp c ∘ wp d`, both directions `refl`), and `wp-⊑` is
  `wp` being contravariant.  So the Hoare sequencing rule is the
  composite of

      (⟦_⟧ is a monoid hom)  ∙  (wp is contravariant)  ∙  (wp inverts ⨟)

  and there is nothing else in it.  In particular the rule is proved ONCE
  here, for every instruction set, every resource model and every
  presentation of program text at the same time.  See `ISA.Program` for
  what is left over: exactly the proof that the free-monoid
  interpretation IS a homomorphism, which is one three-line induction.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Everything in this file is phase 2.  There is not a single pattern
  match outside `respellHom`, which is the standard `boolΠ` respelling
  (compare `Heap.Connectives.respell`) and exists only because `Bool` has
  no η.
-}
open import Cubical.Foundations.Prelude

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Theories.Monoid

module ISA.Interp (Fib  : Fibered monoidSig ℓ-zero ℓ-zero)
                  (PFib : Fibered monoidSig ℓ-zero ℓ-zero) where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import ISA.Machine Fib public

-- ==================================================================
-- Program text, abstractly: whatever `PFib` says it is.
-- ==================================================================

Prog : Type₀
Prog = PFib .carrier tt

-- the two projections of a program-text splitting, named
left· : (r : Prog) → PFib .Split appop r → Prog
left· r sp = PFib .parts appop r sp true

right· : (r : Prog) → PFib .Split appop r → Prog
right· r sp = PFib .parts appop r sp false

-- ==================================================================
-- AN INTERPRETATION: a splitting-preserving map of promodels
-- `PFib → cmdFib`.
-- ==================================================================

record Interp : Type₁ where
  field
    ⟦_⟧ : Prog → Cmd

    -- THE MONOID HOMOMORPHISM.  Splitting program text gives a
    -- factorisation of the command.  Lax, as every promodel splitting is.
    ⟦⟧-⨟ : (r : Prog) (sp : PFib .Split appop r)
         → ⟦ r ⟧ ⊑ ⟦ left· r sp ⟧ ⨟ ⟦ right· r sp ⟧

    -- ... and it sends the unit to the unit.
    ⟦⟧-nil : (r : Prog) → PFib .Split nilop r → ⟦ r ⟧ ⊑ skip

-- ==================================================================
-- That record really is `CarrierMap.SplitPresAt` at `PFib → cmdFib`.
-- ==================================================================

module _ (I : Interp) where

  open Interp I

  homSplit : (r : Prog) → PFib .Split appop r → cmdFib .Split appop ⟦ r ⟧
  homSplit r sp = ⟦ left· r sp ⟧ , ⟦ right· r sp ⟧ , ⟦⟧-⨟ r sp

  -- `Eq.refl` at each constructor of the arity; stuck only at a variable
  -- `a`, which is exactly the `Bool`-has-no-η tax.
  homParts : (r : Prog) (sp : PFib .Split appop r) (a : Bool)
           → cmdFib .parts appop ⟦ r ⟧ (homSplit r sp) a
             Eq.≡ ⟦ PFib .parts appop r sp a ⟧
  homParts r sp =
    boolΠ {M = λ a → cmdFib .parts appop ⟦ r ⟧ (homSplit r sp) a
                     Eq.≡ ⟦ PFib .parts appop r sp a ⟧}
          Eq.refl Eq.refl

  homNilSplit : (r : Prog) → PFib .Split nilop r → cmdFib .Split nilop ⟦ r ⟧
  homNilSplit r sp = lift (⟦⟧-nil r sp)

-- ==================================================================
-- THE HOARE RULES.  All of them are composites.
-- ==================================================================

module Rules (I : Interp) where

  open Interp I public

  -- a triple about PROGRAM TEXT
  ⟪_⟫_⟪_⟫ᵖ : Gr → Prog → Gr → Type₀
  ⟪ P ⟫ r ⟪ Q ⟫ᵖ = ⟪ P ⟫ ⟦ r ⟧ ⟪ Q ⟫

  -- ================================================================
  -- SEQUENCING.  THE RESULT.
  --
  --   homomorphism  ∙  wp contravariant  ∙  wp inverts ⨟
  --
  -- No induction.  No program.  No case analysis.
  -- ================================================================

  seq : {P R Q : Gr} (r : Prog) (sp : PFib .Split appop r)
      → ⟪ P ⟫ left·  r sp ⟪ R ⟫ᵖ
      → ⟪ R ⟫ right· r sp ⟪ Q ⟫ᵖ
      → ⟪ P ⟫ r ⟪ Q ⟫ᵖ
  seq {Q = Q} r sp t₁ t₂ =
    wp-⊑ (⟦⟧-⨟ r sp) Q ∘g seqCmd ⟦ left· r sp ⟧ ⟦ right· r sp ⟧ t₁ t₂

  -- ================================================================
  -- THE EMPTY PROGRAM.  Same shape, one operation down.
  -- ================================================================

  nilRule : (Q : Gr) (r : Prog) → PFib .Split nilop r → ⟪ Q ⟫ r ⟪ Q ⟫ᵖ
  nilRule Q r sp = wp-⊑ (⟦⟧-nil r sp) Q ∘g skipRule Q

  -- ================================================================
  -- CONSEQUENCE and FRAMING, inherited from the command layer.
  -- ================================================================

  consequenceᵖ : {P P' Q Q' : Gr} (r : Prog)
               → P' ⊢ P → Q ⊢ Q' → ⟪ P ⟫ r ⟪ Q ⟫ᵖ → ⟪ P' ⟫ r ⟪ Q' ⟫ᵖ
  consequenceᵖ r = consequence ⟦ r ⟧

  frameRule : {P Q : Gr} (R : Gr) (r : Prog) → Local ⟦ r ⟧
            → ⟪ P ⟫ r ⟪ Q ⟫ᵖ → ⟪ P ∗ R ⟫ r ⟪ Q ∗ R ⟫ᵖ
  frameRule R r = frameRuleCmd R ⟦ r ⟧
