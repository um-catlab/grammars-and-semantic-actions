{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  AN INTERPRETATION IS A MORPHISM OF THEORIES -- LITERALLY.

  `ISA.Interp` builds the Hoare rules from a record whose two fields are,
  in its own words, "exactly `CarrierMap.SplitPresAt` at `PFib → cmdFib`".
  Both `ISA.Interp` and `ISA.Machine` then add a caveat:

      "The record from `CarrierMap` is not literally instantiated because
       `Reindex` forces both `Fibered` into the SAME universe levels, and
       `Cmd = Res → Res → Type₀` sits one level above `Res`."

  THAT CAVEAT IS STALE.  `CarrierMap.Reindex` is now

      Reindex : Fibered σ ℓX ℓP → Fibered σ ℓX' ℓP' → Type _

  -- two independent carrier levels, two independent splitting levels --
  and its own header records why ("the glued `Fibered` of
  `TheoryGrammar.Gluing` has a carrier at the max of its two factors'").
  So the identification can be made, and this file makes it:

      semReindex : Reindex PFib cmdFib
      semPres    : (o : MonOp) → SplitPresAt semReindex o

  Nothing is reproved.  `ISA.Interp.homSplit`/`homParts`/`homNilSplit`
  are the three fields verbatim; this file only puts them in the record
  they were written to fill.

  WHY THAT IS WORTH DOING: THE SEQUENCING RULE BECOMES A TRANSPORT.

  Once `sem` is a `Reindex`, the generic machinery of `CarrierMap.Along`
  applies, and the Hoare sequencing rule factors into two moves that were
  previously fused:

      pull      -- a predicate on COMMANDS becomes a predicate on
                   PROGRAM TEXT.  `pull (Tri P Q) r` is definitionally
                   `⟪ P ⟫ r ⟪ Q ⟫ᵖ`; no lemma, no coercion.

      push⊗     -- split preservation, i.e. `sem` is a monoid
                   homomorphism, as a TERM.

      pullTerm  -- and then EVERY command-level derivation is a
                   program-level derivation, with no hypothesis at all.

  So `seqᵐ` below is

      pullTerm seqTri  ∘g  push⊗ appop (semPres appop)

  where `seqTri` is a term of the COMMAND theory -- it mentions no
  program, no instruction, no list.  `seqAgrees` proves by `refl` that
  this is the same term as `ISA.Interp.Rules.seq`.

  That is the shape the whole pipeline is supposed to have and this is
  the first place it is exhibited end to end: a rule proved once at the
  target theory, transported to the source theory by `pullTerm`, with
  `push⊗` supplying the one thing that is not free.

  PHASE.  Phase 1: nothing.  Every definition below is a record
  instantiation or a `⊢`-composite.
-}
open import Cubical.Foundations.Prelude

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Theories.Monoid

module TheoryGrammar.Machine.Morphism
  (Fib  : Fibered monoidSig ℓ-zero ℓ-zero)      -- machine resource
  (PFib : Fibered monoidSig ℓ-zero ℓ-zero)      -- program text
  where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.RulesFib
open import TheoryGrammar.CarrierMap

import ISA.Machine
import ISA.Interp

module M = ISA.Machine Fib
module I = ISA.Interp Fib PFib

-- the combinator layer of the COMMAND theory (the resource theory's own
-- is already in scope via `ISA.Machine`, under `M`)
module C = RulesF M.cmdFib

Prog : Type₀
Prog = PFib .carrier tt

module _ (Int : I.Interp) where

  open I.Interp Int using (⟦_⟧; ⟦⟧-⨟; ⟦⟧-nil)
  module R = I.Rules Int

  -- THE MORPHISM.

  semReindex : Reindex PFib M.cmdFib
  semReindex .hom _ = ⟦_⟧

  -- The three fields are `ISA.Interp`'s, unchanged.
  semPres : (o : MonOp) → SplitPresAt semReindex o
  semPres appop .homSplit     = I.homSplit    Int
  semPres appop .homParts     = I.homParts    Int
  semPres nilop .homSplit     = I.homNilSplit Int
  semPres nilop .homParts r sp ()

  module A = Along semReindex

  -- A PREDICATE ON COMMANDS, AND ITS PULLBACK. `Tri P Q` is a type of the
  -- COMMAND theory: a family over `Cmd`.

  Tri : M.Gr → M.Gr → M.Cmd → Type₀
  Tri P Q c = M.⟪_⟫_⟪_⟫ P c Q

  pullTri : (P Q : M.Gr) (r : Prog) → A.pull (Tri P Q) r ≡ R.⟪_⟫_⟪_⟫ᵖ P r Q
  pullTri P Q r = refl

  -- THE SEQUENCING RULE, AT THE COMMAND THEORY. Three combinators: `⊗ˢ-E`
  -- to consume the factorisation, `seqCmd` (which is `wp` inverting `⨟`),
  -- `refine` (which is `wp` being contravariant).

  Tri₂ : M.Gr → M.Gr → M.Gr → Bool → M.Cmd → Type₀
  Tri₂ P Md Q = boolΠ {M = λ _ → M.Cmd → Type₀} (Tri P Md) (Tri Md Q)

  seqTri : (P Md Q : M.Gr) → C.⊗ˢ appop (Tri₂ P Md Q) C.⊢ Tri P Q
  seqTri P Md Q =
    C.⊗ˢ-E appop {A = Tri₂ P Md Q}
      (λ c sp k → M.refine (sp .snd .snd)
                    (M.seqCmd (sp .fst) (sp .snd .fst) (k true) (k false)))

  -- ... AND THEREFORE AT PROGRAM TEXT, BY TRANSPORT. pullTerm (a command-
  -- level derivation) ∘g push⊗ (the morphism) Read the type: the source is
  -- "the program splits, and each half satisfies its triple"; the target
  -- is `⟪ P ⟫ r ⟪ Q ⟫ᵖ`.

  module P = RulesF PFib

  seqᵐ : (P Md Q : M.Gr)
       → P.⊗ˢ appop (λ a → A.pull (Tri₂ P Md Q a)) P.⊢ A.pull (Tri P Q)
  seqᵐ P Md Q =
    A.pullTerm (seqTri P Md Q) P.∘g
    A.push⊗ appop (semPres appop) {B = Tri₂ P Md Q}

  -- AND IT IS THE SAME RULE. `refl`.

  seqAgrees : (P Md Q : M.Gr) (r : Prog) (sp : PFib .Split appop r)
              (t₁ : R.⟪_⟫_⟪_⟫ᵖ P (I.left· r sp) Md)
              (t₂ : R.⟪_⟫_⟪_⟫ᵖ Md (I.right· r sp) Q)
            → seqᵐ P Md Q r
                (sp , boolΠ {M = λ a → A.pull (Tri₂ P Md Q a)
                                           (PFib .parts appop r sp a)} t₁ t₂)
              ≡ R.seq r sp t₁ t₂
  seqAgrees P Md Q r sp t₁ t₂ = refl
