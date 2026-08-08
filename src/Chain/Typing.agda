{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  TASK 1: WIRING `LinTyped` INTO THE RUST CHAIN -- WHAT LINES UP, WHAT
  DOES NOT, AND THE OBSTRUCTION THAT DECIDES THE ANSWER.

  The handoff asks whether a translation is needed between `LinTyped`'s
  `Ctx = List (Maybe Ty)` and `LinLam`'s `Usage = List Bool`.  It is,
  and that is the SMALLER of two mismatches.  The larger one is in the
  TERMS, and it decides how the pass can be wired at all.

  ------------------------------------------------------------------
  §1  THE TWO MISMATCHES.

  CONTEXTS.  `Ctx` is `Usage` with a type in each live slot, so there is
  a total erasure `usageOf = map is-just` and NO section: `notInjective`
  exhibits two contexts with one usage.  `Ctx` REFINES `Usage`; it is
  not isomorphic to it, and any pass going the other way must invent
  types.

  TERMS.  `LinLam`'s de Bruijn terms are `dvar | dapp | dlam`;
  `LinTyped`'s `Raw` is `var | app | lam | ann`.  The embedding is
  total and obvious -- and it never produces an `ann`, which
  `embedNoAnn` proves by induction rather than by inspection.

  ------------------------------------------------------------------
  §2  AND THAT IS THE OBSTRUCTION.  `LinTyped` is BIDIRECTIONAL:

      SynStep Γ = VarG (Look Γ) ⊕ (SynApp Γ ⊕ SynAnn Γ)

  -- there is no `lam` rule in SYNTHESIS mode, by design.  So an
  annotation-free lambda synthesises nothing, and since the chain's
  surface alphabet is `{x, y, λx., λy.}` with no type syntax, EVERY
  term the front end produces is annotation-free.

  The consequence is sharper than "synthesis is unavailable", and §4
  pins it: the chain's own flagship term `(λx.x)(λx.x)` -- which
  `Chain.Pipeline` proves is what `"λx. x λy. y"` compiles to --
  neither synthesises NOR checks, at any type.  Check mode handles a
  LAMBDA in head position and an application must go through synthesis,
  which dies at the bare function.

  So `LinTyped` cannot be wired in as a pass over the front end's output
  as it stands.  Three honest options, and this file delivers the first
  and specifies the third:

    (a) CHECK MODE AT A SUPPLIED GOAL TYPE.  Sound, available today, and
        bounded: it accepts terms whose head is a lambda (`idLin`) and
        rejects applications (`selfApp`).  §3.
    (b) Extend the surface syntax with annotations -- a change to
        `Lambda.Parse`, out of scope here.
    (c) AN ANNOTATION-INSERTING PASS.  §5 measures exactly what it owes:
        ONE annotation, at the FUNCTION of each application.  Annotating
        the function alone is enough -- the argument is then CHECKED
        against the domain -- and `fnOnly` synthesises `o ⊸ᵗ o` on the
        nose.  That is a complete specification for the pass; writing it
        is elaboration and is not attempted here.

  ------------------------------------------------------------------
  PHASE.  `embedS`/`usageOf`/`headTy` are PRIMITIVES: carrier maps
  between two theories over DIFFERENT signatures (`λSig` against
  `LinTyped`'s three-sorted `TSig`), so they are the same kind of escape
  as `Chain.Elab.stripL` and belong to the task-2 list, not to phase 2.
  Everything from §3 down is a term.
-}
open import Cubical.Foundations.Prelude

module Chain.Typing where

open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Empty as E using ()
open import Cubical.Data.List using (List; []; _∷_; map)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma using (_×_; _,_)
open import Cubical.Data.Unit using (Unit; tt)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.SemanticAction using (passes; _↦_; _at_)
open import TheoryGrammar.Instances.LinTyped

import TheoryGrammar.Instances.LinLam.Syntax as L
import TheoryGrammar.Instances.LinLam.Check  as C

-- ==================================================================
-- §1  THE TRANSLATIONS.  Both PRIMITIVE -- see the header on phase.
-- ==================================================================

-- TERMS.  `Check.Skel` is already the untyped de Bruijn skeleton both
-- `DBTm` and `Tm` erase to, so the embedding is written once, there.
embedS : C.Skel → Raw
embedS (C.svar i)   = var i
embedS (C.sapp f a) = app (embedS f) (embedS a)
embedS (C.slam b)   = lam (embedS b)

-- the front end's output, embedded
embedTm : {u : L.Usage} → L.Tm u → Raw
embedTm t = embedS (C.eraseS t)

-- CONTEXTS.  The erasure exists; the section does not.
isJust : Maybe Ty → Bool
isJust (just _) = true
isJust nothing  = false

usageOf : Ctx → L.Usage
usageOf = map isJust

headTy : Ctx → Ty
headTy (just A ∷ _) = A
headTy _            = base

ctxA ctxB : Ctx
ctxA = just base ∷ []
ctxB = just (base ⊸ᵗ base) ∷ []

-- one usage, two contexts: `Ctx` refines `Usage` and does not embed it
sameUsage : usageOf ctxA ≡ usageOf ctxB
sameUsage = refl

notInjective : ctxA ≡ ctxB → E.⊥
notInjective p = base≢lol base base (Eq.pathToEq (cong headTy p))

-- ==================================================================
-- §2  THE EMBEDDING NEVER ANNOTATES.  A recursive `Unit`/`⊥` predicate,
-- so it computes, and an induction rather than an inspection.
-- ==================================================================

NoAnn : Raw → Type₀
NoAnn (var _)   = Unit
NoAnn (app f a) = NoAnn f × NoAnn a
NoAnn (lam b)   = NoAnn b
NoAnn (ann _ _) = E.⊥

embedNoAnn : (sk : C.Skel) → NoAnn (embedS sk)
embedNoAnn (C.svar i)   = tt
embedNoAnn (C.sapp f a) = embedNoAnn f , embedNoAnn a
embedNoAnn (C.slam b)   = embedNoAnn b

-- ... hence for every term the front end can produce
tmNoAnn : {u : L.Usage} (t : L.Tm u) → NoAnn (embedTm t)
tmNoAnn t = embedNoAnn (C.eraseS t)

-- ==================================================================
-- §3  THE PASS THAT IS AVAILABLE TODAY: CHECK MODE, AT A GOAL TYPE.
--
-- All terms, no `run` -- the exit is in the `refl` lines of §4 only.
-- ==================================================================

o oo : Ty
o  = base
oo = o ⊸ᵗ o

-- THE TYPE PASS.  A decision, so its failure branch carries a
-- refutation of the typing judgement rather than a `nothing`.
typePass : (T : Ty) → ⊤G ⊢ Dec⟨ Check [] T ⟩
typePass = closed-check?

-- the generic Bool view, and the synthesis mode for contrast
typechecks! : (T : Ty) → ⊤G ⊢ Δ Bool
typechecks! T = okA (Check [] T) (¬G (Check [] T)) ∘g typePass T

synthesises! : ⊤G ⊢ Δ Bool
synthesises! = okA (Syn []) (¬G (Syn [])) ∘g closed-infer?

synth : ⊤G ⊢ Result (¬G (Syn [])) (Δ Ty)
synth = mapR (¬G (Syn [])) (Δ Ty) (tagA Ty) ∘g closed-infer?

-- a negative answer is a REFUTATION, not an observation
noCheck : (T : Ty) (t : Raw) → run (typechecks! T) t ≡ false → (¬G (Check [] T)) t
noCheck T = refute (Check [] T) (¬G (Check [] T)) (typePass T)

noSyn : (t : Raw) → run synthesises! t ≡ false → (¬G (Syn [])) t
noSyn = refute (Syn []) (¬G (Syn [])) closed-infer?

yesCheck : (T : Ty) (t : Raw) → run (typechecks! T) t ≡ true → Check [] T t
yesCheck T = witness (Check [] T) (¬G (Check [] T)) (typePass T)

-- ==================================================================
-- §4  WHAT IT DOES AND DOES NOT ACCEPT, ON THE FRONT END'S OWN TERMS.
--
-- `Chain.Pipeline` proves `"λx. x λy. y"` compiles to `L.selfApp`, so
-- the second block below is about the chain's actual output.
-- ==================================================================

-- the embedding computes, and is annotation-free by §2
_ : embedTm L.idLin ≡ lam (var 0)
_ = refl

_ : embedTm L.selfApp ≡ app (lam (var 0)) (lam (var 0))
_ = refl

-- ------------------------------------------------------------------
-- 4.1  A LAMBDA IN HEAD POSITION: check mode works.
-- ------------------------------------------------------------------

_ : passes (run (typechecks! oo) at (embedTm L.idLin ↦ true ∷ []))
_ = refl

-- ... and only at the right type
_ : passes (run (typechecks! o) at (embedTm L.idLin ↦ false ∷ []))
_ = refl

-- the positive answer CARRIES the derivation
idTyped : Check [] oo (embedTm L.idLin)
idTyped = yesCheck oo (embedTm L.idLin) refl

-- the negative one carries a refutation of the judgement
idNotBase : (¬G (Check [] o)) (embedTm L.idLin)
idNotBase = noCheck o (embedTm L.idLin) refl

-- synthesis is unavailable, as the mode discipline says
idNoSyn : (¬G (Syn [])) (embedTm L.idLin)
idNoSyn = noSyn (embedTm L.idLin) refl

-- ------------------------------------------------------------------
-- 4.2  THE OBSTRUCTION.  The chain's own output is an APPLICATION with
-- a bare function, and it is rejected in BOTH modes at BOTH types.
-- These are theorems, not observations: each is a refutation.
-- ------------------------------------------------------------------

selfAppNoSyn : (¬G (Syn [])) (embedTm L.selfApp)
selfAppNoSyn = noSyn (embedTm L.selfApp) refl

selfAppNotOO : (¬G (Check [] oo)) (embedTm L.selfApp)
selfAppNotOO = noCheck oo (embedTm L.selfApp) refl

selfAppNotO : (¬G (Check [] o)) (embedTm L.selfApp)
selfAppNotO = noCheck o (embedTm L.selfApp) refl

-- ==================================================================
-- §5  THE SPECIFICATION FOR THE MISSING PASS.
--
-- One annotation, at the FUNCTION of the application, is enough: the
-- ARGUMENT is then checked against the domain and needs none.  So an
-- annotation-inserting pass owes exactly one type per application node,
-- not one per lambda.
-- ==================================================================

fnOnly : Raw
fnOnly = app (ann (lam (var 0)) (oo ⊸ᵗ oo)) (lam (var 0))

-- it is `embedTm L.selfApp` with ONE `ann` inserted, and nothing else
_ : fnOnly ≡ app (ann (lam (var 0)) (oo ⊸ᵗ oo)) (lam (var 0))
_ = refl

_ : passes (run synthesises! at (fnOnly ↦ true ∷ []))
_ = refl

-- ... and it synthesises the type the chain would want
_ : passes (runΔ Ty (¬G (Syn [])) synth at (fnOnly ↦ just oo ∷ []))
_ = refl

-- the annotated form is of course no longer annotation-free, which is
-- the precise sense in which §2's lemma is the obstruction
fnOnlyAnnotated : NoAnn fnOnly → E.⊥
fnOnlyAnnotated (k , _) = k
