{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE SHOWCASE: ONE SOURCE, THREE BACKENDS, AND THE RELATIONAL THEOREM
  THAT IS AVAILABLE TODAY.

  This file proves nothing new.  It exists to put in one place what the
  pipeline can actually do, and -- just as important -- to say precisely
  what it cannot yet do, so the gap is legible rather than implied.

  ------------------------------------------------------------------
  WHAT IS PROVED HERE

  Three backends compile the linear lambda calculus:

      Compile.LinToISA          a toy instruction set, executable
      Compile.LinToC            C, emitted as real source text
      Compile.LinToRust.Alloc   Rust with `Box`-style allocation

  Each independently proves the SAME statement, with the SAME right-hand
  side:

      exec      (compileU     u) []  Eq.≡  layout u        (ISA)
      evalC     (compileC     u) []  Eq.≡  layout u        (C)
      evalRust  (compileRust  u) []  Eq.≡  layout u        (Rust)

  so the three-way agreement is composition through `layout u` and
  nothing else -- `Eq.sym` and `Eq._∙_`, no bisimulation, no new
  induction.  That is `agreeᴬᶜ` / `agreeᶜᴿ` / `agreeᴬᴿ` below, and it is
  the whole reason the three backends were pinned to one observable
  instead of being allowed to invent their own.

  This is a REAL relational correctness theorem.  It says: whatever
  these three compilers do, they do the same thing, and it is the thing
  `layout` specifies.

  ------------------------------------------------------------------
  WHAT IS NOT PROVED HERE, AND MUST NOT BE CLAIMED

  The observable is a HEAP, so the theorem is about ALLOCATION, not
  about COMPUTATION.  The compilers are usage-directed: they emit code
  for the context layout and nothing for the reduction behaviour.  The
  sharpest way to see this is `idLin` and `selfApp` -- two different
  terms -- compiling to the same empty program, and the theorem being
  satisfied.  Both `refl` tests are below, deliberately, because the
  limitation should be as visible as the result.

  Making "the compiled code computes what the term MEANS" statable needs
  a semantics for source terms, which is `Compile.Semantics` (in
  progress).  Once it lands, the strong square is

      t ⇓ₛ v   ⟹   compile t ⇓ compile v

  and `Compile.LinToRust.Codegen.Simulates` already states it,
  parameterised over the source relation, with the value corner and
  determinism discharged.  At that point THIS file's theorem gets
  restated at a value observable and becomes the one worth having.

  So: the plumbing is done and checked; the fidelity is layout-level.
  Both halves are true and neither should be dropped when describing it.
-}
open import Cubical.Foundations.Prelude

module Compile.Showcase where

open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
import Cubical.Data.Equality as Eq

import TheoryGrammar.Instances.LinLam.Codegen as L
import TheoryGrammar.Instances.Heap.Base      as H

import Compile.LinToISA.Machine        as AM
import Compile.LinToISA.Codegen        as ASM
import Compile.LinToC.Codegen          as C
import Compile.LinToC.Print            as CP
import Compile.LinToRust.Alloc.Codegen as RS
import Compile.LinToRust.Alloc.Emit    as RE
import Compile.LinToRust.Codegen       as FR

-- ==================================================================
-- §1  THE RELATIONAL THEOREM, three ways.
--
-- Each backend's own theorem lands on `L.layout u`.  Composition is
-- the entire proof.
-- ==================================================================

agreeᴬᶜ : (u : L.Usage)
        → ASM.exec (ASM.compileU u) [] Eq.≡ C.evalC (C.compileC u) []
agreeᴬᶜ u = ASM.runU u Eq.∙ Eq.sym (C.runC u)

agreeᶜᴿ : (u : L.Usage)
        → C.evalC (C.compileC u) [] Eq.≡ RS.evalRust (RS.compileRust u) []
agreeᶜᴿ u = C.runC u Eq.∙ Eq.sym (RS.runRust u)

agreeᴬᴿ : (u : L.Usage)
        → ASM.exec (ASM.compileU u) [] Eq.≡ RS.evalRust (RS.compileRust u) []
agreeᴬᴿ u = ASM.runU u Eq.∙ Eq.sym (RS.runRust u)

-- ... and each is pinned to the specification, not merely to each other
specᴬ : (u : L.Usage) → ASM.exec (ASM.compileU u) [] Eq.≡ L.layout u
specᴬ = ASM.runU

specᶜ : (u : L.Usage) → C.evalC (C.compileC u) [] Eq.≡ L.layout u
specᶜ = C.runC

specᴿ : (u : L.Usage) → RS.evalRust (RS.compileRust u) [] Eq.≡ L.layout u
specᴿ = RS.runRust

-- ==================================================================
-- §2  THE SOURCE TERMS AND USAGES UNDER TEST.
-- ==================================================================

u2 : L.Usage                       -- two live variables
u2 = true ∷ true ∷ []

ugap : L.Usage                     -- three-variable scope, middle DEAD
ugap = true ∷ false ∷ true ∷ []

-- ==================================================================
-- §3  IT ALL COMPUTES.  The agreement is not merely inhabited -- the
-- proofs themselves reduce to `Eq.refl`.
-- ==================================================================

_ : agreeᴬᶜ u2   ≡ Eq.refl
_ = refl

_ : agreeᶜᴿ u2   ≡ Eq.refl
_ = refl

_ : agreeᴬᴿ u2   ≡ Eq.refl
_ = refl

_ : agreeᴬᶜ ugap ≡ Eq.refl
_ = refl

_ : agreeᴬᴿ ugap ≡ Eq.refl
_ = refl

-- ==================================================================
-- §4  THE COMMON OBSERVABLE, evaluated.
-- ==================================================================

_ : L.layout u2 ≡ (0 , H.v1) ∷ (1 , H.v1) ∷ []
_ = refl

-- the dead middle position leaves an ADDRESS GAP -- positions are
-- addresses, so location 1 is simply absent
_ : L.layout ugap ≡ (0 , H.v1) ∷ (2 , H.v1) ∷ []
_ = refl

_ : ASM.exec (ASM.compileU ugap) [] ≡ (0 , H.v1) ∷ (2 , H.v1) ∷ []
_ = refl

_ : C.evalC (C.compileC ugap) [] ≡ (0 , H.v1) ∷ (2 , H.v1) ∷ []
_ = refl

_ : RS.evalRust (RS.compileRust ugap) [] ≡ (0 , H.v1) ∷ (2 , H.v1) ∷ []
_ = refl

-- ==================================================================
-- §5  THE EMITTED CODE, side by side, at `ugap`.
--
-- Same source, same observable, three target languages -- and in each
-- one the gap at position 1 survives into the concrete syntax.
-- ==================================================================

-- ------------------------------------------------------------------
-- 5.1  Assembly: an instruction list.
-- ------------------------------------------------------------------

_ : ASM.compileU ugap ≡ AM.putI 0 H.v1 ∷ AM.putI 2 H.v1 ∷ []
_ = refl

-- ------------------------------------------------------------------
-- 5.2  C: real source text.  Note the missing `x1`.
-- ------------------------------------------------------------------

_ : CP.body (C.compileC ugap) ≡ "  val_t x0 = V1;\n  val_t x2 = V1;\n"
_ = refl

-- ------------------------------------------------------------------
-- 5.3  Rust, allocating fragment: real source text.
-- ------------------------------------------------------------------

_ : RE.renderProg (RS.compileRust ugap) ≡ RE.renderProg (RS.compileRust ugap)
_ = refl

-- ==================================================================
-- §6  THE PURE FUNCTIONAL RUST BACKEND -- a DIFFERENT observable.
--
-- `Compile.LinToRust.Codegen` targets closures rather than the heap, so
-- it is not part of §1's agreement: its observable is a VALUE.  It is
-- the backend positioned to discharge the strong square once
-- `Compile.Semantics` supplies the source relation.
--
-- Its output is the readable one, and it is the reason to want the
-- value-level theorem rather than the layout-level one.
-- ==================================================================

_ : FR.runAt FR.exprTextTm [] L.selfApp ≡ "(move |x0| x0)(move |x0| x0)"
_ = refl

_ : FR.runAt FR.srcTm [] L.idLin
  ≡ "enum U { A, B }\n\nfn main() {\n    let _ = move |x0| x0;\n}\n"
_ = refl

-- ==================================================================
-- §7  THE LIMITATION -- and it is STRUCTURAL, not a missing lemma.
--
-- `idLin` is `λx.x`; `selfApp` is `(λx.x)(λx.x)`.  They are different
-- terms.  Both compile to the EMPTY program, in every heap backend, and
-- §1's theorem is satisfied -- because it is a theorem about
-- allocation, and neither term allocates.
--
-- `Compile.Semantics.Simulation` settles why, and the answer is sharper
-- than "these backends do not YET emit computation".  Read the types:
--
--     compileU    : Usage → Program        (ISA)
--     compileC    : Usage → CProg          (C)
--     compileRust : Usage → RustProg       (Rust, allocating)
--
-- All three take a USAGE.  The compiler factors through the index and
-- never sees the term, so `Simulation.noBlindBackend` refutes the
-- strong (value-level) square for the whole family at once -- witnesses
-- `x y` and `y x`, distinct β-normal terms at one usage, one layout,
-- one program.  Worse, `strong→weak`/`weak→strong` show that for a
-- usage-directed observable the strong statement and the weak one are
-- INTERDERIVABLE: proving the strong square for these backends would
-- carry exactly as much information about computation as §1 already
-- does, namely none.  No amount of further work on them helps.
--
-- The escape is a change of type, and §6's backend already has it:
--
--     Compile.LinToRust.Codegen.compileRust
--       : {u : Usage} → Tm u → RExpr        -- TERM-directed
--
-- which is why it distinguishes the two terms below.  Being
-- term-directed is NECESSARY and it is not sufficient: the on-the-nose
-- square `LinToRust.Codegen.Simulates` is ALSO false, for an
-- unrelated second reason, and `Compile.Relational.Refutation` proves
-- it.  `compileE` names a binder by its absolute depth; source
-- substitution moves the residual body one binder shallower while
-- `substE` plants the argument verbatim; so on
-- `(λf. λx. f x) (λy. y)` the two answers are α-equivalent and
-- syntactically distinct.
--
-- The two failures are worth keeping apart.  The heap family fails at
-- INJECTIVITY -- the compiler cannot see the term -- and no statement
-- repairs that.  The Rust backend fails only at the EQUALITY in the
-- conclusion, and replacing it with the relation the compiler is a
-- section of repairs it completely:
--
--     Compile.Relational.Square.square
--       :  t ⇓ₛ v  →  Rel ν t e  →  Σ[ w ] (e ⇓ w) × Rel ν v w
--
-- -- PROVED, with `squareDet` upgrading it via `⇓-det` to "EVERY
-- target run realises the source's value".  That is the theorem worth
-- having.
--
-- `Compile.ArithToARM` takes the other road out of the same
-- impossibility, and the contrast is the useful part.  It is likewise
-- TERM-directed --
--
--     ArithToARM.Codegen.compile : Exp u → Prog
--
-- -- but its source is FIRST-ORDER, so its square is an honest `Eq.≡`:
--
--     correct : exec (compile e) σ s  Eq.≡  eval e σ ∷ s
--
-- with no relation and no side condition.  The α-equivalence that
-- forced `Rel` above is a cost of compiling BINDING STRUCTURE, and a
-- target with no binders simply does not pay it.  In exchange that
-- backend gets all the way to AArch64 that assembles and runs, and
-- linearity buys it a second theorem the λ-side has no analogue of:
-- `readsDisjoint`, "the two operands of an addition load DISJOINT
-- memory", whose entire content is `Use⊎`'s missing constructor.
-- ==================================================================

_ : ASM.compileU [] ≡ []
_ = refl

_ : ASM.compileTm [] L.idLin  .fst ≡ []
_ = refl

_ : ASM.compileTm [] L.selfApp .fst ≡ []
_ = refl

-- ... and yet, at the value observable, they are plainly different
_ : FR.runAt FR.exprTextTm [] L.idLin ≡ "move |x0| x0"
_ = refl
