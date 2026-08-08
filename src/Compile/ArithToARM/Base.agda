{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  A TERM-DIRECTED TARGET.  The source, the machine, and nothing else.

  ------------------------------------------------------------------
  WHY THIS FILE EXISTS
  ------------------------------------------------------------------

  `Compile.LinToISA.Codegen` compiles

      compileU : Usage → Program

  -- it takes the INDEX, not the term.  `Compile.Semantics.Simulation`'s
  `noBlindBackend` refutes the value-level square for every compiler of
  that shape at once, so no amount of further work on it can produce a
  theorem about COMPUTATION; `Compile.Showcase` §7 states the situation
  and the two `refl` tests there (`idLin` and `selfApp`, distinct terms,
  both compiling to the EMPTY program) are the measurement.

  Being term-directed is therefore a PRECONDITION for any correctness
  theorem about a target machine, not an optimisation.  This file and
  its two companions supply one, at a source small enough that the
  compilation is direct -- no closures, hence no runtime.

      Base      the source language, the machine, and `exec`
      Codegen   `compile`, the simulation square, and the linearity
                theorem
      Emit      AArch64 for Apple silicon

  ------------------------------------------------------------------
  THE SOURCE: LINEAR ARITHMETIC
  ------------------------------------------------------------------

  `Exp u` is an arithmetic expression whose free variables are exactly
  the live positions of `u`, USED ONCE EACH -- `eadd` carries a
  `Use⊎ u₁ u₂ u`, the same splitting `LinLam.Syntax.tapp` carries, and
  the same missing `(true , true)` constructor makes double use
  unrepresentable.

  That is the whole reason to build the fragment here rather than take
  a textbook expression compiler off the shelf.  A textbook compiler
  proves `exec (compile e) = eval e` and stops.  Linearity buys a
  second theorem that a nonlinear source cannot state:

      readsDisjoint : the two operands of an addition compile to code
                      that reads DISJOINT memory

  -- proved in `Codegen`, and its entire content is `Use⊎`'s missing
  constructor, transported along `readsLive`.  That is an ALIASING fact
  about the emitted machine code, obtained from the source's type.

  ------------------------------------------------------------------
  THE MACHINE
  ------------------------------------------------------------------

  A stack machine over a read-only environment:

      pushI n     push the literal n
      loadI l     push the contents of slot l
      addI        pop two, push their sum

  `exec` threads a `Stack`, and `exec-app` is the one fact the compiler
  proof needs: running `p ++ q` is running `q` after `p`.  That is
  `ISA.Program`'s "`sem` is a monoid homomorphism" in its functional
  reading, and here it is two clauses because `exec` is a function
  rather than a relation.

  `stepI addI` has a catch-all clause for a stack of fewer than two
  entries.  It is UNREACHABLE in every statement below: `correct` is
  stated at an ARBITRARY tail stack, so the induction hypothesis always
  supplies the operands.  Keeping the machine total rather than partial
  is what lets `exec` be a function, and being a function is what makes
  the theorem an `Eq.≡` that computes.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1 throughout: this is the definition of a machine and a
  metatheorem about it, not a program in the calculus.
-}
open import Cubical.Foundations.Prelude

module Compile.ArithToARM.Base where

open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.List using (List; []; _∷_; _++_)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

import TheoryGrammar.Instances.LinLam.Syntax as L

-- ==================================================================
-- §1  THE ENVIRONMENT.
--
-- Total, so `eval` needs no side condition.  The usage says which
-- positions may be READ, not which are defined -- exactly as `layout`
-- says which addresses are written.
-- ==================================================================

Env : Type₀
Env = ℕ → ℕ

-- ==================================================================
-- §2  THE POSITION OF THE SOLE LIVE VARIABLE.
--
-- The same function `LinToRust.Codegen.soloAt` computes; repeated here
-- so the ARM path does not depend on the Rust path.  `slotOf-shift` is
-- the offset law, and it is the only fact about it anything needs.
-- ==================================================================

-- PRIMITIVE (phase 1)
slotOf : ℕ → (u : L.Usage) → L.Solo u → ℕ
slotOf p []          ()
slotOf p (true  ∷ u) e = p
slotOf p (false ∷ u) s = slotOf (suc p) u s

-- PRIMITIVE (phase 1)
slotOf-shift : (p : ℕ) (u : L.Usage) (s : L.Solo u)
             → slotOf (suc p) u s Eq.≡ suc (slotOf p u s)
slotOf-shift p []          ()
slotOf-shift p (true  ∷ u) e = Eq.refl
slotOf-shift p (false ∷ u) s = slotOf-shift (suc p) u s

-- ==================================================================
-- §3  THE SOURCE.
--
-- `eadd` carries the splitting, so a term that used a variable twice
-- would need a `Use⊎ u₁ u₂ u` with `true` on both sides, and there is
-- no such constructor.  Linearity is structural, not a side condition.
-- ==================================================================

data Exp : L.Usage → Type₀ where
  evar : ∀ {u} → L.Solo u → Exp u
  elit : ∀ {u} → L.Empty u → ℕ → Exp u
  eadd : ∀ {u₁ u₂ u} → L.Use⊎ u₁ u₂ u → Exp u₁ → Exp u₂ → Exp u

-- PRIMITIVE (phase 1): the denotation.
eval : ∀ {u} → Exp u → Env → ℕ
eval {u} (evar s)     σ = σ (slotOf 0 u s)
eval     (elit _ n)   σ = n
eval     (eadd _ a b) σ = eval a σ + eval b σ

-- ==================================================================
-- §4  THE MACHINE.
-- ==================================================================

data AI : Type₀ where
  pushI : ℕ → AI
  loadI : ℕ → AI
  addI  : AI

Prog : Type₀
Prog = List AI

Stack : Type₀
Stack = List ℕ

-- PRIMITIVE (phase 1): the machine, one instruction at a time.  The
-- final clause is the underflow case and is unreachable below.
stepI : AI → Env → Stack → Stack
stepI (pushI n) σ s           = n ∷ s
stepI (loadI l) σ s           = σ l ∷ s
stepI addI      σ (y ∷ x ∷ s) = (x + y) ∷ s
stepI addI      σ s           = s

-- PRIMITIVE (phase 1): the one recursion over a program in this file.
exec : Prog → Env → Stack → Stack
exec []      σ s = s
exec (i ∷ p) σ s = exec p σ (stepI i σ s)

-- ==================================================================
-- §5  `exec` IS A MONOID HOMOMORPHISM.
--
-- `ISA.Program` proves this for the RELATIONAL semantics of an
-- arbitrary instruction set, by the same two-clause induction.  Here
-- the semantics is a function, so the statement is an equation and the
-- proof is the induction with no bookkeeping at all.
-- ==================================================================

-- PRIMITIVE (phase 1)
exec-app : (p q : Prog) (σ : Env) (s : Stack)
         → exec (p ++ q) σ s Eq.≡ exec q σ (exec p σ s)
exec-app []      q σ s = Eq.refl
exec-app (i ∷ p) q σ s = exec-app p q σ (stepI i σ s)

-- ==================================================================
-- §6  LIVENESS, AS A COMPUTING PREDICATE.
--
-- `Unit`/`⊥`-valued, in `Syntax.Same`'s style, so its proofs are `tt`
-- and never block a `refl`.  This is `Compile.Relational.Base.LiveAt`;
-- repeated for the same reason `slotOf` is.
-- ==================================================================

-- PRIMITIVE (phase 1)
LiveAt : ℕ → L.Usage → Type₀
LiveAt _       []          = ⊥
LiveAt zero    (true  ∷ _) = Unit
LiveAt zero    (false ∷ _) = ⊥
LiveAt (suc p) (_ ∷ u)     = LiveAt p u

-- the sole live variable of a `Solo` really is live
solo-live : (u : L.Usage) (s : L.Solo u) → LiveAt (slotOf 0 u s) u
solo-live []          ()
solo-live (true  ∷ u) e = tt
solo-live (false ∷ u) s =
  Eq.transport (λ z → LiveAt z (false ∷ u))
               (Eq.sym (slotOf-shift 0 u s))
               (solo-live u s)

-- ==================================================================
-- §7  WHAT A SPLITTING SAYS ABOUT LIVENESS.
--
-- Two directions and an exclusion.  `use⊎-excl` is the one that pays:
-- its `uleft`/`uright` clauses are absurd IMMEDIATELY, because the
-- constructor that would have given `true` on both sides does not
-- exist.  Everything `Codegen` proves about aliasing is this.
-- ==================================================================

use⊎-liveL : ∀ {u₁ u₂ u} → L.Use⊎ u₁ u₂ u → (p : ℕ) → LiveAt p u₁ → LiveAt p u
use⊎-liveL L.unil        p       ()
use⊎-liveL (L.uleft sp)  zero    lv = tt
use⊎-liveL (L.uleft sp)  (suc p) lv = use⊎-liveL sp p lv
use⊎-liveL (L.uright sp) zero    ()
use⊎-liveL (L.uright sp) (suc p) lv = use⊎-liveL sp p lv
use⊎-liveL (L.uskip sp)  zero    ()
use⊎-liveL (L.uskip sp)  (suc p) lv = use⊎-liveL sp p lv

use⊎-liveR : ∀ {u₁ u₂ u} → L.Use⊎ u₁ u₂ u → (p : ℕ) → LiveAt p u₂ → LiveAt p u
use⊎-liveR L.unil        p       ()
use⊎-liveR (L.uleft sp)  zero    ()
use⊎-liveR (L.uleft sp)  (suc p) lv = use⊎-liveR sp p lv
use⊎-liveR (L.uright sp) zero    lv = tt
use⊎-liveR (L.uright sp) (suc p) lv = use⊎-liveR sp p lv
use⊎-liveR (L.uskip sp)  zero    ()
use⊎-liveR (L.uskip sp)  (suc p) lv = use⊎-liveR sp p lv

-- THE LINEARITY FACT.  No position is live on both sides of a
-- splitting.  Compare `Heap.Base`'s `apart-self` and
-- `LinLam.Context`'s remark: a variable cannot be used twice, and the
-- proof is the missing constructor.
use⊎-excl : ∀ {u₁ u₂ u} → L.Use⊎ u₁ u₂ u
          → (p : ℕ) → LiveAt p u₁ → LiveAt p u₂ → ⊥
use⊎-excl L.unil        p       ()
use⊎-excl (L.uleft sp)  zero    l₁ ()
use⊎-excl (L.uleft sp)  (suc p) l₁ l₂ = use⊎-excl sp p l₁ l₂
use⊎-excl (L.uright sp) zero    () l₂
use⊎-excl (L.uright sp) (suc p) l₁ l₂ = use⊎-excl sp p l₁ l₂
use⊎-excl (L.uskip sp)  zero    () l₂
use⊎-excl (L.uskip sp)  (suc p) l₁ l₂ = use⊎-excl sp p l₁ l₂
