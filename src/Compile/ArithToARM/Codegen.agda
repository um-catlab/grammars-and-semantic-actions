{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE COMPILER, THE SQUARE, AND THE ALIASING THEOREM.

  ------------------------------------------------------------------
  THE SQUARE, AND WHY IT IS AN `Eq.≡` THIS TIME
  ------------------------------------------------------------------

      correct : exec (compile e) σ s  Eq.≡  eval e σ ∷ s

  On-the-nose, for an ARBITRARY tail stack `s`, with no relation and no
  side condition.  It is worth being precise about why this is available
  here and was not available for `Compile.LinToRust`.

  `Compile.Relational.Refutation` refutes

      compileRust t ⇓ compileRust v

  because `compileE` names a binder by its ABSOLUTE DEPTH while source
  substitution moves the residual body one binder shallower: the two
  answers are α-equivalent and syntactically distinct, so the `≡` had to
  be replaced by the realisation relation `Rel`
  (`Compile.Relational.Square.square`).

  Nothing of the kind can happen here, and the reason is structural
  rather than lucky: THE TARGET HAS NO BINDERS.  `AI` has three
  constructors and none of them scopes anything, so there is no naming
  to disagree about, and the observable is a number rather than a piece
  of syntax.  The α-equivalence problem is a cost of compiling BINDING
  STRUCTURE, and it is exactly what restricting the source to a
  first-order fragment buys back.

  The generalisation over the tail stack `s` is the whole induction.
  `eadd`'s proof runs `exec-app` twice and the two hypotheses once each,
  and the final step -- `addI` on `vb ∷ va ∷ s` -- is definitional.

  ------------------------------------------------------------------
  THE ALIASING THEOREM, WHICH IS THE POINT OF DOING IT HERE
  ------------------------------------------------------------------

  A textbook expression compiler stops at `correct`.  The source is
  LINEAR, so a second theorem is available:

      readsLive     : every address the emitted code loads is live in
                      the usage
      readsDisjoint : the two operands of an addition emit code that
                      loads DISJOINT addresses

  `readsDisjoint` has no content of its own -- it is `use⊎-excl`
  transported along `readsLive` -- and `use⊎-excl` in turn is the
  missing `(true , true)` constructor of `Use⊎`.  So a fact about which
  MEMORY the machine code touches is being read straight off the
  source's type, with no analysis pass and no alias solver.

  This is the ARM-relevant form of the linear discipline.  Register
  allocation, frame reuse, and destructive reads are all justified by
  "no two loads name the same slot", and that is what is proved.

  ------------------------------------------------------------------
  WHAT IS AND IS NOT VERIFIED
  ------------------------------------------------------------------

  Everything down to `Prog` is proved.  `Compile.ArithToARM.Emit` turns
  a `Prog` into an AArch64 string, and THAT function has no theorem --
  the same trusted edge `Compile.LinToISA.ARM64` documents, and for the
  same reason (it would need a semantics for the emitted subset, or a
  parser and a round trip).  It is one small total function over a
  three-constructor instruction set, which is a far better boundary than
  "the compiler never sees the program".

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1: a compiler and its metatheory.
-}
open import Cubical.Foundations.Prelude

module Compile.ArithToARM.Codegen where

open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.List using (List; []; _∷_; _++_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import Compile.ArithToARM.Base
import TheoryGrammar.Instances.LinLam.Syntax as L

-- ==================================================================
-- §1  THE COMPILER.  TERM-DIRECTED: it recurses on `Exp`, and the
-- usage is along for the ride.  Contrast
-- `Compile.LinToISA.Codegen.code`, which recurses on the USAGE and
-- therefore cannot distinguish two terms at one index.
-- ==================================================================

-- PRIMITIVE (phase 1)
compile : ∀ {u} → Exp u → Prog
compile {u} (evar s)     = loadI (slotOf 0 u s) ∷ []
compile     (elit _ n)   = pushI n ∷ []
compile     (eadd _ a b) = compile a ++ (compile b ++ (addI ∷ []))

-- ==================================================================
-- §2  THE SIMULATION SQUARE.
--
-- `eadd`, read as a chain:
--
--     exec (ca ++ (cb ++ [addI])) σ s
--   = exec (cb ++ [addI]) σ (exec ca σ s)        exec-app
--   = exec (cb ++ [addI]) σ (va ∷ s)             IH on a
--   = exec [addI] σ (exec cb σ (va ∷ s))         exec-app
--   = exec [addI] σ (vb ∷ va ∷ s)                IH on b
--   = (va + vb) ∷ s                              definitional
--
-- The last line is why `stepI addI`'s underflow clause never appears:
-- the tail `s` was arbitrary, so both hypotheses fired at a stack that
-- already had room.
-- ==================================================================

correct : ∀ {u} (e : Exp u) (σ : Env) (s : Stack)
        → exec (compile e) σ s Eq.≡ (eval e σ ∷ s)
correct (evar s)   σ s' = Eq.refl
correct (elit _ n) σ s' = Eq.refl
correct (eadd _ a b) σ s' =
  (exec-app (compile a) (compile b ++ (addI ∷ [])) σ s'
   Eq.∙ Eq.ap (λ z → exec (compile b ++ (addI ∷ [])) σ z) (correct a σ s'))
  Eq.∙ (exec-app (compile b) (addI ∷ []) σ (eval a σ ∷ s')
        Eq.∙ Eq.ap (λ z → exec (addI ∷ []) σ z)
                   (correct b σ (eval a σ ∷ s')))

-- THE FORM A CLIENT WANTS: run the compiled program on the empty
-- stack and read off the answer.
run : ∀ {u} (e : Exp u) (σ : Env) → exec (compile e) σ [] Eq.≡ (eval e σ ∷ [])
run e σ = correct e σ []

-- ==================================================================
-- §3  WHICH ADDRESSES THE CODE READS.
--
-- A computing predicate rather than a list, so `Reads (pushI n ∷ p) l`
-- reduces to `Reads p l` on the spot and the absurd cases below are
-- `()` rather than lemmas.
-- ==================================================================

-- PRIMITIVE (phase 1)
Reads : Prog → ℕ → Type₀
Reads []             l = ⊥
Reads (loadI k ∷ p)  l = (l Eq.≡ k) ⊎ Reads p l
Reads (_ ∷ p)        l = Reads p l

-- PRIMITIVE (phase 1): reading is additive over concatenation.  Only
-- the forward direction is needed.
reads-app→ : (p q : Prog) (l : ℕ) → Reads (p ++ q) l → Reads p l ⊎ Reads q l
reads-app→ []              q l r       = inr r
reads-app→ (pushI n ∷ p)   q l r       = reads-app→ p q l r
reads-app→ (addI ∷ p)      q l r       = reads-app→ p q l r
reads-app→ (loadI k ∷ p)   q l (inl e) = inl (inl e)
reads-app→ (loadI k ∷ p)   q l (inr r) with reads-app→ p q l r
... | inl x = inl (inr x)
... | inr y = inr y

-- ==================================================================
-- §4  EVERY ADDRESS READ IS LIVE.
--
-- The `evar` clause is `solo-live` transported along the equation the
-- `Reads` witness carries; the `elit` clause is absurd because a
-- literal emits no load; the `eadd` clause splits the concatenation and
-- pushes each side up through the splitting.
-- ==================================================================

readsLive : ∀ {u} (e : Exp u) (l : ℕ) → Reads (compile e) l → LiveAt l u
readsLive {u} (evar s) l (inl e) =
  Eq.transport (λ z → LiveAt z u) (Eq.sym e) (solo-live u s)
readsLive     (evar s) l (inr ())
readsLive     (elit _ n) l ()
readsLive (eadd sp a b) l r with reads-app→ (compile a) (compile b ++ (addI ∷ [])) l r
... | inl ra = use⊎-liveL sp l (readsLive a l ra)
... | inr r' with reads-app→ (compile b) (addI ∷ []) l r'
...   | inl rb = use⊎-liveR sp l (readsLive b l rb)
...   | inr ()

-- ==================================================================
-- §5  THE ALIASING THEOREM.
--
-- One line, and every symbol in it was proved somewhere else.  What it
-- says about the emitted AArch64: the two operand sequences of an
-- addition never load the same slot, so their frame cells may be
-- reused, consumed, or held in registers independently -- WITHOUT an
-- alias analysis, because the source's type already ruled it out.
-- ==================================================================

readsDisjoint : ∀ {u₁ u₂ u} (sp : L.Use⊎ u₁ u₂ u)
                (a : Exp u₁) (b : Exp u₂) (l : ℕ)
              → Reads (compile a) l → Reads (compile b) l → ⊥
readsDisjoint sp a b l ra rb =
  use⊎-excl sp l (readsLive a l ra) (readsLive b l rb)

-- ==================================================================
-- §6  IT COMPUTES.
--
-- A three-variable scope with the middle position DEAD -- the same
-- `ugap` shape `Compile.LinToISA.ARM64` measures -- and the source
-- `x0 + x2`, which is linear in it.
-- ==================================================================

ugap : L.Usage
ugap = true ∷ false ∷ true ∷ []

-- `x0` alone, and `x2` alone, at the two halves of the splitting
uL : L.Usage
uL = true ∷ false ∷ false ∷ []

uR : L.Usage
uR = false ∷ false ∷ true ∷ []

spgap : L.Use⊎ uL uR ugap
spgap = L.uleft (L.uskip (L.uright L.unil))

egap : Exp ugap
egap = eadd spgap (evar tt) (evar tt)

-- one load per LIVE position, in source order, and the dead middle
-- position is simply absent from the code
_ : compile egap ≡ loadI 0 ∷ loadI 2 ∷ addI ∷ []
_ = refl

-- an environment, and the answer
σ0 : Env
σ0 zero          = 7
σ0 (suc zero)    = 99          -- position 1 is DEAD: never read
σ0 (suc (suc _)) = 5

_ : eval egap σ0 ≡ 12
_ = refl

_ : exec (compile egap) σ0 [] ≡ 12 ∷ []
_ = refl

-- ... and the theorem itself reduces, not merely inhabits
_ : run egap σ0 ≡ Eq.refl
_ = refl

-- a nested example: (x0 + x2) is itself an operand
enest : Exp ugap
enest = eadd spgap (evar tt) (eadd (L.uskip (L.uskip (L.uright L.unil)))
                                   (elit tt 1) (evar tt))

_ : compile enest ≡ loadI 0 ∷ pushI 1 ∷ loadI 2 ∷ addI ∷ addI ∷ []
_ = refl

_ : exec (compile enest) σ0 [] ≡ 13 ∷ []
_ = refl
