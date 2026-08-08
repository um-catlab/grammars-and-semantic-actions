{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  REAL AArch64, AS A MACHINE.

  ------------------------------------------------------------------
  WHY THE INSTRUCTION SET CHANGED
  ------------------------------------------------------------------

  `Compile.ArithToARM.Base`'s machine has three constructors --
  `pushI`, `loadI`, `addI` -- and `Emit` expands each into two to four
  REAL AArch64 instructions.  So `stepI addI` had to model a
  four-instruction sequence including two post-indexed loads and a
  pre-indexed store, and the expansion sat OUTSIDE the proof.

  That is the wrong place for a trust boundary.  It is precisely where
  transcription slips live -- `Emit`'s own header flags the operand
  order of `addI` as a slip that would be invisible in a `refl` test,
  harmless only because addition commutes.

  This file moves the boundary down.  `Instr` is the real instruction
  set: `mov`, `add`, `ldr`, `str`, with the real addressing modes,
  acting on a real register file and a flat memory.  `push`, `load` and
  `add` become DERIVED PROGRAMS, and their correctness becomes a
  theorem rather than an assumption.

  What is trusted is now a list of eight small declarative facts --
  `exec1`'s clauses -- each of which reads directly against ARM's
  manual and can be checked by someone who has never seen the
  compiler.  That is as far as the reduction goes: no framework proves
  its own model faithful.

  ------------------------------------------------------------------
  THE ADDRESSING MODES, WHICH ARE THE PART WORTH READING TWICE
  ------------------------------------------------------------------

      ldrO t n k     ldr  wt, [xn, #k]        offset, no writeback
      strO t n k     str  wt, [xn, #k]        offset, no writeback
      strPost t n k  str  wt, [xn], #k        store at [xn], THEN xn += k
      ldrPre  t n k  ldr  wt, [xn, #-k]!      xn -= k FIRST, then load

  The operand stack uses `strPost`/`ldrPre`, so it grows UPWARD and the
  pointer always names the next FREE slot.  That choice is not
  cosmetic: it makes a push arithmetic `+` and keeps every address the
  compiler reasons about of the form `base + 16·j`, which is what makes
  the separation argument in `Codegen` a comparison of indices rather
  than of truncated subtractions.

  ------------------------------------------------------------------
  WHAT IS FREE ONCE `step` IS GIVEN
  ------------------------------------------------------------------

  `step i = fn (exec1 i)` makes every instruction a DETERMINISTIC
  command, so `ISA.Program stFib Instr step` applies and supplies, with
  no further obligation:

      sem (p ++ q) ⊑ sem p ⨟ sem q        the monoid homomorphism
      seq / seq++ / seq∷ / instrRule      Hoare sequencing
      emptyRule / consequence / refine    the structural rules

  proved once, generically, for every instruction set.  This file owes
  only `exec1`.  `exec-app` below is the FUNCTIONAL shadow of the
  homomorphism and is two clauses; it is stated separately because the
  correctness theorem in `Codegen` is an equation between states rather
  than a Hoare triple, and an equation is what makes the `refl` tests
  reduce.

  The frame rule needs a SEPARATING resource promodel, which a pair of
  total functions is not.  `stFib` below is therefore the trivial
  promodel: enough for sequencing, not enough for framing.  `Codegen`
  proves its non-interference results directly, and says so.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1: this is the definition of a machine.
-}
open import Cubical.Foundations.Prelude

module Compile.ArithToARM.AArch64 where

open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; _·_)
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.List using (List; []; _∷_; _++_)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

-- ==================================================================
-- §1  WORDS, AND DECIDABLE EQUALITY THAT COMPUTES.
--
-- `eqℕ` is `Bool`-valued so that `setM` reduces on closed addresses
-- and the `refl` tests below go through; the two lemmas are what a
-- SYMBOLIC address needs.
-- ==================================================================

Word : Type₀
Word = ℕ

eqℕ : ℕ → ℕ → Bool
eqℕ zero    zero    = true
eqℕ zero    (suc _) = false
eqℕ (suc _) zero    = false
eqℕ (suc m) (suc n) = eqℕ m n

eqℕ-refl : (n : ℕ) → eqℕ n n Eq.≡ true
eqℕ-refl zero    = Eq.refl
eqℕ-refl (suc n) = eqℕ-refl n

-- `Lt m n` -- "m is strictly below n", `Unit`/`⊥`-valued so proofs are
-- `tt` and never block a reduction
Lt : ℕ → ℕ → Type₀
Lt _       zero    = ⊥
Lt zero    (suc _) = Unit
Lt (suc m) (suc n) = Lt m n

lt-neq : (m n : ℕ) → Lt m n → eqℕ m n Eq.≡ false
lt-neq m       zero    ()
lt-neq zero    (suc n) l = Eq.refl
lt-neq (suc m) (suc n) l = lt-neq m n l

lt-suc : (m : ℕ) → Lt m (suc m)
lt-suc zero    = tt
lt-suc (suc m) = lt-suc m

lt-trans-suc : (m n : ℕ) → Lt m n → Lt m (suc n)
lt-trans-suc m       zero    ()
lt-trans-suc zero    (suc n) l = tt
lt-trans-suc (suc m) (suc n) l = lt-trans-suc m n l

-- ==================================================================
-- §2  THE REGISTER FILE.
--
-- The five registers `Emit` actually names.  `regIx` gives them
-- decidable equality without twenty-five clauses, and -- more
-- importantly -- `eqR w9 x20` REDUCES, so `setR` at the concrete
-- registers the compiler uses computes away entirely.
-- ==================================================================

data Reg : Type₀ where
  w0 w9 w10 x19 x20 : Reg

regIx : Reg → ℕ
regIx w0  = 0
regIx w9  = 1
regIx w10 = 2
regIx x19 = 3
regIx x20 = 4

eqR : Reg → Reg → Bool
eqR a b = eqℕ (regIx a) (regIx b)

Regs : Type₀
Regs = Reg → Word

Mem : Type₀
Mem = Word → Word

St : Type₀
St = Regs × Mem

-- A NAMED conditional, not an extended lambda: the two lemmas below
-- rewrite under it, and an anonymous `where`-bound one would be a
-- different function at each use site (the same nominal-identity tax
-- `TheoryGrammar.Base.boolΠ` documents for arities).
ifB : Bool → Word → Word → Word
ifB true  x y = x
ifB false x y = y

-- PRIMITIVE (phase 1): the two updates.
setR : Reg → Word → Regs → Regs
setR r v ρ q = ifB (eqR q r) v (ρ q)

setM : Word → Word → Mem → Mem
setM a v μ b = ifB (eqℕ b a) v (μ b)

-- reading back what was just written, at a SYMBOLIC address
setM-hit : (a v : Word) (μ : Mem) → setM a v μ a Eq.≡ v
setM-hit a v μ = Eq.ap (λ c → ifB c v (μ a)) (eqℕ-refl a)

setM-miss : (a b v : Word) (μ : Mem) → eqℕ b a Eq.≡ false
          → setM a v μ b Eq.≡ μ b
setM-miss a b v μ e = Eq.ap (λ c → ifB c v (μ b)) e

setR-hit : (r : Reg) (v : Word) (ρ : Regs) → setR r v ρ r Eq.≡ v
setR-hit r v ρ = Eq.ap (λ c → ifB c v (ρ r)) (eqℕ-refl (regIx r))

-- ==================================================================
-- §3  THE INSTRUCTION SET.
--
-- Eight constructors, each one a line of AArch64.  This is the whole
-- of what is trusted.
-- ==================================================================

data Instr : Type₀ where
  movI    : Reg → Word → Instr          -- mov  rd, #imm
  addR    : Reg → Reg → Reg → Instr     -- add  rd, rn, rm
  addI    : Reg → Reg → Word → Instr    -- add  rd, rn, #imm
  ldrO    : Reg → Reg → Word → Instr    -- ldr  rt, [rn, #k]
  strO    : Reg → Reg → Word → Instr    -- str  rt, [rn, #k]
  strPost : Reg → Reg → Word → Instr    -- str  rt, [rn], #k
  ldrPre  : Reg → Reg → Word → Instr    -- ldr  rt, [rn, #-k]!
  movR    : Reg → Reg → Instr           -- mov  rd, rn

Prog : Type₀
Prog = List Instr

-- ==================================================================
-- §4  THE MACHINE.  PRIMITIVE (phase 1), and the trusted list.
--
-- `strPost t n k`   store `rt` at `[rn]`, THEN `rn += k`
-- `ldrPre  t n k`   `rn -= k` FIRST, then load `[rn]` into `rt`
--
-- `ldrPre` is written with an explicit `sub` in the arithmetic --
-- `p` is the address AFTER the writeback -- because the compiler only
-- ever pops a slot it has pushed, so the address is always available
-- as a `+`-form and truncated subtraction never arises in a proof.
-- ==================================================================

-- truncated subtraction, TOP LEVEL so a pop address can be named in a
-- proof.  On a literal `k` it strips `k` successors and computes, which
-- is why `Codegen` never needs an arithmetic lemma about it.
sub : ℕ → ℕ → ℕ
sub m       zero    = m
sub zero    (suc _) = zero
sub (suc m) (suc j) = sub m j

exec1 : Instr → St → St
exec1 (movI d n)      (ρ , μ) = setR d n ρ , μ
exec1 (movR d n)      (ρ , μ) = setR d (ρ n) ρ , μ
exec1 (addR d a b)    (ρ , μ) = setR d (ρ a + ρ b) ρ , μ
exec1 (addI d n k)    (ρ , μ) = setR d (k + ρ n) ρ , μ
exec1 (ldrO t n k)    (ρ , μ) = setR t (μ (ρ n + k)) ρ , μ
exec1 (strO t n k)    (ρ , μ) = ρ , setM (ρ n + k) (ρ t) μ
exec1 (strPost t n k) (ρ , μ) = setR n (k + ρ n) ρ , setM (ρ n) (ρ t) μ
exec1 (ldrPre t n k)  (ρ , μ) = setR t (μ (sub (ρ n) k)) (setR n (sub (ρ n) k) ρ) , μ

exec : Prog → St → St
exec []      s = s
exec (i ∷ p) s = exec p (exec1 i s)

-- ==================================================================
-- §5  `exec` IS A MONOID HOMOMORPHISM.
--
-- The functional shadow of `ISA.Program.homSplit3`, and the same two
-- clauses.  Every macro lemma in `Codegen` is this plus `Eq.ap`.
-- ==================================================================

exec-app : (p q : Prog) (s : St) → exec (p ++ q) s Eq.≡ exec q (exec p s)
exec-app []      q s = Eq.refl
exec-app (i ∷ p) q s = exec-app p q (exec1 i s)

-- projections, so statements read like assembly rather than like pairs
rg : St → Regs
rg = fst

mm : St → Mem
mm = snd
