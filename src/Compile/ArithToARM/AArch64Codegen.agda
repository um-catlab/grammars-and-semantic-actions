{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE CORRECTNESS THEOREM FOR REAL AArch64.

  ------------------------------------------------------------------
  THE STATEMENT
  ------------------------------------------------------------------

      correct : Sep e s  →  Post e s (exec (compile e) s)

  where `Post` has four fields and each one is doing work:

      pX19   x19 is UNCHANGED          -- the environment base survives
      pSP    x20 is  16 + old x20      -- EXACTLY one slot is pushed
      pVal   mem at the OLD x20 is `eval e`   -- and it is the answer
      pLow   memory strictly BELOW the old x20 is untouched

  Everything is stated RELATIVE to the incoming stack pointer.  That is
  not a presentational choice: it removes the stack base, the depth,
  and all of `slots`-style arithmetic from the statement, so the
  induction hypothesis at a subexpression is the theorem at the state
  the previous subexpression left behind, with nothing to re-index.

  `pLow` is the load-bearing one.  It is what lets `eadd` know that
  compiling the RIGHT operand did not disturb the value the LEFT
  operand pushed, and -- together with `Sep` -- that neither of them
  disturbed the environment.  A compiler correctness theorem without it
  is not a theorem about a machine with one memory.

  ------------------------------------------------------------------
  SEPARATION, AND WHERE IT IS SPENT
  ------------------------------------------------------------------

      Sep : (l : ℕ) → LiveAt l u → Lt (rg s x19 + off8 l) (rg s x20)

  "every environment slot this expression may read lies strictly below
  the operand stack".  It is spent exactly twice, both times in `eadd`:
  to know the right operand still sees the original environment, and to
  push the hypothesis down to the two subexpressions.

  Note what is NOT assumed: nothing about how big the frame is, nothing
  about alignment, and no upper bound on the stack.  The proof needs
  only that the two regions do not overlap on the addresses actually
  touched, and `Compile.ArithToARM.Codegen.readsLive` already says
  which those are.

  ------------------------------------------------------------------
  WHAT THE FRAMEWORK PAID FOR
  ------------------------------------------------------------------

  `exec-app` -- "running `p ++ q` is running `q` after `p`" -- is the
  functional shadow of `ISA.Program.homSplit3`, and it is the ONLY
  structural fact this proof uses about programs.  Every macro
  (`push9`, `addSeq`) is specified by a lemma proved from it, so the
  expansion of a stack operation into real instructions is a THEOREM
  here, where in `Compile.ArithToARM.Emit` it was an assumption sitting
  outside the proof.  That is the whole point of moving `Instr` down to
  the real instruction set.

  What is still owed to the framework: `stFib` is trivial, so the frame
  rule is not available and `pLow` is proved by hand.  With a
  separating resource promodel over `(Regs × Mem)` it would be
  `frameRuleCmd`, and `pLow` would be free.  See `ISA.Memory`.

  ------------------------------------------------------------------
  WHY THE PROOFS ARE SHORT
  ------------------------------------------------------------------

  `eqR` on the five concrete registers REDUCES, so every `setR` the
  compiler emits computes away and `pX19`/`pSP` for the leaves are
  `Eq.refl`.  `sub` on the literal 16 strips sixteen successors and
  computes, so a pop needs no arithmetic lemma.  The only symbolic
  quantity in the whole development is the incoming `ρ x20`, and it
  occurs ONCE in `exec addSeq` -- which is why `addSeq-spec` is four
  `Eq.ap`s along a single hypothesis.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1: a compiler and its metatheory.
-}
open import Cubical.Foundations.Prelude

module Compile.ArithToARM.AArch64Codegen where

open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.List using (List; []; _∷_; _++_)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import Compile.ArithToARM.AArch64
open import Compile.ArithToARM.Base
  using (Exp; evar; elit; eadd; eval; Env; slotOf; LiveAt; solo-live;
         use⊎-liveL; use⊎-liveR)
import TheoryGrammar.Instances.LinLam.Syntax as L

-- ==================================================================
-- §1  ADDRESSES.
--
-- `off8 l` is the byte offset of environment slot `l`; it is written
-- with 8 on the LEFT so that `8 + X` reduces to `suc⁸ X` and every
-- address the compiler manipulates is a literal prefix of a symbolic
-- tail.  That is what makes `sub _ 16` compute.
-- ==================================================================

off8 : ℕ → Word
off8 zero    = 0
off8 (suc l) = 8 + off8 l

envOf : Word → Mem → Env
envOf eb μ l = μ (eb + off8 l)

-- ==================================================================
-- §2  ORDER LEMMAS.  All four are `Unit`/`⊥` bookkeeping.
-- ==================================================================

lt-add : (j n k : ℕ) → Lt n k → Lt n (j + k)
lt-add zero    n k l = l
lt-add (suc j) n k l = lt-trans-suc n (j + k) (lt-add j n k l)

lt-16 : (n : ℕ) → Lt n (16 + n)
lt-16 zero    = tt
lt-16 (suc m) = lt-16 m

-- ==================================================================
-- §3  `eval` ONLY LOOKS AT LIVE SLOTS.
--
-- Needed because the right operand of an addition is evaluated in the
-- memory the LEFT operand left behind, and those two memories agree
-- only where it matters.
-- ==================================================================

eval-cong : ∀ {u} (e : Exp u) (σ τ : Env)
          → ((l : ℕ) → LiveAt l u → σ l Eq.≡ τ l)
          → eval e σ Eq.≡ eval e τ
eval-cong {u} (evar s)      σ τ h = h (slotOf 0 u s) (solo-live u s)
eval-cong     (elit _ n)    σ τ h = Eq.refl
eval-cong     (eadd sp a b) σ τ h =
  Eq.ap (λ z → z + eval b σ) (eval-cong a σ τ (λ l lv → h l (use⊎-liveL sp l lv)))
  Eq.∙ Eq.ap (λ z → eval a τ + z) (eval-cong b σ τ (λ l lv → h l (use⊎-liveR sp l lv)))

-- ==================================================================
-- §4  THE COMPILER.
--
-- `push9` and `addSeq` are the two macros.  They are ordinary
-- programs, so their specifications below are theorems.
-- ==================================================================

push9 : Prog
push9 = strPost w9 x20 16 ∷ []

addSeq : Prog
addSeq = ldrPre w9 x20 16 ∷ ldrPre w10 x20 16 ∷ addR w9 w10 w9 ∷ push9

compile : ∀ {u} → Exp u → Prog
compile {u} (evar s)     = ldrO w9 x19 (off8 (slotOf 0 u s)) ∷ push9
compile     (elit _ n)   = movI w9 n ∷ push9
compile     (eadd _ a b) = compile a ++ (compile b ++ addSeq)

-- ==================================================================
-- §5  THE MACRO SPECIFICATION.
--
-- `addSeq` pops twice, adds, and pushes.  Written out, the two pop
-- addresses are `sub (ρ x20) 16` and `sub (sub (ρ x20) 16) 16`, and
-- the incoming `ρ x20` occurs exactly once -- so each field is one
-- `Eq.ap` along `h`, and `sub` does the rest by computation.
--
-- The operand order is FIXED here rather than asserted: the first pop
-- takes the value pushed LAST (the right operand), the second takes
-- the left, and `addR w9 w10 w9` computes `w10 + w9` = left + right.
-- ==================================================================

addSeq-x19 : (ρ : Regs) (μ : Mem)
           → rg (exec addSeq (ρ , μ)) x19 Eq.≡ ρ x19
addSeq-x19 ρ μ = Eq.refl

addSeq-sp : (ρ : Regs) (μ : Mem) (X : Word) → ρ x20 Eq.≡ 16 + (16 + X)
          → rg (exec addSeq (ρ , μ)) x20 Eq.≡ 16 + X
addSeq-sp ρ μ X h = Eq.ap (λ z → 16 + sub (sub z 16) 16) h

addSeq-val : (ρ : Regs) (μ : Mem) (X : Word) → ρ x20 Eq.≡ 16 + (16 + X)
           → mm (exec addSeq (ρ , μ)) X Eq.≡ (μ X + μ (16 + X))
addSeq-val ρ μ X h =
  Eq.ap (λ z → setM (sub (sub z 16) 16)
                    (μ (sub (sub z 16) 16) + μ (sub z 16)) μ X) h
  Eq.∙ setM-hit X (μ X + μ (16 + X)) μ

addSeq-low : (ρ : Regs) (μ : Mem) (X : Word) → ρ x20 Eq.≡ 16 + (16 + X)
           → (a : Word) → Lt a X → mm (exec addSeq (ρ , μ)) a Eq.≡ μ a
addSeq-low ρ μ X h a l =
  Eq.ap (λ z → setM (sub (sub z 16) 16)
                    (μ (sub (sub z 16) 16) + μ (sub z 16)) μ a) h
  Eq.∙ setM-miss X a (μ X + μ (16 + X)) μ (lt-neq a X l)

-- ==================================================================
-- §6  THE POSTCONDITION.
-- ==================================================================

record Post {u : L.Usage} (e : Exp u) (s s' : St) : Type₀ where
  field
    pX19 : rg s' x19 Eq.≡ rg s x19
    pSP  : rg s' x20 Eq.≡ 16 + rg s x20
    pVal : mm s' (rg s x20) Eq.≡ eval e (envOf (rg s x19) (mm s))
    pLow : (a : Word) → Lt a (rg s x20) → mm s' a Eq.≡ mm s a

open Post public

Sep : L.Usage → St → Type₀
Sep u s = (l : ℕ) → LiveAt l u → Lt (rg s x19 + off8 l) (rg s x20)

-- ==================================================================
-- §7  THE THEOREM.
-- ==================================================================

correct : ∀ {u} (e : Exp u) (s : St) → Sep u s
        → Post e s (exec (compile e) s)

-- ---- leaves.  Every register fact is `Eq.refl`, because `eqR` on
-- ---- concrete registers computes.
correct {u} (evar so) (ρ , μ) sep .pX19 = Eq.refl
correct {u} (evar so) (ρ , μ) sep .pSP  = Eq.refl
correct {u} (evar so) (ρ , μ) sep .pVal =
  setM-hit (ρ x20) (μ (ρ x19 + off8 (slotOf 0 u so))) μ
correct {u} (evar so) (ρ , μ) sep .pLow a l =
  setM-miss (ρ x20) a (μ (ρ x19 + off8 (slotOf 0 u so))) μ (lt-neq a (ρ x20) l)

correct (elit _ n) (ρ , μ) sep .pX19 = Eq.refl
correct (elit _ n) (ρ , μ) sep .pSP  = Eq.refl
correct (elit _ n) (ρ , μ) sep .pVal = setM-hit (ρ x20) n μ
correct (elit _ n) (ρ , μ) sep .pLow a l =
  setM-miss (ρ x20) a n μ (lt-neq a (ρ x20) l)

-- ---- the compound case.
correct {u} (eadd {u₁} {u₂} sp a b) s sep = res
  where
  s₁ : St
  s₁ = exec (compile a) s

  sepA : Sep u₁ s
  sepA l lv = sep l (use⊎-liveL sp l lv)

  A : Post a s s₁
  A = correct a s sepA

  -- the environment base and the stack pointer, transported to `s₁`
  sepB : Sep u₂ s₁
  sepB l lv =
    Eq.transport (λ z → Lt (rg s₁ x19 + off8 l) z) (Eq.sym (A .pSP))
      (Eq.transport (λ z → Lt (z + off8 l) (16 + rg s x20)) (Eq.sym (A .pX19))
        (lt-add 16 (rg s x19 + off8 l) (rg s x20)
                (sep l (use⊎-liveR sp l lv))))

  s₂ : St
  s₂ = exec (compile b) s₁

  B : Post b s₁ s₂
  B = correct b s₁ sepB

  -- `s₂`'s stack pointer, in the form `addSeq-spec` wants
  hsp : rg s₂ x20 Eq.≡ 16 + (16 + rg s x20)
  hsp = B .pSP Eq.∙ Eq.ap (λ z → 16 + z) (A .pSP)

  -- the left operand's value survived compiling the right one
  keptA : mm s₂ (rg s x20) Eq.≡ eval a (envOf (rg s x19) (mm s))
  keptA =
    B .pLow (rg s x20)
      (Eq.transport (λ z → Lt (rg s x20) z) (Eq.sym (A .pSP)) (lt-16 (rg s x20)))
    Eq.∙ A .pVal

  -- ... and so did the environment, which is what `Sep` was for
  envKept : (l : ℕ) → LiveAt l u₂
          → envOf (rg s x19) (mm s₁) l Eq.≡ envOf (rg s x19) (mm s) l
  envKept l lv = A .pLow (rg s x19 + off8 l) (sep l (use⊎-liveR sp l lv))

  valB : mm s₂ (16 + rg s x20) Eq.≡ eval b (envOf (rg s x19) (mm s))
  valB =
    Eq.transport (λ z → mm s₂ z Eq.≡ eval b (envOf (rg s₁ x19) (mm s₁)))
                 (A .pSP) (B .pVal)
    Eq.∙ (Eq.ap (λ z → eval b (envOf z (mm s₁))) (A .pX19)
          Eq.∙ eval-cong b (envOf (rg s x19) (mm s₁)) (envOf (rg s x19) (mm s))
                         envKept)

  -- the two `exec-app`s, once
  step2 : exec (compile (eadd sp a b)) s Eq.≡ exec addSeq s₂
  step2 =
    exec-app (compile a) (compile b ++ addSeq) s
    Eq.∙ exec-app (compile b) addSeq s₁

  res : Post (eadd sp a b) s (exec (compile (eadd sp a b)) s)
  res .pX19 =
    Eq.transport (λ z → rg z x19 Eq.≡ rg s x19) (Eq.sym step2)
      (addSeq-x19 (fst s₂) (snd s₂) Eq.∙ (B .pX19 Eq.∙ A .pX19))
  res .pSP =
    Eq.transport (λ z → rg z x20 Eq.≡ 16 + rg s x20) (Eq.sym step2)
      (addSeq-sp (fst s₂) (snd s₂) (rg s x20) hsp)
  res .pVal =
    Eq.transport (λ z → mm z (rg s x20)
                        Eq.≡ eval (eadd sp a b) (envOf (rg s x19) (mm s)))
                 (Eq.sym step2)
      (addSeq-val (fst s₂) (snd s₂) (rg s x20) hsp
       Eq.∙ (Eq.ap (λ z → z + mm s₂ (16 + rg s x20)) keptA
             Eq.∙ Eq.ap (λ z → eval a (envOf (rg s x19) (mm s)) + z) valB))
  res .pLow c l =
    Eq.transport (λ z → mm z c Eq.≡ mm s c) (Eq.sym step2)
      (addSeq-low (fst s₂) (snd s₂) (rg s x20) hsp c l
       Eq.∙ (B .pLow c (Eq.transport (λ z → Lt c z) (Eq.sym (A .pSP))
                                     (lt-add 16 c (rg s x20) l))
             Eq.∙ A .pLow c l))


-- ==================================================================
-- §8  IT COMPUTES.
--
-- `x0 + x2` in a three-variable scope with the middle position DEAD,
-- the same witness `Compile.ArithToARM.Codegen` uses.  The emitted
-- code is real AArch64: two `ldr`s off x19, two `str`s onto the
-- operand stack, then the pop/pop/add/push of `addSeq`.
-- ==================================================================

open import Compile.ArithToARM.Codegen using (egap; enest; ugap; σ0)

_ : compile egap
  ≡ ldrO w9 x19 0 ∷ strPost w9 x20 16
  ∷ ldrO w9 x19 16 ∷ strPost w9 x20 16
  ∷ ldrPre w9 x20 16 ∷ ldrPre w10 x20 16 ∷ addR w9 w10 w9 ∷ strPost w9 x20 16
  ∷ []
_ = refl

-- a concrete machine: env base 0, stack base 1024, memory holding the
-- environment at offsets 0 / 8 / 16
mem0 : Mem
mem0 = setM 0 7 (setM 8 99 (setM 16 5 (λ _ → 0)))

regs0 : Regs
regs0 = setR x19 0 (setR x20 1024 (λ _ → 0))

st0 : St
st0 = regs0 , mem0

-- the answer lands at the incoming stack pointer ...
_ : mm (exec (compile egap) st0) 1024 ≡ 12
_ = refl

-- ... x19 is untouched, and exactly one slot was pushed
_ : rg (exec (compile egap) st0) x19 ≡ 0
_ = refl

_ : rg (exec (compile egap) st0) x20 ≡ 1040
_ = refl

-- ... and the environment survived, which is `pLow` at three addresses
_ : mm (exec (compile egap) st0) 0 ≡ 7
_ = refl

_ : mm (exec (compile egap) st0) 8 ≡ 99
_ = refl

_ : mm (exec (compile egap) st0) 16 ≡ 5
_ = refl

-- the nested example exercises `movI` as well
_ : mm (exec (compile enest) st0) 1024 ≡ 13
_ = refl

-- THE THEOREM ITSELF REDUCES at the witness, not merely inhabits
sep0 : Sep ugap st0
sep0 zero                _ = tt
sep0 (suc zero)          ()
sep0 (suc (suc zero))    _ = tt
sep0 (suc (suc (suc _))) ()

_ : correct egap st0 sep0 .pVal ≡ Eq.refl
_ = refl
