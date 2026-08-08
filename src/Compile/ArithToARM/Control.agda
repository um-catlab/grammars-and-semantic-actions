{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  CONTROL FLOW: A PROGRAM COUNTER, BRANCHES, AND CALL/RETURN.

  ------------------------------------------------------------------
  WHAT THIS FILE IS FOR
  ------------------------------------------------------------------

  `AArch64.exec` is a straight-line FOLD over a `List Instr`.  It has no
  program counter, so it cannot express a loop and it cannot express a
  call.  This file adds the counter in the most boring standard way --
  the CompCert/CakeML shape:

      programs stay lists, addressed by a `ℕ` counter;
      `stepPC` is one instruction;
      `run` iterates `stepPC` on FUEL.

  ------------------------------------------------------------------
  THE ONE THING THAT MATTERS: NOTHING IS RE-PROVED
  ------------------------------------------------------------------

  `AArch64Codegen.correct` is stated against `exec`.  It is NOT restated
  here.  Instead §6 proves the COMPATIBILITY THEOREM

      execAgrees : (p : CProg) → BranchFree p → (l : Word) (s : St)
                 → run (suc (length p)) p (0 , l , s)
                   Eq.≡ just (length p , l , exec (strip p) s)

  -- "on branch-free programs, the counter machine with enough fuel
  computes exactly what the fold computes" -- and every existing theorem
  transfers through it by a single `Eq.transport`.  `correctPC` in §8 is
  that transfer, and it is three lines.

  ------------------------------------------------------------------
  TWO DELIBERATE DEVIATIONS, BOTH SO THAT `AArch64.agda` IS UNTOUCHED
  ------------------------------------------------------------------

  (1) `CInstr` WRAPS `Instr` rather than extending it:

          data CInstr = base Instr | bra ℕ | cbz Reg ℕ | bl ℕ | blr Reg | ret

      so `Instr`, `exec1`, `exec`, `exec-app` and everything proved
      about them are literally unchanged, and `BranchFree` is exactly
      "every instruction is a `base`" -- i.e. "p is in the image of the
      old instruction set".  `strip` is the left inverse of that image.

  (2) THE LINK REGISTER LIVES IN THE CONFIGURATION, not in `Regs`:

          Conf = ℕ × Word × St        -- pc , lr , machine state

      Adding `x30` to `Reg` would force new clauses in `AArch64.regIx`,
      in `AArch64Emit`'s two printers, and -- the expensive one -- in
      `StateFib.regCases`, which is a 25-clause exhaustive table.  The
      counter is already outside `St`; the return address goes with it.
      It also says the honest thing: `lr` is interpretation-only, and no
      instruction that touches it is ever emitted.

  ------------------------------------------------------------------
  WHY `exec1` IS NOT CONSULTED FOR THE NEW INSTRUCTIONS
  ------------------------------------------------------------------

  These programs are INTERPRETED (via MAlonzo), not assembled, so for
  the control-flow constructs `stepI` IS the semantics; there is no
  external ISA for it to be unfaithful to.  The eight instructions that
  ARE assembled keep their meaning untouched, inside `base`.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1: this is the definition of a machine.
-}
open import Cubical.Foundations.Prelude

module Compile.ArithToARM.Control where

open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.List using (List; []; _∷_; _++_; length)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import Compile.ArithToARM.AArch64
open import Compile.ArithToARM.AArch64Codegen
  using (compile; Post; Sep; pX19; pSP; pVal; pLow; correct; st0; sep0)
open import Compile.ArithToARM.Codegen using (egap; enest; ugap)
open import Compile.ArithToARM.Base using (Exp)
import TheoryGrammar.Instances.LinLam.Syntax as L

-- ==================================================================
-- §1  THE EXTENDED INSTRUCTION SET.
--
-- Six constructors.  The first one is the whole of the old machine;
-- the other five are the control flow, and every branch target is an
-- ABSOLUTE index into the program -- the boring choice, and the one
-- that keeps `stepI` free of arithmetic.
-- ==================================================================

data CInstr : Type₀ where
  base : Instr → CInstr        -- one of the eight real instructions
  bra  : ℕ → CInstr            -- b    #target            unconditional
  cbz  : Reg → ℕ → CInstr      -- cbz  wr, #target        if wr = 0
  bl   : ℕ → CInstr            -- bl   #target            lr := pc+1
  blr  : Reg → CInstr          -- blr  xr                 lr := pc+1
  ret  : CInstr                -- ret                     pc := lr

CProg : Type₀
CProg = List CInstr

-- A CONFIGURATION.  `lr` sits beside the counter rather than inside
-- `St`; see the header.
Conf : Type₀
Conf = ℕ × Word × St

pc : Conf → ℕ
pc = fst

lr : Conf → Word
lr c = fst (snd c)

stOf : Conf → St
stOf c = snd (snd c)

-- ==================================================================
-- §2  FETCH.
--
-- The `[]` clause comes FIRST so that `instrAt n []` reduces at a
-- VARIABLE `n`; that single ordering choice is what makes the empty
-- case of `execAgrees` an `Eq.refl`.
-- ==================================================================

instrAt : ℕ → CProg → Maybe CInstr
instrAt n       []      = nothing
instrAt zero    (i ∷ _) = just i
instrAt (suc n) (_ ∷ p) = instrAt n p

-- ==================================================================
-- §3  ONE STEP.  PRIMITIVE (phase 1), and the trusted list -- but see
-- the header: only `base` is claimed to model hardware.
--
-- `stepI n i l s` is "instruction `i`, fetched at `n`, with link `l`
-- and state `s`".  Every clause names the NEXT counter first, so the
-- control flow of the machine is readable off six lines.
-- ==================================================================

stepI : ℕ → CInstr → Word → St → Conf
stepI n (base i) l s = suc n           , l     , exec1 i s
stepI n (bra t)  l s = t               , l     , s
stepI n (cbz r t) l s = ifB (eqℕ (rg s r) 0) t (suc n) , l , s
stepI n (bl t)   l s = t               , suc n , s
stepI n (blr r)  l s = rg s r          , suc n , s
stepI n ret      l s = l               , l     , s

-- fetch-and-step, split out so that `stepPC` reduces with the fetch
-- ABSTRACT -- which is what §5's shift lemma quantifies over
stepM : Maybe CInstr → ℕ → Word → St → Maybe Conf
stepM nothing  n l s = nothing
stepM (just i) n l s = just (stepI n i l s)

-- `nothing` = the counter is off the end of the program = HALT
stepPC : CProg → Conf → Maybe Conf
stepPC p (n , l , s) = stepM (instrAt n p) n l s

-- ==================================================================
-- §4  RUNNING ON FUEL.
--
-- `run f p c` iterates `stepPC` at most `f` times, STOPPING EARLY and
-- returning the halted configuration when the counter runs off the
-- end.
--
-- THE `Maybe` IS THE HALT STATE, and the two clauses that make it so
-- are worth reading against each other:
--
--     run zero    p c = nothing        -- out of fuel: NO ANSWER
--     runM f p nothing c = just c      -- off the end: HALTED, here
--
-- so `just d` means "this program FINISHED, in state `d`", and it can
-- only be produced by the counter leaving the program.  A machine that
-- returned the current configuration on fuel exhaustion could not tell
-- a program that terminated from one that looped, and then no theorem
-- it proves is a theorem about termination.  (§12 exhibits the
-- difference.)  Note that the halt clause does not consult the fuel,
-- so SURPLUS fuel is harmless -- which is what lets the tests below be
-- written without counting instructions exactly.
--
-- `runM` is separated out for the same reason `stepM` is: §5 needs to
-- reason about `run` with the STEP abstract.
-- ==================================================================

run  : ℕ → CProg → Conf → Maybe Conf
runM : ℕ → CProg → Maybe Conf → Conf → Maybe Conf

run zero    p c = nothing
run (suc f) p c = runM f p (stepPC p c) c

runM f p nothing  c = just c
runM f p (just d) c = run f p d

-- shifting the counter of a possibly-absent configuration
mapPC : (ℕ → ℕ) → Maybe Conf → Maybe Conf
mapPC g nothing            = nothing
mapPC g (just (n , l , s)) = just (g n , l , s)

-- ==================================================================
-- §5  BRANCH-FREEDOM, AND THE SHIFT LEMMA.
--
-- `BranchFree` is `Unit`/`⊥`-valued, so a proof of it is `tt` and
-- never blocks a reduction, and `strip` is its left inverse onto the
-- old `Prog`.
--
-- The shift lemma is the only real content in this file:
--
--     running `i ∷ p` from counter `suc n`
--   = running `p` from counter `n`, with every counter shifted up.
--
-- It is proved by induction on FUEL ALONE.  The two case analyses that
-- would otherwise need a `with` -- on the fetched instruction, and on
-- whether the machine halted -- are pushed into `stepShiftM` and
-- `runShift`, each of which takes the thing it cases on as an explicit
-- argument.  `runShift` takes the induction hypothesis as a FUNCTION,
-- which keeps `shift` structurally recursive rather than mutual.
-- ==================================================================

BranchFree : CProg → Type₀
BranchFree []              = Unit
BranchFree (base _ ∷ p)    = BranchFree p
BranchFree (bra _  ∷ _)    = ⊥
BranchFree (cbz _ _ ∷ _)   = ⊥
BranchFree (bl _   ∷ _)    = ⊥
BranchFree (blr _  ∷ _)    = ⊥
BranchFree (ret    ∷ _)    = ⊥

strip : CProg → Prog
strip []            = []
strip (base i ∷ p)  = i ∷ strip p
strip (_ ∷ p)       = strip p

-- "the fetch is a `base`, or there is no fetch"
IsBaseM : Maybe CInstr → Type₀
IsBaseM nothing         = Unit
IsBaseM (just (base _)) = Unit
IsBaseM (just (bra _))  = ⊥
IsBaseM (just (cbz _ _)) = ⊥
IsBaseM (just (bl _))   = ⊥
IsBaseM (just (blr _))  = ⊥
IsBaseM (just ret)      = ⊥

bfNth : (p : CProg) → BranchFree p → (n : ℕ) → IsBaseM (instrAt n p)
bfNth []             bf n       = tt
bfNth (base i ∷ p)   bf zero    = tt
bfNth (base i ∷ p)   bf (suc n) = bfNth p bf n
bfNth (bra _ ∷ p)    ()   n
bfNth (cbz _ _ ∷ p)  ()   n
bfNth (bl _ ∷ p)     ()   n
bfNth (blr _ ∷ p)    ()   n
bfNth (ret ∷ p)      ()   n

-- one step commutes with the shift, PROVIDED the fetch is a `base`
stepShiftM : (m : Maybe CInstr) → IsBaseM m → (n : ℕ) (l : Word) (s : St)
           → stepM m (suc n) l s Eq.≡ mapPC suc (stepM m n l s)
stepShiftM nothing         bm n l s = Eq.refl
stepShiftM (just (base i)) bm n l s = Eq.refl
stepShiftM (just (bra _))   () n l s
stepShiftM (just (cbz _ _)) () n l s
stepShiftM (just (bl _))    () n l s
stepShiftM (just (blr _))   () n l s
stepShiftM (just ret)       () n l s

stepShift : (i : CInstr) (p : CProg) → BranchFree p → (n : ℕ) (l : Word) (s : St)
          → stepPC (i ∷ p) (suc n , l , s) Eq.≡ mapPC suc (stepPC p (n , l , s))
stepShift i p bf n l s = stepShiftM (instrAt n p) (bfNth p bf n) n l s

-- the halt/continue case analysis, with the induction hypothesis
-- supplied rather than taken recursively
runShift : (f : ℕ) (i : CInstr) (p : CProg) (n : ℕ) (l : Word) (s : St)
           (md : Maybe Conf)
         → ((n' : ℕ) (l' : Word) (s' : St)
            → run f (i ∷ p) (suc n' , l' , s') Eq.≡ mapPC suc (run f p (n' , l' , s')))
         → runM f (i ∷ p) (mapPC suc md) (suc n , l , s)
           Eq.≡ mapPC suc (runM f p md (n , l , s))
runShift f i p n l s nothing            ih = Eq.refl
runShift f i p n l s (just (n' , l' , s')) ih = ih n' l' s'

shift : (f : ℕ) (i : CInstr) (p : CProg) → BranchFree p
      → (n : ℕ) (l : Word) (s : St)
      → run f (i ∷ p) (suc n , l , s) Eq.≡ mapPC suc (run f p (n , l , s))
shift zero    i p bf n l s = Eq.refl
shift (suc f) i p bf n l s =
  Eq.ap (λ z → runM f (i ∷ p) z (suc n , l , s)) (stepShift i p bf n l s)
  Eq.∙ runShift f i p n l s (stepPC p (n , l , s)) (shift f i p bf)

-- ==================================================================
-- §6  THE COMPATIBILITY THEOREM.
--
--     on BRANCH-FREE programs, `run` with enough fuel agrees with
--     `exec`
--
-- Two clauses.  Note what is NOT here: no arithmetic lemma, no list
-- lemma, no `subst` at a variable index.  That is because the counter
-- is stated RELATIVE to the step just taken (`shift` moves it by one)
-- rather than against an absolute position, which is the same move
-- that makes `AArch64Codegen.Post` short.
-- ==================================================================

execAgrees : (p : CProg) → BranchFree p → (l : Word) (s : St)
           → run (suc (length p)) p (0 , l , s)
             Eq.≡ just (length p , l , exec (strip p) s)
execAgrees []           bf l s = Eq.refl
execAgrees (base i ∷ p) bf l s =
  shift (suc (length p)) (base i) p bf 0 l (exec1 i s)
  Eq.∙ Eq.ap (mapPC suc) (execAgrees p bf l (exec1 i s))
execAgrees (bra _ ∷ p)   () l s
execAgrees (cbz _ _ ∷ p) () l s
execAgrees (bl _ ∷ p)    () l s
execAgrees (blr _ ∷ p)   () l s
execAgrees (ret ∷ p)     () l s

-- ==================================================================
-- §7  THE SAME THEOREM ALONG THE INCLUSION `Prog ↪ CProg`.
--
-- `emb` is the image `BranchFree` describes, and `strip ∘ emb = id`.
-- Stating the agreement directly at `emb p` avoids transporting along
-- `strip (emb p) ≡ p` and `length (emb p) ≡ length p`, which would put
-- a `subst` at a variable list into every downstream `refl` test.  The
-- proof is the same two lines.
-- ==================================================================

emb : Prog → CProg
emb []      = []
emb (i ∷ p) = base i ∷ emb p

emb-bf : (p : Prog) → BranchFree (emb p)
emb-bf []      = tt
emb-bf (i ∷ p) = emb-bf p

runEmb : (p : Prog) (l : Word) (s : St)
       → run (suc (length p)) (emb p) (0 , l , s)
         Eq.≡ just (length p , l , exec p s)
runEmb []      l s = Eq.refl
runEmb (i ∷ p) l s =
  shift (suc (length p)) (base i) (emb p) (emb-bf p) 0 l (exec1 i s)
  Eq.∙ Eq.ap (mapPC suc) (runEmb p l (exec1 i s))

-- ==================================================================
-- §8  THE COROLLARY: `AArch64Codegen.correct`, ON THE COUNTER MACHINE.
--
-- `PostM` is `Post` lifted along `Maybe`, `⊥` at `nothing`; so the
-- statement also says "the fuel sufficed".  The proof is one
-- `Eq.transport` along §7 -- the codegen theorem is used as a BLACK
-- BOX and not touched.
-- ==================================================================

PostM : ∀ {u : L.Usage} → Exp u → St → Maybe Conf → Type₀
PostM e s nothing            = ⊥
PostM e s (just (_ , _ , s')) = Post e s s'

correctPC : ∀ {u} (e : Exp u) (s : St) (l : Word) → Sep u s
          → PostM e s (run (suc (length (compile e))) (emb (compile e)) (0 , l , s))
correctPC e s l sep =
  Eq.transport (λ z → PostM e s z) (Eq.sym (runEmb (compile e) l s))
               (correct e s sep)

-- ==================================================================
-- §9  IT COMPUTES: THE COMPILED ARITHMETIC, UNDER `run`.
--
-- The same witnesses and the same numbers as `AArch64Codegen`'s §8, so
-- the two machines can be compared by eye as well as by §6.
-- ==================================================================

memOf : Maybe Conf → Word → Word
memOf nothing            a = 0
memOf (just (_ , _ , s)) a = mm s a

regOf : Maybe Conf → Reg → Word
regOf nothing            r = 0
regOf (just (_ , _ , s)) r = rg s r

pcOf : Maybe Conf → ℕ
pcOf nothing            = 0
pcOf (just (n , _ , _)) = n

gapRun : Maybe Conf
gapRun = run 20 (emb (compile egap)) (0 , 0 , st0)

-- the answer still lands at the incoming stack pointer ...
_ : memOf gapRun 1024 ≡ 12
_ = refl

-- ... exactly one slot was pushed, x19 is untouched ...
_ : regOf gapRun x20 ≡ 1040
_ = refl

_ : regOf gapRun x19 ≡ 0
_ = refl

-- ... the environment survived ...
_ : memOf gapRun 0 ≡ 7
_ = refl

_ : memOf gapRun 16 ≡ 5
_ = refl

-- ... and the machine halted just past the last instruction
_ : pcOf gapRun ≡ 8
_ = refl

_ : memOf (run 20 (emb (compile enest)) (0 , 0 , st0)) 1024 ≡ 13
_ = refl

-- THE COMPATIBILITY THEOREM ITSELF REDUCES at the witness
_ : runEmb (compile egap) 0 st0 ≡ Eq.refl
_ = refl

-- ... and so does the transferred codegen theorem
_ : correctPC egap st0 0 sep0 .pVal ≡ Eq.refl
_ = refl

-- ==================================================================
-- §10  IT COMPUTES: A PROGRAM THAT ACTUALLY BRANCHES.
--
-- Sum a zero-terminated array.  This is a genuine loop -- backward
-- `bra`, `cbz` exit test, pointer bumped by `addI` -- and it runs on
-- the SAME eight arithmetic instructions, which is the point: the
-- control flow is the only thing that is new.
--
--     0  ldr  w9, [x19]        load the current element
--     1  cbz  w9, #5           zero terminator?  leave
--     2  add  w10, w10, w9     accumulate
--     3  add  x19, x19, #8     bump the pointer
--     4  b    #0               round again
--     5                        (off the end = halt)
-- ==================================================================

sumProg : CProg
sumProg = base (ldrO w9 x19 0)
        ∷ cbz w9 5
        ∷ base (addR w10 w10 w9)
        ∷ base (addI x19 x19 8)
        ∷ bra 0
        ∷ []

-- 3 , 4 , 5 , 0 at offsets 0 / 8 / 16 / 24 (the default memory is 0,
-- so the terminator is free)
arr : Mem
arr = setM 0 3 (setM 8 4 (setM 16 5 (λ _ → 0)))

sumSt : St
sumSt = (λ _ → 0) , arr

sumRun : Maybe Conf
sumRun = run 40 sumProg (0 , 0 , sumSt)

_ : regOf sumRun w10 ≡ 12
_ = refl

-- the loop LEFT, at the exit target, rather than running out of fuel
_ : pcOf sumRun ≡ 5
_ = refl

-- `sumProg` is not branch-free, and that is a computation, not a claim
_ : BranchFree sumProg ≡ ⊥
_ = refl

-- ==================================================================
-- §11  IT COMPUTES: CALL AND RETURN.
--
--     0  mov  w9, #21
--     1  bl   #3               lr := 2 , jump to the callee
--     2  b    #5               (returned here)  halt
--     3  add  w9, w9, w9       the callee
--     4  ret                   pc := lr = 2
-- ==================================================================

callProg : CProg
callProg = base (movI w9 21)
         ∷ bl 3
         ∷ bra 5
         ∷ base (addR w9 w9 w9)
         ∷ ret
         ∷ []

_ : regOf (run 20 callProg (0 , 0 , sumSt)) w9 ≡ 42
_ = refl

_ : pcOf (run 20 callProg (0 , 0 , sumSt)) ≡ 5
_ = refl

-- the same, through a register-indirect call (`blr`), which is what a
-- closure's code pointer will need
indProg : CProg
indProg = base (movI w0 4)
        ∷ base (movI w9 21)
        ∷ blr w0
        ∷ bra 6
        ∷ base (addR w9 w9 w9)
        ∷ ret
        ∷ []

_ : regOf (run 20 indProg (0 , 0 , sumSt)) w9 ≡ 42
_ = refl

_ : pcOf (run 20 indProg (0 , 0 , sumSt)) ≡ 6
_ = refl

-- ==================================================================
-- §12  THE HALT STATE, AND FUEL.
--
-- `run zero p c = nothing` is what buys the distinction §4 claims, and
-- these three lines are the claim as a computation: a program that
-- terminates answers `just` however much fuel is left over, a program
-- that loops answers `nothing` however much fuel it is given, and a
-- terminating program starved of fuel answers `nothing` too.
--
-- `runMono` is the other half: an ANSWER, once obtained, is stable
-- under more fuel -- so "enough fuel" is a well-behaved notion and the
-- specific number in `execAgrees` is a bound, not a coincidence.  It
-- is the same shape as §5: induction on fuel alone, with the case
-- analysis on the step pushed into a helper that receives the
-- induction hypothesis as an argument.
-- ==================================================================

isJust : Maybe Conf → Type₀
isJust nothing  = ⊥
isJust (just _) = Unit

runMonoM : (f : ℕ) (p : CProg) (c d : Conf) (md : Maybe Conf)
         → ((c' : Conf) → run f p c' Eq.≡ just d → run (suc f) p c' Eq.≡ just d)
         → runM f p md c Eq.≡ just d
         → runM (suc f) p md c Eq.≡ just d
runMonoM f p c d nothing  ih h = h
runMonoM f p c d (just e) ih h = ih e h

runMono : (f : ℕ) (p : CProg) (c d : Conf)
        → run f p c Eq.≡ just d → run (suc f) p c Eq.≡ just d
runMono zero    p c d h = E.rec (Eq.transport isJust (Eq.sym h) tt)
runMono (suc f) p c d h =
  runMonoM f p c d (stepPC p c) (λ c' → runMono f p c' d) h

-- a program that never leaves: `nothing`, at any fuel
loopProg : CProg
loopProg = bra 0 ∷ []

_ : run 100 loopProg (0 , 0 , sumSt) ≡ nothing
_ = refl

-- a program that DOES leave, starved: also `nothing` ...
_ : run 3 sumProg (0 , 0 , sumSt) ≡ nothing
_ = refl

-- ... and fed: `just`, and the surplus changed nothing
_ : run 40 sumProg (0 , 0 , sumSt) ≡ run 400 sumProg (0 , 0 , sumSt)
_ = refl
