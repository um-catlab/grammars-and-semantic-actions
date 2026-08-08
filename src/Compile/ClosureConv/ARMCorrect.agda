{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  TOWARDS THE CORRECTNESS OF `ClosureConv.ARM`: THE SIMULATION TOOLKIT,
  THE REALISATION RELATION, AND AN HONEST ACCOUNT OF WHAT IS LEFT.

  ------------------------------------------------------------------
  1.  WHY THIS IS NOT `AArch64Codegen.correct` WITH DIFFERENT LETTERS
  ------------------------------------------------------------------

  `AArch64Codegen.correct` is an EQUATION ON A FOLD:

      Post e s (exec (compile e) s)

  and it can be, because `exec` is a fold over a list and `compile` is a
  fold over an `Exp`.  Neither survives here.

    * `Control.run` is FUEL-BASED and stops when the counter leaves the
      program, so there is no fold to state an equation about.  A
      backward `blr` is not a suffix of anything.
    * `IR`'s semantics is a BIG-STEP RELATION (`Ev`), not a function of
      the term: the body of a call is not a subterm, and the number of
      machine steps is a function of the DERIVATION.

  So the statement has to be a SIMULATION ACROSS FUEL: from a derivation
  `Ev T σ e v`, produce a step count `n` and a machine transition of
  exactly `n` steps.  §2 is the toolkit that makes such a statement
  composable, and it is proved in full.

  ------------------------------------------------------------------
  2.  AND NOT AN EQUATION ON ANSWERS, EITHER
  ------------------------------------------------------------------

  `Correct.noNoseSquare` already refutes the on-the-nose square one
  level up, and the machine inherits the refutation with interest: a
  target answer here is a machine WORD -- a heap address -- and

      which address a value lands at depends on the allocation history,
      which depends on the whole program

  exactly as a block index depends on the whole table.  So the relation
  between a `Val` and a machine word is `RealV` of §4, and it is
  `Correct.RelV` with "block index" replaced by "code address" and
  "`capVals` list" by "consecutive record fields".  `ARM.decodeV` is a
  FUNCTION in the same relation, at a fixed program; §11 of `ARM.agda`
  pins it at three witnesses.

  ------------------------------------------------------------------
  3.  WHAT IS PROVED HERE, AND WHAT IS NOT
  ------------------------------------------------------------------

  PROVED, no holes:

    * §2  `Steps`, the exact-length transition relation, with
          composition (`stepsTrans`), extraction into `run`
          (`stepsRun`, `runFromSteps`), and the halt lemma.
    * §3  `CodeAt`, "this program sits at this address", with the two
          splitting lemmas and `codeAtSuffix`.
    * §3  `runBase` -- THE GENERALISATION OF `Control.execAgrees` THAT
          IS ACTUALLY USABLE HERE.  `execAgrees` is stated for a whole
          branch-free program starting at counter 0; every branch-free
          stretch this compiler emits sits at an OFFSET inside a program
          that is not branch-free.  `runBase` says such a stretch runs
          as `AArch64.exec` runs it, and it is four lines.
    * §5  three arithmetic facts about `_+_`, which is three more than
          the rest of the development needs.  They are unavoidable here
          because `CodeAt` walks a program with `suc` on the address
          while `_++_` measures with `length _ + _`.

  NOT PROVED, and the holes are marked:

    * §6  `simulate`, the simulation itself.  Its STATEMENT is complete
          and is the thing to attack; §7 says what each of its three
          cases needs.
    * §7  the RESOURCE hypothesis, which is not bookkeeping and is the
          most interesting thing this file found.  See below.

  ------------------------------------------------------------------
  4.  THE OBSTRUCTION THIS FILE FOUND: THE TWO REGIONS CAN COLLIDE
  ------------------------------------------------------------------

  `AArch64Codegen`'s `Post` gets away with two memory clauses -- "x20 is
  16 + old x20" and "memory below old x20 is untouched" -- because it
  has ONE growing region.  This machine has TWO: the operand stack
  (`x20`, upward) and the heap (`w0`, upward), and the CALLER needs both

      everything below SP survives            (its own stack)
      everything below HP survives            (the closures it allocated)

  Those two cannot both be phrased as "below a pointer" unless the
  regions are known DISJOINT, because HP is above SP: "below HP"
  includes the callee's scratch stack, which is not preserved.  So the
  postcondition must carry a separation hypothesis

      Lt (high-water mark of the stack) heapBase

  and the high-water mark is a function of the DERIVATION (call depth
  times 32 plus operand depth), not of the term.  This is not an
  artefact of the layout: a bump allocator and a stack in one flat
  `Word → Word` memory can genuinely collide, and a total correctness
  theorem for such a machine must say so.  `Sep` in §6 is where it is
  carried; `SepGrows` is the obligation it generates and is the reason
  the `⇓call` case is the hard one.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1: metatheorems about a machine and a compiler.
-}
open import Cubical.Foundations.Prelude

module Compile.ClosureConv.ARMCorrect where

open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.List using (List; []; _∷_; _++_; length)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import Compile.ArithToARM.AArch64 hiding (Prog)
import Compile.ArithToARM.AArch64 as A
open import Compile.ArithToARM.Control
open import Compile.ClosureConv.Convert
open import Compile.ClosureConv.ARM
open import Compile.ClosureConv.Names using (LiveAt)

-- ==================================================================
-- §1  THREE ARITHMETIC FACTS.
--
-- The development owns none anywhere else, and it is worth saying why
-- it needs them here.  `CodeAt` walks a program one instruction at a
-- time, so its address grows by `suc`; `_++_` measures a segment as
-- `length q + a`.  Reconciling `length q + suc a` with
-- `suc (length q + a)` is `+suc`, and nothing else in this file is
-- arithmetic.  All three are in Eq-world and compute on literals.
-- ==================================================================

+suc : (m n : ℕ) → m + suc n Eq.≡ suc (m + n)
+suc zero    n = Eq.refl
+suc (suc m) n = Eq.ap suc (+suc m n)

+zero : (m : ℕ) → m + 0 Eq.≡ m
+zero zero    = Eq.refl
+zero (suc m) = Eq.ap suc (+zero m)

+comm : (m n : ℕ) → m + n Eq.≡ n + m
+comm m zero    = +zero m
+comm m (suc n) = +suc m n Eq.∙ Eq.ap suc (+comm m n)

-- ==================================================================
-- §2  `Steps`: THE MACHINE TRANSITION OF AN EXACT LENGTH.
--
-- `run` answers `Maybe Conf` and conflates "still going" with "no
-- fuel", which is exactly right as an OBSERVATION (`Control.agda` §4)
-- and useless as an induction hypothesis.  `Steps p n c d` is the
-- missing intermediate: "`p` takes `c` to `d` in exactly `n` steps",
-- with no claim about halting.
--
-- It is a RECURSIVE FAMILY rather than a `data`, so that `Steps p 0`
-- is definitionally an equation and `stepsTrans`' zero case is a
-- pattern match rather than a transport.
-- ==================================================================

Steps : CProg → ℕ → Conf → Conf → Type₀
Steps p zero    c d = c Eq.≡ d
Steps p (suc n) c d = Σ[ e ∈ Conf ] ((stepPC p c Eq.≡ just e) × Steps p n e d)

steps1 : (p : CProg) (c d : Conf) → stepPC p c Eq.≡ just d → Steps p 1 c d
steps1 p c d h = d , h , Eq.refl

-- COMPOSITION.  The lengths add on the LEFT, which is the side `_+_`
-- recurses on, so `suc m + n` reduces and the proof is two clauses.
stepsTrans : (p : CProg) (m n : ℕ) (c d e : Conf)
           → Steps p m c d → Steps p n d e → Steps p (m + n) c e
stepsTrans p zero    n c d e Eq.refl        q = q
stepsTrans p (suc m) n c d e (c' , h , r)   q =
  c' , h , stepsTrans p m n c' d e r q

-- EXTRACTION.  A `Steps` prefix is fuel spent: whatever `run` says
-- from `d`, it says from `c` with `n` more units.  This is the only
-- place the two notions of "running" meet.
stepsRun : (p : CProg) (n f : ℕ) (c d : Conf) (r : Maybe Conf)
         → Steps p n c d → run f p d Eq.≡ r → run (n + f) p c Eq.≡ r
stepsRun p zero    f c d r Eq.refl      h = h
stepsRun p (suc n) f c d r (c' , hs , st) h =
  Eq.ap (λ z → runM (n + f) p z c) hs Eq.∙ stepsRun p n f c' d r st h

-- HALTING is the counter leaving the program, and one unit of fuel
-- observes it (`Control.agda` §4: the halt clause does not consult the
-- fuel, so surplus is harmless).
haltAt : (p : CProg) (d : Conf) → instrAt (pc d) p Eq.≡ nothing
       → run 1 p d Eq.≡ just d
haltAt p (n , l , s) h = Eq.ap (λ z → runM 0 p (stepM z n l s) (n , l , s)) h

-- ... and the two together are the shape a whole-program theorem has.
runFromSteps : (p : CProg) (n : ℕ) (c d : Conf)
             → Steps p n c d → instrAt (pc d) p Eq.≡ nothing
             → run (n + 1) p c Eq.≡ just d
runFromSteps p n c d st h = stepsRun p n 1 c d (just d) st (haltAt p d h)

-- ==================================================================
-- §3  `CodeAt`: WHERE A PIECE OF CODE SITS.
--
-- `Control.shift` prepends ONE instruction to a BRANCH-FREE program;
-- that is the right lemma when branch targets are relative and the
-- wrong one when they are absolute, which they are here.  With
-- absolute targets a segment does not need to be relocated -- it needs
-- to be LOCATED, and `CodeAt p a q` is that: `q` is what `p` fetches
-- from `a` onwards.
--
-- `Unit`/`Σ`-valued, so a proof of it computes and never blocks.
-- ==================================================================

CodeAt : CProg → ℕ → CProg → Type₀
CodeAt p a []      = Unit
CodeAt p a (i ∷ q) = (instrAt a p Eq.≡ just i) × CodeAt p (suc a) q

codeAtL : (p : CProg) (q₁ q₂ : CProg) (a : ℕ)
        → CodeAt p a (q₁ ++ q₂) → CodeAt p a q₁
codeAtL p []       q₂ a h       = tt
codeAtL p (i ∷ q₁) q₂ a (h , r) = h , codeAtL p q₁ q₂ (suc a) r

codeAtR : (p : CProg) (q₁ q₂ : CProg) (a : ℕ)
        → CodeAt p a (q₁ ++ q₂) → CodeAt p (length q₁ + a) q₂
codeAtR p []       q₂ a h       = h
codeAtR p (i ∷ q₁) q₂ a (_ , r) =
  Eq.transport (λ z → CodeAt p z q₂) (+suc (length q₁) a)
               (codeAtR p q₁ q₂ (suc a) r)

-- locating a program inside itself: the pointwise fetch agreement
codeAtHere : (p q : CProg) (a : ℕ)
           → ((k : ℕ) → instrAt (k + a) p Eq.≡ instrAt k q) → CodeAt p a q
codeAtHere p []      a h = tt
codeAtHere p (i ∷ q) a h =
  h 0 , codeAtHere p q (suc a)
          (λ k → Eq.transport (λ z → instrAt z p Eq.≡ instrAt k q)
                              (Eq.sym (+suc k a)) (h (suc k)))

instrAt-++ʳ : (q₁ q₂ : CProg) (a : ℕ)
            → instrAt (length q₁ + a) (q₁ ++ q₂) Eq.≡ instrAt a q₂
instrAt-++ʳ []       q₂ a = Eq.refl
instrAt-++ʳ (i ∷ q₁) q₂ a = instrAt-++ʳ q₁ q₂ a

codeAtSuffix : (q₁ q₂ : CProg) → CodeAt (q₁ ++ q₂) (length q₁) q₂
codeAtSuffix q₁ q₂ =
  codeAtHere (q₁ ++ q₂) q₂ (length q₁)
    (λ k → Eq.transport (λ z → instrAt z (q₁ ++ q₂) Eq.≡ instrAt k q₂)
                        (+comm (length q₁) k) (instrAt-++ʳ q₁ q₂ k))

codeAtPrefix : (q₁ q₂ : CProg) → CodeAt (q₁ ++ q₂) 0 q₁
codeAtPrefix q₁ q₂ = codeAtL (q₁ ++ q₂) q₁ q₂ 0 (codeAtSuffix [] (q₁ ++ q₂))

-- ------------------------------------------------------------------
-- ONE BASE INSTRUCTION, AND THEN THE GENERALISATION OF `execAgrees`.
--
-- `Control.execAgrees` transfers `AArch64Codegen.correct` to the
-- counter machine, but only for a WHOLE branch-free program at counter
-- 0.  Every branch-free stretch this compiler emits -- and that is all
-- of them except `blr` -- sits at an offset in a program that branches.
-- `runBase` is the statement that survives: a located stretch of
-- `base` instructions runs as `AArch64.exec` runs it, so every
-- straight-line fact about the emitted code is still `exec1`
-- computation and nothing new is trusted.
-- ------------------------------------------------------------------

stepBase : (p : CProg) (i : Instr) (a : ℕ) (l : Word) (s : St)
         → instrAt a p Eq.≡ just (base i)
         → Steps p 1 (a , l , s) (suc a , l , exec1 i s)
stepBase p i a l s h = _ , Eq.ap (λ z → stepM z a l s) h , Eq.refl

runBase : (p : CProg) (q : A.Prog) (a : ℕ) (l : Word) (s : St)
        → CodeAt p a (emb q)
        → Steps p (length q) (a , l , s) (length q + a , l , exec q s)
runBase p []      a l s h       = Eq.refl
runBase p (i ∷ q) a l s (h , r) =
  stepsTrans p 1 (length q) (a , l , s) (suc a , l , exec1 i s)
             (suc (length q + a) , l , exec q (exec1 i s))
    (stepBase p i a l s h)
    (Eq.transport
       (λ z → Steps p (length q) (suc a , l , exec1 i s)
                     (z , l , exec q (exec1 i s)))
       (+suc (length q) a)
       (runBase p q (suc a) l (exec1 i s) r))

-- ==================================================================
-- §4  THE REALISATION RELATION.
--
-- `Correct.RelV` relates a source value to a `Val` with respect to a
-- TABLE, because a block index means nothing without one.  One level
-- down the same thing is true of a machine word, with respect to a
-- PROGRAM: `rmv` says the record's field 0 is the code address the
-- layout assigns to block `i`, and its fields 1.. realise the captured
-- values -- positionally, which is the machine's form of
-- `Names.spreadIdCap`.
--
-- Two families rather than a family and a recursive function, so the
-- positivity checker has nothing to think about.
-- ==================================================================

data RealV  (P : Prog) (μ : Mem) : Word → Val → Type₀
data RealVs (P : Prog) (μ : Mem) : Word → ℕ → List Val → Type₀

data RealV P μ where
  rmv : ∀ {a i vs}
      → μ a Eq.≡ addrOf P i          -- field 0 IS block `i`'s code
      → RealVs P μ a 1 vs            -- fields 1.. are the environment
      → RealV P μ a (clos i vs)

data RealVs P μ where
  rmnil  : ∀ {a j} → RealVs P μ a j []
  rmcons : ∀ {a j v vs}
         → RealV P μ (μ (a + off8 j)) v
         → RealVs P μ a (suc j) vs
         → RealVs P μ a j (v ∷ vs)

-- ------------------------------------------------------------------
-- THE FRAME, ON THE MACHINE.  `Ev` reads `σ p`; the machine reads
-- `mSlot`, and the two definitions are the same case split -- position
-- 0 is the activation record's argument field, position `suc q` is a
-- load THROUGH the environment pointer at the packed index `packIx`
-- computes.  Compare `IR.callFrame` = `extF va (spread sh vs)`.
-- ------------------------------------------------------------------

mSlot : Usage → Mem → Word → ℕ → Word
mSlot sh μ f zero    = μ (f + fARG)
mSlot sh μ f (suc q) = μ (μ (f + fENV) + off8 (suc (packIx sh q)))

-- "the machine's frame at FP realises σ, on every slot `u` says is live"
RealF : Prog → Usage → Mem → Word → Frame → Usage → Type₀
RealF P sh μ f σ u = (p : ℕ) → LiveAt p u → RealV P μ (mSlot sh μ f p) (σ p)

-- ==================================================================
-- §5  SEPARATION, AND WHY IT IS A HYPOTHESIS AND NOT A LEMMA.
--
-- See the header §4.  `Sep hb s` says the stack pointer is below the
-- heap base and the heap pointer is above it: the two regions of the
-- one flat memory have not met.  It is an ASSUMPTION about resources,
-- like `AArch64Codegen.Sep`, but unlike that one it is not preserved
-- for free -- a call pushes 32 bytes, so `⇓call` must re-establish it
-- one activation record higher, and the bound it needs is a function
-- of the derivation's call depth.
-- ==================================================================

Sep : Word → St → Type₀
Sep hb s = Lt (rg s x20) hb × Lt hb (rg s w0)

-- ------------------------------------------------------------------
-- THE POSTCONDITION.  Four clauses, all RELATIVE to the incoming
-- state, which is `AArch64Codegen.Post`'s discipline and the reason
-- that record is short.
--
--   qFP   the frame pointer is restored -- a call is transparent
--   qSP   EXACTLY one slot is pushed    -- the invariant of `ARM.agda`
--   qVal  ... and it realises the value the big-step semantics gives
--   qLow  memory strictly below the incoming SP is untouched
--   qHeap the heap allocated so far is untouched, and HP only grew
--
-- `qLow` and `qHeap` are two clauses and not one exactly because there
-- are two growing regions; see the header.
-- ------------------------------------------------------------------

record QPost (P : Prog) (v : Val) (s s' : St) : Type₀ where
  field
    qFP   : rg s' x19 Eq.≡ rg s x19
    qSP   : rg s' x20 Eq.≡ 8 + rg s x20
    qVal  : RealV P (mm s') (mm s' (rg s x20)) v
    qLow  : (a : Word) → Lt a (rg s x20) → mm s' a Eq.≡ mm s a
    qHeap : (a : Word) → Lt a (rg s w0) → Lt (rg s x20) a
          → mm s' a Eq.≡ mm s a

open QPost public

-- ==================================================================
-- §6  THE SIMULATION.  THE STATEMENT IS COMPLETE; THE PROOF IS NOT.
--
-- Read the conclusion first.  From a big-step derivation it produces
--
--     a STEP COUNT `n`         -- fuel, as a function of the derivation
--     a final state `s'`
--     `Steps` of exactly that length, from the code's own address to
--       one past its last instruction (`sizeE e + pc`, which is
--       `ARM.sizeIsLength` spent)
--     and `QPost`.
--
-- That is the shape §1 of the header argued for: a simulation across
-- fuel, not an equation on a fold.
-- ==================================================================

Simulation : Type₀
Simulation =
    (P : Prog) (sh : Usage) (σ : Frame) {u : Usage} (e : IR u) (v : Val)
    (a : ℕ) (l : Word) (s : St) (hb : Word)
  → Ev (P .fst) σ e v                                   -- the source runs
  → CodeAt (compileC P) a (emitE (addrOf P) sh a e)     -- the code is here
  → RealF P sh (mm s) (rg s x19) σ u                    -- the frame realises σ
  → Sep hb s                                            -- the regions are apart
  → Σ[ n ∈ ℕ ] Σ[ s' ∈ St ]
      ( Steps (compileC P) n (a , l , s) (sizeE e + a , l , s')
      × QPost P v s s'
      × Sep hb s' )

-- ------------------------------------------------------------------
-- THE HOLE.  One hole, deliberately at the top rather than three at
-- the leaves: filling it needs the three lemmas §7 names, and stubbing
-- the two easy cases while the third is open would misreport where the
-- difficulty is (this repository's own standing complaint about
-- headers that go stale).
-- ------------------------------------------------------------------

simulate : Simulation
simulate = {!!}

-- ==================================================================
-- §7  WHAT EACH CASE NEEDS.  Written out because the statement above
-- is only useful if the next person knows where to push.
--
--  (a) `⇓var`.  `emitE` emits `loadSlot sh p` then a push, all `base`
--      instructions -- and `loadSlot ... ++ (push ∷ [])` is
--      DEFINITIONALLY `emb` of a `Prog`, so §3's `runBase` applies with
--      no coercion and the machine part of the case is `exec1`
--      computation plus `setM-hit`/`setM-miss`: `AArch64Codegen`'s
--      `evar` clause, one indirection deeper.  `mSlot` was defined so
--      that the address agreement is `Eq.refl` at `p = 0` and one
--      `ldrO` at `p = suc q`.
--
--      BUT IT IS NOT FREE, and the reason is worth recording, because
--      it is a fact about `RealV` and not about `ivar`.  The push
--      WRITES MEMORY, so `qVal` needs `RealV` at `mm s'` while `RealF`
--      supplies it at `mm s`, and `RealV` as defined in §4 is NOT
--      stable under a memory change: nothing in it says WHERE it reads.
--      The repair is to bound it --
--
--          rmv : Lt a (heap pointer) → ... → RealV P μ a (clos i vs)
--
--      -- so that "memory unchanged below HP" (`qHeap`) can be pushed
--      through the record and its fields.  That extra field is a
--      prerequisite for ALL THREE cases, not just this one, and it is
--      the first thing to add.
--
--  (b) `⇓clos`.  Also entirely `base`, so also `runBase`; the content
--      is an induction over `capPos cap` showing `emitCap` writes
--      `capVals σ cap` into consecutive fields.  The two recursions
--      were written clause-for-clause parallel (`ARM.agda` §2) so this
--      is a plain induction -- but it needs `qLow`-style
--      non-interference for the record under construction, because the
--      loads that fill field `j` may not disturb fields `< j`.
--      `setM-miss` at `off8`, as in `addSeq-low`.
--
--  (c) `⇓call`.  THE ONE THAT IS NOT BOOKKEEPING.  It composes five
--      `Steps`: the callee's code, the argument's code, the ten `base`
--      instructions of `callSeq` before the `blr`, the CALLEE'S OWN
--      simulation (the induction hypothesis, at a DIFFERENT `a` and a
--      different frame), and the epilogue.  Three things are owed:
--
--        * the `blr` transition, which is `steps1` and the only place
--          the fetched instruction is not a `base`;
--        * CODE LOCATION for the callee: `CodeAt (compileC P)
--          (addrOf P i) (emitE ... ++ epilogue)`, which is §3's
--          `codeAtSuffix`/`codeAtR` plus associativity bookkeeping
--          about `emitTbl`.  Mechanical, and the largest single piece;
--        * `Sep` ONE ACTIVATION RECORD HIGHER, which is the resource
--          obligation of the header §4 and is NOT mechanical: it is
--          where a real stack/heap collision would show up, and the
--          bound is a function of the derivation.
--
--      The return is a `blr` on the address `movI` planted, so the
--      "return address is a constant" trick of `ARM.agda` is what makes
--      this a `Steps` composition at all rather than a fixpoint.
--
--  (d) THE WHOLE PROGRAM.  `simulate` at `a = 0` plus the main
--      epilogue, then `runFromSteps` and `Control.runMono`: `runMono`
--      is exactly the lemma that turns "at some fuel" into "at any
--      larger fuel", which is what `ARM.answer`'s fixed 500 needs.
--
--  (e) DECODING.  `ARM.decodeV` is `RealV` as a function, so the last
--      step is `RealV P μ a v → decodeV k P μ a Eq.≡ v` for large
--      enough `k`.  It needs `unAddr (mainLen ...) T 0 (addrOf P i)
--      Eq.≡ i`, i.e. that the block addresses are STRICTLY INCREASING
--      -- true because `blkSize` is `5 + _`, and an ordering induction
--      away.
-- ==================================================================

-- ==================================================================
-- §8  THE TOOLKIT COMPUTES.
--
-- Not a proof of anything, but the point of `Steps` is that it is a
-- transition and not a claim: at the concrete program of `ARM.agda`
-- §11.1 the first two instructions really do compose.
-- ==================================================================

private
  idP : CProg
  idP = compileARM idLin

  -- instruction 0 is fetched, and it is the `movI` that plants the
  -- code address
  _ : instrAt 0 idP Eq.≡ just (base (movI w9 6))
  _ = Eq.refl

  -- the whole program is located at 0 inside itself
  _ : CodeAt idP 0 idP
  _ = codeAtHere idP idP 0 (λ k → Eq.ap (λ z → instrAt z idP) (+zero k))

  -- and it halts at 13, which is off the end
  _ : instrAt 13 idP Eq.≡ nothing
  _ = Eq.refl
