{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE LINEAR λ-CALCULUS, ON AArch64.

  ------------------------------------------------------------------
  WHAT THIS FILE CLOSES
  ------------------------------------------------------------------

  The chain was

      Tm []  --Convert-->  IR + Table  --???-->  CProg  --run-->  answer

  and every link but the middle one existed.  This file is the middle
  link: a CODE GENERATOR from `ClosureConv.IR` to `ArithToARM.Control`'s
  counter machine, and -- §11 -- `refl` tests that a closed linear λ-term
  compiled all the way down RUNS on that machine and produces the value
  `IR.runP` says it should.

  ------------------------------------------------------------------
  THE ONE DESIGN CONSTRAINT THAT SHAPED EVERYTHING
  ------------------------------------------------------------------

  `Control.agda` keeps the link register in the CONFIGURATION rather
  than in `Reg`, and `stepI n (blr r) l s = rg s r , suc n , s`
  OVERWRITES it.  There is no instruction that reads `lr` into a
  register or memory.  So `bl`/`ret` support call depth ONE and no
  more, and a λ-calculus needs unbounded depth.

  The repair costs nothing and uses no new instruction:

      A RETURN ADDRESS IS A CONSTANT, so PUSH IT YOURSELF.

  At a call site the address to come back to is a literal (`movI`), and
  the callee returns with `blr` on an address it loaded from its own
  frame.  `lr` is never read, `bl` and `ret` are never emitted, and the
  five registers of `Reg` are untouched -- no new constructor, so
  `StateFib.regCases`' 25-clause table and `AArch64Emit`'s two printers
  are not disturbed.

  ------------------------------------------------------------------
  THE FIVE REGISTERS, ALL OF THEM SPOKEN FOR
  ------------------------------------------------------------------

      w0    HP   heap pointer, a bump allocator; monotone, never restored
      x19   FP   frame pointer: the current activation record
      x20   SP   operand stack pointer, grows UP (as in `AArch64Codegen`)
      w9         scratch, and THE RETURN VALUE
      w10        scratch

  There is no sixth register, and that is why the environment pointer
  and the argument live in MEMORY (in the activation record) rather than
  in registers: they must survive a nested call, and a caller-saved
  register cannot.

  ACTIVATION RECORD, at `FP`, built by the CALLER:

      [FP +  0]   return address        (a literal, see above)
      [FP +  8]   the caller's FP
      [FP + 16]   the environment       -- the callee closure's address
      [FP + 24]   the argument
      [FP + 32]   the callee's operand stack starts here

  CLOSURE RECORD, at `a`, built by `iclos`:

      [a +  0]        the block's CODE ADDRESS
      [a + 8·(j+1)]   captured value `j`, in `capVals` order

  A `Val` is a heap address throughout; there is no other kind of value,
  which is `IR.agda` §4 ("a value is a closure and nothing else") read
  as a representation decision.

  ------------------------------------------------------------------
  THE INVARIANT THAT MAKES THE ADDRESSES STATIC
  ------------------------------------------------------------------

  EVERY expression's code pushes EXACTLY ONE SLOT onto the operand
  stack and restores everything else.  That is `AArch64Codegen.Post`'s
  `pSP` again, and it is what lets the epilogue find the block's result
  at the fixed offset `[FP + 32]` without a `with` or an arithmetic
  lemma.  All three `IR` constructors respect it: `ivar` and `iclos`
  push once; `iapp` pushes twice, pops twice, and pushes once.

  A FRAME POSITION IS STATIC TOO.  `Ev` reads `σ (slotOf 0 u s)`, and
  `slotOf` walks the usage list, so position `0` is the argument and
  position `suc q` is shape position `q`.  `packIx` turns the latter
  into the closure record's PACKED index, and it is exactly `spread`
  read backwards -- compare the two definitions in §2.

  ------------------------------------------------------------------
  CODE LAYOUT, AND WHY MEASURING WITH A DUMMY MAP IS SOUND
  ------------------------------------------------------------------

      [0 .. mainLen)   the main expression, a pop, and a `bra` off the end
      [mainLen .. )    the blocks, in table order

  A block's address is needed INSIDE the code (as `movI`'s immediate in
  `iclos`, and as the return address in `iapp`), and the code's length
  is needed to compute that address.  The knot is cut by the
  observation that an ADDRESS IS ALWAYS AN IMMEDIATE: no choice of
  address changes any instruction COUNT.  §4's `sizeE` therefore takes
  NEITHER the address map NOR the enclosing shape, and §6 proves it is
  the length of what §5 emits -- so the layout is well founded and the
  two cannot drift apart.

  That separation is also what keeps the `refl` tests of §11 cheap.
  Agda's `let` is substitution, so an emitter that measured itself
  (`length (emitE ...)`) would recompute each subterm's code once per
  occurrence -- exponential in the nesting of `iapp`, and observably so:
  the three-call `applyK` did not finish.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1: this is a compiler, in the style of `AArch64Codegen` §4.
  `loadSlot`, `emitCap`, `callSeq`, `epilogue` are PRIMITIVE and marked.
-}
open import Cubical.Foundations.Prelude

module Compile.ClosureConv.ARM where

open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.List using (List; []; _∷_; _++_; length)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import Compile.ArithToARM.AArch64 hiding (Prog)
open import Compile.ArithToARM.Control
open import Compile.ClosureConv.Convert

-- ==================================================================
-- §1  ADDRESSES.
--
-- `off8` is `AArch64Codegen`'s, repeated rather than imported so this
-- path does not drag in `Exp`.  Eight on the LEFT so that `8 + X`
-- reduces to `suc⁸ X`: the development's standing rule, and the reason
-- it owns no arithmetic lemma.
-- ==================================================================

off8 : ℕ → Word
off8 zero    = 0
off8 (suc l) = 8 + off8 l

-- the four fields of an activation record, and where the callee's own
-- stack begins.  Literals, so every `ldrO`/`strO` offset computes.
fRET fSAV fENV fARG fTOP : Word
fRET = 0
fSAV = 8
fENV = 16
fARG = 24
fTOP = 32

-- ==================================================================
-- §2  FROM A FRAME POSITION TO A CLOSURE FIELD.
--
-- `packIx` is `IR.spread` read backwards, clause for clause:
--
--     spread (true  ∷ sh) (v ∷ vs) zero    = v          -- index 0
--     spread (true  ∷ sh) (v ∷ vs) (suc p) = spread sh vs p
--     spread (false ∷ sh) vs       (suc p) = spread sh vs p
--
-- so shape position `q` sits at packed index "number of live positions
-- of `sh` strictly below `q`".
-- ==================================================================

packIx : Usage → ℕ → ℕ
packIx []           q       = 0
packIx (_ ∷ sh)     zero    = 0
packIx (true  ∷ sh) (suc q) = suc (packIx sh q)
packIx (false ∷ sh) (suc q) = packIx sh q

-- how many values a closure over this shape carries -- i.e. the length
-- of `capVals` at `idCap sh`
liveCount : Usage → ℕ
liveCount []          = 0
liveCount (true  ∷ u) = suc (liveCount u)
liveCount (false ∷ u) = liveCount u

-- THE CAPTURE, AS A LIST OF FRAME POSITIONS.  Clause for clause the
-- same recursion as `IR.capVals`, with `σ` removed: that is the sense
-- in which the emitted code computes `capVals`.
capPos : ∀ {sh u} → Cap sh u → List ℕ
capPos (cnil _)                   = []
capPos (cdead c)                  = capPos c
capPos (clive {u₁ = u₁} sp so c)  = slotOf 0 u₁ so ∷ capPos c

-- ==================================================================
-- §3  THE MACROS.  PRIMITIVE (phase 1): each is a short list of real
-- AArch64, and the comment beside it is its specification.
-- ==================================================================

-- PRIMITIVE: frame position `p` into w9.  Position 0 is the argument,
-- which is a field of the activation record; anything above it is a
-- field of the environment, hence a load THROUGH the environment
-- pointer -- two loads, and that asymmetry is the whole of closure
-- conversion at the machine level.
loadSlot : Usage → ℕ → CProg
loadSlot sh zero    = base (ldrO w9 x19 fARG) ∷ []
loadSlot sh (suc q) = base (ldrO w9 x19 fENV)
                    ∷ base (ldrO w9 w9 (off8 (suc (packIx sh q))))
                    ∷ []

-- PRIMITIVE: write the capture's values into the record being built at
-- HP, starting at field `j`.
emitCap : Usage → ℕ → List ℕ → CProg
emitCap sh j []       = []
emitCap sh j (p ∷ ps) =
  loadSlot sh p ++ (base (strO w9 w0 (off8 j)) ∷ emitCap sh (suc j) ps)

-- PRIMITIVE: THE CALL SEQUENCE.  On entry the operand stack holds the
-- closure (below) and the argument (above); `r` is the address to come
-- back to.  Twelve instructions, and the last one is at offset 11 --
-- which is why `emitE`'s `iapp` clause says `11 + pk`.
--
--   0  pop the argument                       SP -= 8
--   1  pop the closure                        SP -= 8
--   2  [SP+16] := the closure  (the callee's environment)
--   3  [SP+24] := the argument
--   4  the return address, as a LITERAL       -- see the header
--   5  [SP+ 0] := it
--   6  [SP+ 8] := the caller's FP
--   7  w9 := the block's code address, off the closure record
--   8  FP := SP                               the record is now a frame
--   9  SP := 32 + SP                          the callee's stack
--  10  jump.  `lr` is clobbered and never read.
--  11  the callee returns here, result in w9; push it.
callSeq : ℕ → CProg
callSeq r = base (ldrPre w10 x20 8)
          ∷ base (ldrPre w9  x20 8)
          ∷ base (strO w9  x20 fENV)
          ∷ base (strO w10 x20 fARG)
          ∷ base (movI w10 r)
          ∷ base (strO w10 x20 fRET)
          ∷ base (strO x19 x20 fSAV)
          ∷ base (ldrO w9 w9 0)
          ∷ base (movR x19 x20)
          ∷ base (addI x20 x20 fTOP)
          ∷ blr w9
          ∷ base (strPost w9 x20 8)
          ∷ []

-- PRIMITIVE: THE EPILOGUE.  The body pushed its answer at the block's
-- entry stack pointer, which is `FP + 32` -- the one-slot invariant of
-- the header, spent.  Read the answer and the return address BEFORE
-- either pointer moves.
epilogue : CProg
epilogue = base (ldrO w9  x19 fTOP)
         ∷ base (ldrO w10 x19 fRET)
         ∷ base (movR x20 x19)
         ∷ base (ldrO x19 x19 fSAV)
         ∷ blr w10
         ∷ []

-- ==================================================================
-- §4  MEASURING, BEFORE EMITTING.
--
-- A block's address is needed inside the code, and the code's length is
-- needed to compute the address; §5 cuts that knot by computing the
-- SIZE first, structurally.  The three clauses are written in exactly
-- the shape `length` produces on the emitted list -- `f + (a + 12)` and
-- not `12 + (f + a)` -- so that §6's agreement theorem is four `Eq.ap`s
-- and this development still owns no arithmetic lemma.
--
-- Note what is NOT here: `sizeE` does not take the shape `sh` and does
-- not take the address map.  Neither can change an instruction COUNT,
-- and saying so in the TYPE is what makes the layout well-founded.
-- ==================================================================

sizeLoad : ℕ → ℕ
sizeLoad zero    = 1
sizeLoad (suc _) = 2

sizeCap : List ℕ → ℕ
sizeCap []       = 0
sizeCap (p ∷ ps) = sizeLoad p + suc (sizeCap ps)

sizeE : ∀ {u} → IR u → ℕ
sizeE (ivar {u} s)  = suc (sizeLoad (slotOf 0 u s))
sizeE (iclos i cap) = 2 + (sizeCap (capPos cap) + 2)
sizeE (iapp _ f a)  = sizeE f + (sizeE a + 12)

-- ==================================================================
-- §5  THE CODE GENERATOR.
--
-- `am` is the address map (block index ↦ code address), `sh` the
-- enclosing block's environment shape, `pc` the address this code will
-- be placed at.  `pc` is consulted ONLY to build the return address in
-- `iapp`; nothing else in the emitted code is position-dependent.
-- ==================================================================

emitE : (am : ℕ → ℕ) (sh : Usage) (pc : ℕ) {u : Usage} → IR u → CProg

-- a frame read, then the one push
emitE am sh pc (ivar {u} s) =
  loadSlot sh (slotOf 0 u s) ++ (base (strPost w9 x20 8) ∷ [])

-- ALLOCATION.  Code address into field 0, the captured values into
-- fields 1.., push the record's address, bump HP.  `capPos` is
-- `capVals` with the frame erased, so the record the machine builds is
-- the list `capVals` computes -- positionally, entry by entry.
emitE am sh pc (iclos i cap) =
    base (movI w9 (am i))
  ∷ base (strO w9 w0 0)
  ∷ ( emitCap sh 1 (capPos cap)
      ++ ( base (strPost w0 x20 8)
         ∷ base (addI w0 w0 (off8 (suc (length (capPos cap)))))
         ∷ [] ) )

-- A CALL.  The callee, then the argument, then `callSeq` -- and the
-- return address is computed from the two SIZES, which is the only
-- place `pc` is used.  §6 is what stops `sizeE` and `emitE` drifting
-- apart.
emitE am sh pc (iapp _ f a) =
    emitE am sh pc f
  ++ ( emitE am sh (sizeE f + pc) a
       ++ callSeq (11 + (sizeE a + (sizeE f + pc))) )

-- ==================================================================
-- §6  ... AND THE SIZE IS THE LENGTH.
--
-- The one thing §4 could get wrong, proved away.  `sizeE` mentions
-- neither `am` nor `pc`, so this also says -- in the only form the
-- layout needs -- that no address choice moves any instruction.
-- ==================================================================

length-++ : (p q : CProg) → length (p ++ q) Eq.≡ length p + length q
length-++ []      q = Eq.refl
length-++ (i ∷ p) q = Eq.ap suc (length-++ p q)

loadLen : (sh : Usage) (p : ℕ) → length (loadSlot sh p) Eq.≡ sizeLoad p
loadLen sh zero    = Eq.refl
loadLen sh (suc q) = Eq.refl

capLen : (sh : Usage) (j : ℕ) (ps : List ℕ)
       → length (emitCap sh j ps) Eq.≡ sizeCap ps
capLen sh j []       = Eq.refl
capLen sh j (p ∷ ps) =
  length-++ (loadSlot sh p) (base (strO w9 w0 (off8 j)) ∷ emitCap sh (suc j) ps)
  Eq.∙ ( Eq.ap (λ z → z + suc (length (emitCap sh (suc j) ps))) (loadLen sh p)
         Eq.∙ Eq.ap (λ z → sizeLoad p + suc z) (capLen sh (suc j) ps) )

sizeIsLength : (am : ℕ → ℕ) (sh : Usage) (pc : ℕ) {u : Usage} (e : IR u)
             → length (emitE am sh pc e) Eq.≡ sizeE e
sizeIsLength am sh pc (ivar {u} s) = go (slotOf 0 u s)
  where
  go : (p : ℕ)
     → length (loadSlot sh p ++ (base (strPost w9 x20 8) ∷ [])) Eq.≡ suc (sizeLoad p)
  go zero    = Eq.refl
  go (suc q) = Eq.refl
sizeIsLength am sh pc (iclos i cap) =
  Eq.ap (λ z → 2 + z)
    ( length-++ (emitCap sh 1 (capPos cap))
                ( base (strPost w0 x20 8)
                ∷ base (addI w0 w0 (off8 (suc (length (capPos cap))))) ∷ [] )
      Eq.∙ Eq.ap (λ z → z + 2) (capLen sh 1 (capPos cap)) )
sizeIsLength am sh pc (iapp _ f a) =
  length-++ (emitE am sh pc f)
            ( emitE am sh (sizeE f + pc) a
              ++ callSeq (11 + (sizeE a + (sizeE f + pc))) )
  Eq.∙ ( Eq.ap (λ z → z + length ( emitE am sh (sizeE f + pc) a
                                   ++ callSeq (11 + (sizeE a + (sizeE f + pc)))))
               (sizeIsLength am sh pc f)
         Eq.∙ Eq.ap (λ z → sizeE f + z)
               ( length-++ (emitE am sh (sizeE f + pc) a)
                           (callSeq (11 + (sizeE a + (sizeE f + pc))))
                 Eq.∙ Eq.ap (λ z → z + 12) (sizeIsLength am sh (sizeE f + pc) a) ) )

-- ==================================================================
-- §7  THE LAYOUT.
-- ==================================================================

blkSize : Blk → ℕ
blkSize (sh , b) = 5 + sizeE b

tblSize : Table → ℕ
tblSize []      = 0
tblSize (B ∷ T) = blkSize B + tblSize T

-- THE ADDRESS MAP.  `blkAddr b T i` is where block `i` lands when the
-- table starts at `b`.  Out-of-range indices get `b`; the table is
-- well-formed at every program this development compiles, and a
-- malformed one would jump to block 0 rather than into nowhere.
blkAddr : ℕ → Table → ℕ → ℕ
blkAddr b []      i       = b
blkAddr b (B ∷ T) zero    = b
blkAddr b (B ∷ T) (suc i) = blkAddr (blkSize B + b) T i

emitBlk : (ℕ → ℕ) → ℕ → Blk → CProg
emitBlk am pc (sh , b) = emitE am sh pc b ++ epilogue

emitTbl : (ℕ → ℕ) → ℕ → Table → CProg
emitTbl am pc []      = []
emitTbl am pc (B ∷ T) = emitBlk am pc B ++ emitTbl am (blkSize B + pc) T

-- ==================================================================
-- §8  THE WHOLE PROGRAM.
--
-- `Prog` here is `IR.Prog` -- a table and a closed expression;
-- `AArch64`'s `Prog` is hidden at the import, and the ARM side is
-- `Control.CProg` throughout.  (The naming hazard is real: `LinToC`
-- has a third `CProg`.)
--
-- Main is the expression, a pop into w9, and a `bra` PAST THE END --
-- which is `Control`'s halt, so `run` answers `just`.
-- ==================================================================

mainLen : IR [] → ℕ
mainLen e = 2 + sizeE e

addrOf : Prog → ℕ → ℕ
addrOf P = blkAddr (mainLen (P .snd)) (P .fst)

progLen : Prog → ℕ
progLen P = mainLen (P .snd) + tblSize (P .fst)

compileC : Prog → CProg
compileC P =
  ( emitE (addrOf P) [] 0 (P .snd)
    ++ ( base (ldrPre w9 x20 8) ∷ bra (progLen P) ∷ [] ) )
  ++ emitTbl (addrOf P) (mainLen (P .snd)) (P .fst)

-- the whole pipeline, from a closed linear λ-term
compileARM : Tm [] → CProg
compileARM t = compileC (compileP t)

-- ==================================================================
-- §9  THE INITIAL MACHINE.
--
-- Two disjoint regions, both growing UP, and the numbers are small so
-- that `eqℕ` -- which is unary -- does not dominate the `refl` tests.
-- Nothing else is initialised: the memory is all zeros, and `x19` is
-- zero because a closed main reads no frame slot (`IR []` has no
-- `Solo`, and every `Cap sh []` is `cdead`/`cnil`).
-- ==================================================================

stackBase heapBase : Word
stackBase = 64
heapBase  = 512

initSt : St
initSt = setR w0 heapBase (setR x19 0 (setR x20 stackBase (λ _ → 0)))
       , (λ _ → 0)

initC : Conf
initC = 0 , 0 , initSt

runARM : ℕ → Prog → Maybe Conf
runARM f P = run f (compileC P) initC

-- ==================================================================
-- §10  READING THE ANSWER BACK.
--
-- The machine's answer is a heap ADDRESS in w9, and an address is not a
-- `Val`.  `decodeV` walks the record: field 0 is a code address, which
-- `unAddr` turns back into a block index, and the block's shape says
-- how many captured fields to follow.
--
-- This is `Correct.agda`'s `RelV` as a FUNCTION, at the one program the
-- answer means anything in -- which is exactly that file's lesson ("a
-- `Val` is only meaningful relative to a table") applied to a machine
-- word.  It is bounded by a depth so that it is total.
-- ==================================================================

unAddr : ℕ → Table → ℕ → Word → ℕ
unAddr b []      i a = i
unAddr b (B ∷ T) i a = ifB (eqℕ a b) i (unAddr (blkSize B + b) T (suc i) a)

arityM : Maybe Blk → ℕ
arityM nothing         = 0
arityM (just (sh , _)) = liveCount sh

decodeV  : ℕ → Prog → Mem → Word → Val
decodeCs : ℕ → Prog → Mem → Word → ℕ → ℕ → List Val

decodeV zero    P μ a = junk
decodeV (suc k) P μ a =
  clos (unAddr (mainLen (P .snd)) (P .fst) 0 (μ a))
       (decodeCs k P μ a 1
          (arityM (blkAt (P .fst) (unAddr (mainLen (P .snd)) (P .fst) 0 (μ a)))))

decodeCs k P μ a j zero    = []
decodeCs k P μ a j (suc n) =
  decodeV k P μ (μ (a + off8 j)) ∷ decodeCs k P μ a (suc j) n

answerM : ℕ → Prog → Maybe Conf → Maybe Val
answerM k P nothing            = nothing
answerM k P (just (_ , _ , s)) = just (decodeV k P (mm s) (rg s w9))

-- THE OBSERVATION.  `answer fuel depth P` runs the compiled program and
-- decodes what it halted holding.  Compare `IR.runP`, which is the same
-- observation of the same program one level up.
answer : ℕ → ℕ → Prog → Maybe Val
answer f k P = answerM k P (runARM f P)

answerT : ℕ → ℕ → Tm [] → Maybe Val
answerT f k t = answer f k (compileP t)

-- ==================================================================
-- §11  IT RUNS.
--
-- Everything below is `Eq.refl` or `refl`, so a closed linear λ-term
-- really is compiled to real AArch64 control flow and really is
-- executed by `Control.run`.
-- ==================================================================

-- ------------------------------------------------------------------
-- 11.1  `λx. x`.  The whole program, printed, because it is small
-- enough to read and because the reader should see that there is no
-- `bl` and no `ret` in it.
-- ------------------------------------------------------------------

_ : compileARM idLin
  Eq.≡ ( base (movI w9 6)          -- the closure record: code address
       ∷ base (strO w9 w0 0)
       ∷ base (strPost w0 x20 8)   -- push it
       ∷ base (addI w0 w0 8)       -- bump HP
       ∷ base (ldrPre w9 x20 8)    -- main: pop the answer into w9
       ∷ bra 13                    -- ... and halt
       ∷ base (ldrO w9 x19 24)     -- block 0: the argument
       ∷ base (strPost w9 x20 8)
       ∷ base (ldrO w9  x19 32)    -- the epilogue
       ∷ base (ldrO w10 x19 0)
       ∷ base (movR x20 x19)
       ∷ base (ldrO x19 x19 8)
       ∷ blr w10
       ∷ [] )
_ = Eq.refl

idRun : Maybe Conf
idRun = runARM 500 (compileP idLin)

-- it HALTED, one past the end of the program
_ : pcOf idRun ≡ 13
_ = refl

-- the answer is the heap record allocated at the heap base ...
_ : regOf idRun w9 ≡ 512
_ = refl

-- ... whose code field is block 0's address ...
_ : memOf idRun 512 ≡ 6
_ = refl

-- ... and HP was bumped by exactly one field
_ : regOf idRun w0 ≡ 520
_ = refl

-- ... and the stack pointer came back to where it started
_ : regOf idRun x20 ≡ 64
_ = refl

-- THE STATEMENT THAT MATTERS: decoded, the machine's answer is the
-- value `IR.runP` computes for the same program.
_ : answerT 500 8 idLin Eq.≡ just (clos 0 [])
_ = Eq.refl

_ : answerT 500 8 idLin Eq.≡ runP 20 (compileP idLin)
_ = Eq.refl

-- ------------------------------------------------------------------
-- 11.2  `(λx.x) (λx.x)` -- ONE CALL.  The identity closure is applied
-- to the identity closure and returns its argument, so the answer is
-- the SECOND record, naming block 1.  This is `Correct.agda` §2.1's
-- witness, run on the machine.
-- ------------------------------------------------------------------

selfRun : Maybe Conf
selfRun = runARM 500 (compileP selfApp)

_ : pcOf selfRun ≡ 36
_ = refl

_ : regOf selfRun w9 ≡ 520          -- the second record
_ = refl

_ : memOf selfRun 520 ≡ 29          -- ... naming block 1
_ = refl

-- the stack pointer is back at its base: the call returned cleanly
_ : regOf selfRun x20 ≡ 64
_ = refl

_ : answerT 500 8 selfApp Eq.≡ just (clos 1 [])
_ = Eq.refl

_ : answerT 500 8 selfApp Eq.≡ runP 20 (compileP selfApp)
_ = Eq.refl

-- ------------------------------------------------------------------
-- 11.3  `(λf. λx. f x) (λy. y)` -- THE CAPSTONE TERM.  The answer is a
-- closure WITH AN ENVIRONMENT, so the machine had to allocate a
-- two-field record and fill its second field from the activation
-- record's argument slot.  `Correct.agda`'s `capstone` is the
-- hand-built realisation of exactly this value; here it is the
-- machine's.
-- ------------------------------------------------------------------

bigRun : Maybe Conf
bigRun = runARM 500 (compileP bigT)

_ : pcOf bigRun ≡ 62
_ = refl

-- three records were allocated: block 0's, block 2's, and the one
-- block 0's body built for the inner λ
_ : regOf bigRun w0 ≡ 544
_ = refl

_ : regOf bigRun w9 ≡ 528          -- the answer's record
_ = refl

_ : memOf bigRun 528 ≡ 33          -- ... names block 1 ...
_ = refl

_ : memOf bigRun 536 ≡ 520         -- ... and its one captured field ...
_ = refl

_ : memOf bigRun 520 ≡ 55          -- ... is the record naming block 2
_ = refl

_ : regOf bigRun x20 ≡ 64
_ = refl

-- decoded: the machine's answer IS `clos 1 (clos 2 [] ∷ [])`
_ : answerT 500 8 bigT Eq.≡ just (clos 1 (clos 2 [] ∷ []))
_ = Eq.refl

_ : answerT 500 8 bigT Eq.≡ runP 20 (compileP bigT)
_ = Eq.refl

-- ------------------------------------------------------------------
-- 11.4  `(λf. f (λz.z)) (λx.x)` -- `Normalise.agda`'s separating term,
-- whose contraction CREATES a redex, and hence the first test with two
-- nested calls live at once.  That is the case `bl`/`ret` could not
-- have run: the inner call would have destroyed the outer's return
-- address.
-- ------------------------------------------------------------------

_ : pcOf (runARM 200 (compileP applyK)) ≡ 59
_ = refl

_ : answerT 200 8 applyK Eq.≡ just (clos 1 [])
_ = Eq.refl

_ : answerT 200 8 applyK Eq.≡ runP 40 (compileP applyK)
_ = Eq.refl

-- ------------------------------------------------------------------
-- 11.5  FUEL BEHAVES.  Starved, the machine answers `nothing` -- so
-- the `just`s above really are TERMINATIONS and not a decoding of a
-- half-run state.  That distinction is `Control.agda` §4's, inherited
-- intact: `just` can only be produced by the counter leaving the
-- program.
-- ------------------------------------------------------------------

_ : runARM 5 (compileP bigT) ≡ nothing
_ = refl

_ : answerT 5 8 bigT Eq.≡ nothing
_ = Eq.refl

-- ... and surplus fuel changes nothing.  Stated against the ANSWER and
-- not against the other run: `Eq.≡` between two `run`s at different
-- fuels makes the conversion checker walk two fuel recursions in
-- lockstep, and that costs minutes where this costs nothing.
-- `Control.runMono` is the theorem this line samples.
_ : answerT 4000 8 bigT Eq.≡ just (clos 1 (clos 2 [] ∷ []))
_ = Eq.refl

-- ------------------------------------------------------------------
-- 11.6  NO `bl`, NO `ret`, ANYWHERE -- the header's claim, as a
-- computation.  `NoLR` is `Unit`/`⊥`-valued, so the proof is `tt`.
--
-- And the emitted code is NOT branch-free, which is the honest
-- statement of what `Control.execAgrees` can and cannot do here: it
-- transfers `AArch64Codegen.correct` to a whole branch-free program at
-- counter 0, and no program this compiler emits is one.  The
-- generalisation that does apply -- a LOCATED branch-free stretch
-- inside a program that branches -- is `ARMCorrect.runBase`.
-- ------------------------------------------------------------------

NoLR : CProg → Type₀
NoLR []           = Unit
NoLR (bl _  ∷ _)  = ⊥
NoLR (ret   ∷ _)  = ⊥
NoLR (_     ∷ p)  = NoLR p

_ : NoLR (compileARM bigT)
_ = tt

_ : NoLR (compileARM applyK)
_ = tt

_ : BranchFree (compileARM idLin) ≡ ⊥
_ = refl
