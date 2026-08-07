{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  A RISC-V FRAGMENT, AS AN INSTANCE OF THE ABSTRACT ISA LAYER.

  `ISA.Toy` checked that the generic layer is not vacuous.  This file
  checks that it survives contact with a REAL instruction set: four
  registers, a word-addressed memory, and `ADDI`/`ADD`/`MV`/`LW`/`SW`
  besides `NOP`.  The instantiation is still the three lines `ISA.Toy`
  advertised -- `exec`, `riscvStep`, and the `open import ISA.Program` --
  and everything else here is either the answer to a question the toy did
  not have to face, or a `refl`.

  ------------------------------------------------------------------
  IS A REGISTER FILE A PCM?  YES, AND IT IS THE SAME ONE.
  ------------------------------------------------------------------

  This is the design decision the file turns on, so it is worth stating
  the three candidates and why one of them wins.

    (a) REGISTERS AS A SEPARATE PROMODEL, with `Split` at a register-name
        carrier.  Rejected: it would be `Heap/Base` copied out with `Loc`
        replaced by `Reg`, i.e. the same construction at a finite address
        space.  Nothing about `Ilv` or `_#_` uses infinitude of `Loc`.

    (b) A PRODUCT PROMODEL `Heap × RegFile`, splitting componentwise.
        Rejected, but only as a PRESENTATION: the componentwise product
        of two "finite partial maps" PCMs over address spaces `A` and `B`
        IS the finite-partial-maps PCM over `A ⊎ B`.  Choosing (b) would
        mean building a second `Fibered`, re-deriving `Ilv`/`_#_` for
        pairs, and re-proving `Heap/Graded`, to land on a promodel
        isomorphic to the one already in the repo.

    (c) ONE `heapFib`, WITH THE ADDRESS SPACE PARTITIONED.  Taken.
        Registers `t0..t3` are memory-mapped at locations `0..3`, RAM
        starts at `4`.  `Reg ↪ Loc` realises the iso of (b) on the nose,
        so `ISA.Machine heapFib` -- the whole command / `wp` / frame
        layer -- applies verbatim, with no new promodel and no new
        grading.

  The mathematical claim behind (c) is that OWNING A REGISTER is a
  resource in exactly the sense owning a heap cell is.  A register file
  in which you always own all of `t0..t3` is not a PCM in any useful way
  -- it is one indivisible element.  It becomes a PCM the moment you
  allow PARTIAL register files, "I own `t0` and `t2`", which is precisely
  what a calling convention (caller-saved vs callee-saved) and a register
  allocator (live ranges) reason about.  Partial maps `Reg ⇀ Val` under
  disjoint union is a PCM, and it is `heapFib` restricted to `Loc < 4`.
  `splitT0` below is that statement inside the calculus: the register
  file entails "`t0` holds `v0`" separated from the other three
  registers, by `⌈⌉-E` and nothing else.

  What actually distinguishes registers from RAM is therefore NOT the
  resource algebra but the OPERATIONS: the register address space is
  FINITE and STATICALLY NAMED, so there is no `alloc` for it.  `ISA.Toy`
  had exactly one `Local` instruction, and it was `alloc`, whose locality
  came from being nondeterministic in the address.  RISC-V has no such
  instruction, and `noLocalAddi` below is the consequence, proved.
  Finiteness is also what `ISA/RiscV/RegAlloc` turns into a theorem.

  ------------------------------------------------------------------
  WORDS ARE ℤ/3.  This is a real restriction and it is deliberate.
  ------------------------------------------------------------------

  Reusing `heapFib` fixes `Val` to `Heap/Base`'s three-element type, so a
  word is `ℤ/3` and `addV` is a nine-entry table.  32-bit words are NOT
  modelled: `Loc = ℕ` is unary, so a numeral like `2^31` is not a
  reducible closed term and every `refl` test in this file would become
  inert -- which is the failure mode `Heap/Base`'s header warns about for
  a function-valued heap, in another guise.  The fragment is therefore a
  3-bit-ish machine, and it is closed under its own pointer arithmetic:
  a word `x` addresses RAM word `dataAddr x ∈ {4,5,6}`, so the three
  values index exactly the three RAM cells and `LW`/`SW` can never
  compute an address outside the map.  Nothing in the ISA layer knows
  the size of a word, so widening `Val` is a change to `Heap/Base`, not
  to this file.

  ------------------------------------------------------------------
  THE SEMANTICS IS DETERMINISTIC, AND THAT MAKES THE AXIOMS FREE
  ------------------------------------------------------------------

  `exec : Instr → Heap → Heap` is a function, so `riscvStep i = fn
  (exec i)` and `ISA.Machine.wp-fn` gives `wp (fn f) Q h ≅ Q (f h)` with
  both round trips `refl`.  Consequently the exact-state Hoare axiom

      stepAx i h : ⟪ ⌈ h ⌉ ⟫ riscvStep i ⟪ ⌈ exec i h ⌉ ⟫

  is `⌈⌉-E` (Yoneda) applied to `⌈⌉-pt`, with no case analysis at all,
  and `progAx` lifts it to whole programs by the same two-clause
  recursion `ISA.Program.local-sem` uses.  So for a deterministic machine
  THE HOARE TRIPLE IS THE EVALUATOR: `progTriple` below is `progAx prog
  st₀`, and its stated postcondition `⌈ st₁ ⌉` is accepted because
  `execP prog st₀` reduces to `st₁`.

  Small-footprint axioms (`mvAx`, `addiAx`) are the same term at a
  two-cell heap, and they carry the hypothesis `Diff (regLoc rd)
  (regLoc rs)` -- which is aliasing showing up already at the level of
  one instruction: `mv t0, t0` has a ONE-cell footprint, not two, so the
  two-cell axiom does not apply to it.

  ------------------------------------------------------------------
  WHAT IS NOT LOCAL, AND WHY -- proved, not asserted
  ------------------------------------------------------------------

  `noLocalAddi` shows `Local (riscvStep (ADDI t0 t1 v1))` is refutable.
  The reason is structural and applies to every instruction here except
  `NOP`: split the two-register state into (source) ∗ (destination), and
  the destination register is in the FRAME, but the instruction changes
  it, whereas `ISA.Machine.Local` demands `parts h' sp' false Eq.≡
  parts h sp false` -- the frame slot untouched, on the nose.

  This is not the failure `ISA.Toy`'s `store` had.  `store` failed for
  lack of a SAFETY side condition (it is undefined on the frame-free
  part).  `ADDI` is total; it fails because it writes a STATICALLY NAMED
  location, and a statically named location can always be put in the
  frame.  Allocation escapes only because it is nondeterministic in the
  address: `ilv-fresh` lets it pick a location fresh for the whole,
  hence fresh for both parts.  So:

      on a register machine the unconditional frame rule is available
      for `NOP` and nothing else,

  and a usable frame rule must be conditioned on the footprint being
  disjoint from the frame -- which is the safety side condition
  `ISA.Machine`'s header declines to build in.  That is a statement about
  register machines, not about this fragment.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1, all marked: `regLoc`, `addV`, `dataAddr`, `eqLoc`, `getH`,
  `setH`, `exec` (the machine has to be defined somewhere), `execP`,
  the two directions `sem→exec` / `exec→sem`, `progAx`, and the
  `eqLoc`/`getH`/`setH` lemmas the generic axioms need.  Everything from
  `stepAx` onward is a composite of `⌈⌉-E`, `⌈⌉-pt`, `seq∷`,
  `instrRule`, `emptyRule` and `boolΠ`.
-}
open import Cubical.Foundations.Prelude

module ISA.RiscV.Base where

open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Unit
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Theories.Monoid

open import TheoryGrammar.Instances.Heap.Base
  using ( Loc ; Val ; v0 ; v1 ; v2 ; Cell ; Heap ; single
        ; Diff ; diff-irrefl ; Fresh ; _#_ ; Ilv ; nil ; left ; right
        ; heapFib )

import ISA.Machine
module M = ISA.Machine heapFib

-- ==================================================================
-- THE REGISTER FILE, MEMORY-MAPPED.
--
-- `t0..t3` are RISC-V's caller-saved temporaries -- the registers an
-- allocator actually colours.  `x0` (hardwired zero) is deliberately
-- absent: it is the one register whose write is discarded, which would
-- add a special case to `exec` and buy nothing here.
--
-- The map `regLoc` is the entire content of design choice (c): it
-- realises `Reg ⊎ RAM ≅ Loc` on the nose, so the register file is a
-- sub-PCM of `heapFib` rather than a promodel of its own.
-- ==================================================================

data Reg : Type₀ where
  t0 t1 t2 t3 : Reg

numRegs : ℕ
numRegs = 4

-- PRIMITIVE (phase 1): the memory map.
regLoc : Reg → Loc
regLoc t0 = 0
regLoc t1 = 1
regLoc t2 = 2
regLoc t3 = 3

-- ==================================================================
-- WORDS.  `Val` is `Heap/Base`'s three-element type, so a word is ℤ/3
-- and this is its addition table.  PRIMITIVE (phase 1): the ALU.
-- ==================================================================

addV : Val → Val → Val
addV v0 y  = y
addV v1 v0 = v1
addV v1 v1 = v2
addV v1 v2 = v0
addV v2 v0 = v2
addV v2 v1 = v0
addV v2 v2 = v1

-- PRIMITIVE (phase 1): a word, read as an address.  RAM begins just
-- above the register block, so the three words address the three RAM
-- cells and the machine is closed under its own pointer arithmetic.
dataAddr : Val → Loc
dataAddr v0 = 4
dataAddr v1 = 5
dataAddr v2 = 6

-- ==================================================================
-- READING AND WRITING THE STATE.
--
-- `Loc = ℕ`, so location equality is structural and Bool-valued, and
-- `boolΠ` (never an extended lambda) is what consumes it.
--
-- `getH` of an UNOWNED location is `v0` and `setH` of one is a no-op:
-- the machine does not fault.  Nothing below relies on that -- every
-- Hoare axiom states a precondition naming the cells it touches -- but
-- it is why `exec` is total, and totality is what makes `fn` and hence
-- `wp-fn` applicable.
-- ==================================================================

eqLoc : Loc → Loc → Bool                             -- PRIMITIVE
eqLoc zero    zero    = true
eqLoc zero    (suc _) = false
eqLoc (suc _) zero    = false
eqLoc (suc m) (suc n) = eqLoc m n

getH : Loc → Heap → Val                              -- PRIMITIVE
getH l []            = v0
getH l ((k , y) ∷ h) = M.boolΠ {M = λ _ → Val} y (getH l h) (eqLoc l k)

setH : Loc → Val → Heap → Heap                       -- PRIMITIVE
setH l x []            = []
setH l x ((k , y) ∷ h) =
  M.boolΠ {M = λ _ → Heap} ((k , x) ∷ h) ((k , y) ∷ setH l x h) (eqLoc l k)

-- ==================================================================
-- THE INSTRUCTION SET.
-- ==================================================================

data Instr : Type₀ where
  NOP  : Instr
  ADDI : Reg → Reg → Val → Instr        -- rd ← rs + imm
  ADD  : Reg → Reg → Reg → Instr        -- rd ← rs₁ + rs₂
  MV   : Reg → Reg → Instr              -- rd ← rs
  LW   : Reg → Reg → Instr              -- rd ← M[rs]
  SW   : Reg → Reg → Instr              -- M[rbase] ← rsrc

-- PRIMITIVE (phase 1): the machine.  This -- and `riscvStep` -- is the
-- ONLY thing the generic layer asks a concrete ISA for.
exec : Instr → Heap → Heap
exec NOP             h = h
exec (ADDI rd rs k)  h = setH (regLoc rd) (addV (getH (regLoc rs) h) k) h
exec (ADD rd rs₁ rs₂) h =
  setH (regLoc rd) (addV (getH (regLoc rs₁) h) (getH (regLoc rs₂) h)) h
exec (MV rd rs)      h = setH (regLoc rd) (getH (regLoc rs) h) h
exec (LW rd rs)      h = setH (regLoc rd) (getH (dataAddr (getH (regLoc rs) h)) h) h
exec (SW rb rs)      h = setH (dataAddr (getH (regLoc rb) h)) (getH (regLoc rs) h) h

-- A deterministic instruction is `fn` of its transition function, which
-- is what makes `wp-fn` -- and therefore every axiom below -- available.
riscvStep : Instr → M.Cmd
riscvStep i = M.fn (exec i)

-- ... and here is the entire instantiation.
open import ISA.Program heapFib Instr riscvStep public

-- ==================================================================
-- THE REGISTER FILE IS A PCM: the state SEPARATES, inside the calculus.
--
-- `st₀` splits as (register file) ∗ (RAM), and the register file splits
-- again as (t0) ∗ (t1,t2,t3).  Both are `⌈⌉-E` at an explicit splitting
-- of `heapFib`, and the disjointness component is a nest of `tt` -- i.e.
-- it held on the nose, which is the whole claim.
-- ==================================================================

regs ram : Heap
regs = (0 , v0) ∷ (1 , v1) ∷ (2 , v0) ∷ (3 , v0) ∷ []
ram  = (4 , v1) ∷ (5 , v1) ∷ (6 , v0) ∷ []

st₀ : Heap
st₀ = (0 , v0) ∷ (1 , v1) ∷ (2 , v0) ∷ (3 , v0)
    ∷ (4 , v1) ∷ (5 , v1) ∷ (6 , v0) ∷ []

-- the register block is apart from RAM, on the nose
regsRam : heapFib .Split appop st₀
regsRam =
    regs , ram
  , left (left (left (left (right (right (right nil))))))
  , ( (tt , tt , tt , tt)
    , (tt , tt , tt , tt)
    , (tt , tt , tt , tt)
    , (tt , tt , tt , tt)
    , tt )

splitState : ⌈ st₀ ⌉ ⊢ (⌈ regs ⌉ ∗ ⌈ ram ⌉)
splitState =
  ⌈⌉-E ( regsRam
       , boolΠ {M = λ a → boolΠ {M = λ _ → Gr} ⌈ regs ⌉ ⌈ ram ⌉ a
                            (heapFib .parts appop st₀ regsRam a)}
               (⌈⌉-pt regs) (⌈⌉-pt ram) )

-- ... and a SINGLE REGISTER separates from the rest of the file.  This
-- is the statement that "owning `t0`" is a resource.
regs' : Heap
regs' = (1 , v1) ∷ (2 , v0) ∷ (3 , v0) ∷ []

t0Rest : heapFib .Split appop regs
t0Rest =
    single 0 v0 , regs'
  , left (right (right (right nil)))
  , ((tt , tt , tt , tt) , tt)

splitT0 : ⌈ regs ⌉ ⊢ (⌈ single 0 v0 ⌉ ∗ ⌈ regs' ⌉)
splitT0 =
  ⌈⌉-E ( t0Rest
       , boolΠ {M = λ a → boolΠ {M = λ _ → Gr} ⌈ single 0 v0 ⌉ ⌈ regs' ⌉ a
                            (heapFib .parts appop regs t0Rest a)}
               (⌈⌉-pt (single 0 v0)) (⌈⌉-pt regs') )

-- ==================================================================
-- THE EVALUATOR, AND THE FACT THAT IT IS `sem`.
--
-- `sem` is the free-monoid extension of `riscvStep`, hence a RELATION.
-- For a deterministic machine it is the graph of the fold of `exec`, and
-- the two directions are the two unit/associativity clauses again.
-- ==================================================================

execP : Program → Heap → Heap                        -- PRIMITIVE
execP []      h = h
execP (i ∷ p) h = execP p (exec i h)

-- PRIMITIVE (phase 1): soundness and completeness of the evaluator.
sem→exec : (p : Program) → sem p ⊑ fn (execP p)
sem→exec []      h h'  e              = e
sem→exec (i ∷ p) h h'' (_ , Eq.refl , r) = sem→exec p (exec i h) h'' r

exec→sem : (p : Program) → fn (execP p) ⊑ sem p
exec→sem []      h h'  e = e
exec→sem (i ∷ p) h h'' e = exec i h , Eq.refl , exec→sem p (exec i h) h'' e

-- ==================================================================
-- THE HOARE AXIOMS.  For a deterministic machine the exact-state axiom
-- is `⌈⌉-E` at `⌈⌉-pt` and there is nothing else in it: `wp-fn` turns
-- `wp` at a function into reindexing, and reindexing a representable at
-- its own image is `refl`.
-- ==================================================================

stepAx : (i : Instr) (h : Heap) → ⟪ ⌈ h ⌉ ⟫ riscvStep i ⟪ ⌈ exec i h ⌉ ⟫
stepAx i h = ⌈⌉-E (wp-fn (exec i) ⌈ exec i h ⌉ h .Iso.inv (⌈⌉-pt (exec i h)))

-- `NOP` needs no axiom: `exec NOP` is the identity, so `riscvStep NOP`
-- IS `skip` definitionally and the rule is `skipRule`.
nopAx : (Q : Gr) → ⟪ Q ⟫ riscvStep NOP ⟪ Q ⟫
nopAx = skipRule

-- PRIMITIVE (phase 1): the same two-clause recursion as `local-sem`,
-- lifting the per-instruction axiom to a whole program.
progAx : (p : Program) (h : Heap) → ⟪ ⌈ h ⌉ ⟫ p ⟪ ⌈ execP p h ⌉ ⟫ᵖ
progAx []      h = emptyRule ⌈ h ⌉
progAx (i ∷ p) h = seq∷ i p (instrRule i (stepAx i h)) (progAx p (exec i h))

-- ==================================================================
-- SMALL-FOOTPRINT AXIOMS, generic in the registers.
--
-- These are the axioms a program logic actually quotes: they mention
-- ONLY the cells the instruction touches.  The three `eqLoc` lemmas
-- below are what makes them provable at a VARIABLE register -- at
-- concrete registers `stepAx` already reduces to them.
--
-- Note the hypothesis `Diff (regLoc rd) (regLoc rs)`.  It is aliasing,
-- at the scale of a single instruction: `mv t0, t0` has a one-cell
-- footprint and this two-cell axiom simply does not speak about it.
-- ==================================================================

eqLoc-refl : (l : Loc) → eqLoc l l Eq.≡ true                     -- PRIMITIVE
eqLoc-refl zero    = Eq.refl
eqLoc-refl (suc l) = eqLoc-refl l

eqLoc-Diff : (l k : Loc) → Diff l k → eqLoc l k Eq.≡ false       -- PRIMITIVE
eqLoc-Diff zero    zero    ()
eqLoc-Diff zero    (suc k) d = Eq.refl
eqLoc-Diff (suc l) zero    d = Eq.refl
eqLoc-Diff (suc l) (suc k) d = eqLoc-Diff l k d

-- the ONE place `eqLoc`'s result is destructed: given its value, both
-- `getH` and `setH` reduce.  PRIMITIVE (phase 1).
get-cons : (l k : Loc) (y : Val) (h : Heap) (b : Bool) → eqLoc l k Eq.≡ b
         → getH l ((k , y) ∷ h) Eq.≡ M.boolΠ {M = λ _ → Val} y (getH l h) b
get-cons l k y h b Eq.refl = Eq.refl

set-cons : (l : Loc) (x : Val) (k : Loc) (y : Val) (h : Heap) (b : Bool)
         → eqLoc l k Eq.≡ b
         → setH l x ((k , y) ∷ h)
           Eq.≡ M.boolΠ {M = λ _ → Heap} ((k , x) ∷ h) ((k , y) ∷ setH l x h) b
set-cons l x k y h b Eq.refl = Eq.refl

-- the two-cell footprint of a register-to-register instruction
two : Loc → Val → Loc → Val → Heap
two l x k y = (l , x) ∷ (k , y) ∷ []

get-two-fst : (l k : Loc) (x y : Val) → getH l (two l x k y) Eq.≡ x
get-two-fst l k x y = get-cons l l x ((k , y) ∷ []) true (eqLoc-refl l)

get-two-snd : (l k : Loc) (x y : Val) → Diff k l → getH k (two l x k y) Eq.≡ y
get-two-snd l k x y d =
  get-cons k l x ((k , y) ∷ []) false (eqLoc-Diff k l d)
  Eq.∙ get-cons k k y [] true (eqLoc-refl k)

set-two-fst : (l k : Loc) (x y z : Val) → setH l z (two l x k y) Eq.≡ two l z k y
set-two-fst l k x y z = set-cons l z l x ((k , y) ∷ []) true (eqLoc-refl l)

-- ... and the axioms themselves.  Everything pointful has been pushed
-- into the four lemmas above; these are `⌈⌉-E` at a rewritten state.
private
  coeCmd : (c : M.Cmd) (P : Gr) {h h' : Heap} → h Eq.≡ h'
         → ⟪ P ⟫ c ⟪ ⌈ h ⌉ ⟫ → ⟪ P ⟫ c ⟪ ⌈ h' ⌉ ⟫
  coeCmd c P Eq.refl t = t

  coeArg : (i : Instr) {h h' : Heap} → h Eq.≡ h'
         → ⟪ ⌈ h ⌉ ⟫ riscvStep i ⟪ ⌈ exec i h ⌉ ⟫
         → ⟪ ⌈ h ⌉ ⟫ riscvStep i ⟪ ⌈ exec i h' ⌉ ⟫
  coeArg i Eq.refl t = t

mvAx : (rd rs : Reg) (x y : Val) → Diff (regLoc rs) (regLoc rd)
     → ⟪ ⌈ two (regLoc rd) y (regLoc rs) x ⌉ ⟫ riscvStep (MV rd rs)
       ⟪ ⌈ two (regLoc rd) x (regLoc rs) x ⌉ ⟫
mvAx rd rs x y d =
  coeCmd (riscvStep (MV rd rs)) ⌈ two (regLoc rd) y (regLoc rs) x ⌉
    ( Eq.ap (λ w → setH (regLoc rd) w (two (regLoc rd) y (regLoc rs) x))
            (get-two-snd (regLoc rd) (regLoc rs) y x d)
      Eq.∙ set-two-fst (regLoc rd) (regLoc rs) y x x )
    (stepAx (MV rd rs) (two (regLoc rd) y (regLoc rs) x))

addiAx : (rd rs : Reg) (k x y : Val) → Diff (regLoc rs) (regLoc rd)
       → ⟪ ⌈ two (regLoc rd) y (regLoc rs) x ⌉ ⟫ riscvStep (ADDI rd rs k)
         ⟪ ⌈ two (regLoc rd) (addV x k) (regLoc rs) x ⌉ ⟫
addiAx rd rs k x y d =
  coeCmd (riscvStep (ADDI rd rs k)) ⌈ two (regLoc rd) y (regLoc rs) x ⌉
    ( Eq.ap (λ w → setH (regLoc rd) (addV w k)
                        (two (regLoc rd) y (regLoc rs) x))
            (get-two-snd (regLoc rd) (regLoc rs) y x d)
      Eq.∙ set-two-fst (regLoc rd) (regLoc rs) y x (addV x k) )
    (stepAx (ADDI rd rs k) (two (regLoc rd) y (regLoc rs) x))

-- ==================================================================
-- THE PROGRAM.  Load two words, add them, bump the pointer, store.
--
--     lw   t2, 0(t0)      -- t2 ← M[4]
--     lw   t3, 0(t1)      -- t3 ← M[5]
--     add  t2, t2, t3     -- t2 ← t2 + t3
--     addi t0, t0, 2      -- t0 ← t0 + 2   (now points at M[6])
--     sw   t2, 0(t0)      -- M[6] ← t2
-- ==================================================================

prog : Program
prog = LW t2 t0 ∷ LW t3 t1 ∷ ADD t2 t2 t3 ∷ ADDI t0 t0 v2 ∷ SW t0 t2 ∷ []

st₁ : Heap
st₁ = (0 , v2) ∷ (1 , v1) ∷ (2 , v2) ∷ (3 , v1)
    ∷ (4 , v1) ∷ (5 , v1) ∷ (6 , v2) ∷ []

-- the free-monoid extension computes
_ : sem prog ≡ (riscvStep (LW t2 t0) ⨟ riscvStep (LW t3 t1)
             ⨟ riscvStep (ADD t2 t2 t3) ⨟ riscvStep (ADDI t0 t0 v2)
             ⨟ riscvStep (SW t0 t2) ⨟ skip)
_ = refl

-- THE EVALUATION TEST: a concrete final state, by `refl`.
_ : execP prog st₀ ≡ st₁
_ = refl

-- ... intermediate states, so the trace is visible
_ : execP (LW t2 t0 ∷ LW t3 t1 ∷ []) st₀
  ≡ (0 , v0) ∷ (1 , v1) ∷ (2 , v1) ∷ (3 , v1)
  ∷ (4 , v1) ∷ (5 , v1) ∷ (6 , v0) ∷ []
_ = refl

-- THE TRIPLE, and it is the evaluator: `progAx prog st₀` has stated
-- postcondition `⌈ execP prog st₀ ⌉`, which reduces to `⌈ st₁ ⌉`.
progTriple : ⟪ ⌈ st₀ ⌉ ⟫ prog ⟪ ⌈ st₁ ⌉ ⟫ᵖ
progTriple = progAx prog st₀

-- a small-footprint triple, quoting only the two registers it touches
mvTriple : ⟪ ⌈ two 0 v0 1 v1 ⌉ ⟫ riscvStep (MV t0 t1) ⟪ ⌈ two 0 v1 1 v1 ⌉ ⟫
mvTriple = mvAx t0 t1 v1 v0 tt

-- ==================================================================
-- LOCALITY.  `NOP` has it; `ADDI` provably does not, and the proof is
-- the shape of the argument for every writing instruction.
-- ==================================================================

localNop : M.Local (riscvStep NOP)
localNop = local-skip

-- the counterexample state: `t0 ↦ v0`, `t1 ↦ v0`
cx cxOut : Heap
cx    = (0 , v0) ∷ (1 , v0) ∷ []
cxOut = (0 , v1) ∷ (1 , v0) ∷ []

-- ... split as (SOURCE register `t1`) ∗ (DESTINATION register `t0`), so
-- the destination sits in the FRAME
cxSplit : heapFib .Split appop cx
cxSplit = ((1 , v0) ∷ []) , ((0 , v0) ∷ []) , right (left nil) , ((tt , tt) , tt)

-- no decomposition of the OUTPUT has `t0 ↦ v0` in its frame slot: the
-- four interleavings of a two-cell heap are enumerated and each clashes.
-- PRIMITIVE (phase 1): the one match on `Ilv` in the file.
noFrame : {u' v' : Heap} → Ilv u' v' cxOut → v' Eq.≡ ((0 , v0) ∷ []) → ⊥
noFrame (left  (left  nil)) ()
noFrame (left  (right nil)) ()
noFrame (right (left  nil)) ()
noFrame (right (right nil)) ()

noLocalAddi : M.Local (riscvStep (ADDI t0 t1 v1)) → ⊥
noLocalAddi L = noFrame (r .fst .snd .snd .fst) (r .snd .snd)
  where
  r = L cx cxSplit cxOut Eq.refl
