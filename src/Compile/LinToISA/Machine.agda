{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE TARGET MACHINE: A THREE-INSTRUCTION ISA, AND THE TRADE BETWEEN
  RUNNING A PROGRAM AND FRAMING IT.

  `ISA.Interp` derives the Hoare rules -- sequencing, the empty program,
  consequence, framing -- from an abstract splitting-preserving
  interpretation, and `ISA.Program` supplies the free monoid.  `ISA.Toy`
  instantiates them at `nop`/`alloc`/`store` and stops there.  This file
  instantiates them at the ISA the linear-λ compiler of
  `Compile.LinToISA.Codegen` actually emits, and adds the ONE thing
  neither `ISA.Toy` nor `LinLam/Codegen` has: an EXECUTABLE machine, plus
  the theorem that executing is a run of the relational semantics.

  ------------------------------------------------------------------
  THE INSTRUCTIONS, AND WHY THERE ARE EXACTLY THESE THREE
  ------------------------------------------------------------------

      nopI          skip
      putI l x      append the cell `l ↦ x`      -- DETERMINISTIC
      newI x        append `l ↦ x` at ANY fresh l -- NONDETERMINISTIC

  `putI` and `newI` are the same instruction under two readings of "where
  does the cell go", and the difference between them is the whole content
  of this file:

      DETERMINISM buys EXECUTION.  `Put l x` is `fn (_++h single l x)`,
      so `wp (Put l x) Q` is reindexing (`wp-fn`, the Yoneda lemma), its
      Hoare axiom `putAx` is `⌈⌉-E` at a point, and `execI` can run it.

      NONDETERMINISM buys FRAMING.  `ISA.Toy.localAlloc` proves `Alloc`
      is `Local` precisely because it does not name its location: a
      location fresh for the whole is fresh for both parts of any
      splitting, so the allocation can be pushed into the left slot and
      the frame slot comes back LITERALLY unchanged.

  And the trade is REAL, not an artefact of how the two were written:
  `noPutLocal` below shows `Put` fails `Local` outright.  Split
  `l ↦ y` as `[] ⊎ (l ↦ y)` and run `putI l x` on it; the left part is
  `[]`, so the left slot of any output splitting must be `l ↦ x`, and the
  frame must still be `l ↦ y` -- two cells at one location, which
  `Diff l l = ⊥` refutes.  This is `ISA.Toy`'s remark about `store` in
  its sharpest form, and it is the same failure `LinLam/Codegen`'s
  `noPackPres` exhibits one layer up: naming an address is exactly what
  a frame cannot tolerate.

  So the compiler emits `putI` (and gets exact heaps and `refl`-computing
  tests), while `newI` is kept in the alphabet so that
  `Compile.LinToISA.Codegen.spill` can demonstrate the frame rule on a
  program that really allocates.  `Dets` marks the executable fragment,
  and `exec-sound` is stated only there -- which is honest rather than
  restrictive, since a nondeterministic instruction has no `exec`.

  ------------------------------------------------------------------
  WHAT IS REUSED
  ------------------------------------------------------------------

  Sequencing, the empty program, consequence and framing are NOT proved
  here.  They arrive through

      ISA.Program heapFib LI liStep

  which is one line, and whose entire obligation -- "`sem` is a monoid
  homomorphism" -- was discharged once and for all in `ISA.Program` by a
  two-clause induction.  `ISA.Toy.Alloc`, `ISA.Toy.allocAx` and
  `ISA.Toy.localAlloc` are IMPORTED rather than restated: they are facts
  about `heapFib`, not about `ToyI`, and nothing in them mentions the
  instruction alphabet.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1, all marked: `Put`, `liStep` (a machine has to be defined
  somewhere), `execI`/`exec` and `exec-sound` (the one recursion over a
  program in this file), and the two-line `#-same-loc`.  `putAx`,
  `nopAx`, `noPutLocal` and everything in `Codegen` are composites.
-}
open import Cubical.Foundations.Prelude

module Compile.LinToISA.Machine where

open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.List using (List; []; _∷_; _++_)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Theories.Monoid

-- the TARGET promodel, qualified: `Heap/Base` has its own `boolΠ`, and
-- `ISA.Machine` has another, so exactly one of them may be unqualified
import TheoryGrammar.Instances.Heap.Base as HB
open HB using ( Loc ; Val ; v0 ; v1 ; v2 ; Cell ; Heap ; single ; _++h_
              ; Diff ; Fresh ; _#_ ; IsNil ; Ilv ; nil ; left ; right
              ; ilv-nilL ; ilv-nilR ; heapFib ) public

-- `Alloc`, its Hoare axiom and its LOCALITY, imported.  All three are
-- statements about `heapFib` alone; the instruction alphabet they were
-- first written at is irrelevant, which is the point.
import ISA.Toy as Toy

import ISA.Machine
module M = ISA.Machine heapFib

-- ==================================================================
-- THE INSTRUCTION SET.
-- ==================================================================

data LI : Type₀ where
  nopI : LI
  putI : Loc → Val → LI
  newI : Val → LI

-- PRIMITIVE (phase 1): the deterministic append.  Being an `fn` is the
-- whole of it -- `wp` at a function is the Cartesian lift, so the Hoare
-- axiom below is the Yoneda lemma and `execI` is the function itself.
Put : Loc → Val → M.Cmd
Put l x = M.fn (λ h → h ++h single l x)

-- PRIMITIVE (phase 1): the machine.  This is the ONLY thing the generic
-- layer asks a concrete ISA for.
liStep : LI → M.Cmd
liStep nopI       = M.skip
liStep (putI l x) = Put l x
liStep (newI x)   = Toy.Alloc x

-- ... and here is the entire instantiation: sequencing, the empty
-- program, consequence and the frame rule, all of them, for free.
open import ISA.Program heapFib LI liStep public

-- ==================================================================
-- THE HOARE AXIOMS.  Neither matches a heap.
-- ==================================================================

-- `Put` is deterministic, so its axiom is `wp-fn` (reindexing along the
-- function) transposed by `⌈⌉-E` (Yoneda).  No induction, no heap.
putAx : (l : Loc) (x : Val) (h : Heap)
      → ⟪ ⌈ h ⌉ ⟫ Put l x ⟪ ⌈ h ++h single l x ⌉ ⟫
putAx l x h =
  ⌈⌉-E {a = h} {B = wp (Put l x) ⌈ h ++h single l x ⌉}
       ( wp-fn (λ k → k ++h single l x) ⌈ h ++h single l x ⌉ h .Iso.inv
               (⌈⌉-pt (h ++h single l x)) )

-- `nop` needs no axiom at all: it is `skipRule`.
nopAx : (Q : Gr) → ⟪ Q ⟫ liStep nopI ⟪ Q ⟫
nopAx = skipRule

-- `newI` reuses `ISA.Toy`'s axiom verbatim.
newAx : (x : Val) (u : Heap)
      → ⟪ ⌈ u ⌉ ⟫ liStep (newI x) ⟪ ⊕ᴰ Loc (λ l → ⌈ u ++h single l x ⌉) ⟫
newAx = Toy.allocAx

-- ... and its locality, likewise.
newLocal : (x : Val) → Local (liStep (newI x))
newLocal = Toy.localAlloc

-- ==================================================================
-- THE NEGATIVE HALF: NAMING AN ADDRESS BREAKS THE FRAME RULE.
--
-- Read the counterexample in the proof: the input splits as
-- `[] ⊎ (l ↦ y)`, so `Local` forces the output's left slot to be what
-- `Put l x` produces from `[]` -- namely `l ↦ x` -- while the frame slot
-- must still be `l ↦ y`.  A splitting owns its two slots disjointly, so
-- that is `Diff l l`, and `Diff l l = ⊥`.
--
-- Compare `LinLam/Codegen.noPackPres`, which refutes `SplitPresAt` for
-- the compacting layout by exactly the same collision.  The two are the
-- same theorem at two layers: a frame tolerates an allocator only when
-- the allocator does not choose.
-- ==================================================================

-- PRIMITIVE (phase 1): the one match on `_#_`'s representation.
#-same-loc : (l : Loc) (x y : Val) → single l x # single l y → ⊥
#-same-loc l x y ((d , _) , _) = HB.diff-irrefl l d

noPutLocal : (l : Loc) (x y : Val) → Local (Put l x) → ⊥
noPutLocal l x y loc =
  #-same-loc l x y
    (HB.#-Eq (Eq.sym (r .snd .fst)) (r .snd .snd)
             (r .fst .snd .snd .snd))
  where
  h : Heap
  h = single l y

  spl : heapFib .Split appop h
  spl = [] , single l y , ilv-nilL (single l y) , tt

  r = loc h spl (h ++h single l x) Eq.refl

-- ==================================================================
-- THE EXECUTABLE FRAGMENT.
--
-- `Det` marks the instructions that are functions, `Dets` the programs
-- built from them.  `newI` is deliberately outside: it has no `exec`
-- because it has no chosen location, which is precisely the property
-- `newLocal` turns into the frame rule.
-- ==================================================================

-- PRIMITIVE (phase 1): the machine, as a function.
execI : LI → Heap → Heap
execI nopI       h = h
execI (putI l x) h = h ++h single l x
execI (newI x)   h = h              -- unreachable: `Det (newI x) = ⊥`

-- PRIMITIVE (phase 1): the ONE recursion over a program in this file.
exec : Program → Heap → Heap
exec []      h = h
exec (i ∷ p) h = exec p (execI i h)

Det : LI → Type₀
Det nopI       = Unit
Det (putI _ _) = Unit
Det (newI _)   = ⊥

Dets : Program → Type₀
Dets []      = Unit
Dets (i ∷ p) = Det i × Dets p

-- ==================================================================
-- ... AND THE BRIDGE.  `exec` is a run of `sem`, so a Hoare triple
-- about `sem p` is a statement about the machine that runs `p`.
--
-- This is the only place the two presentations of the ISA -- the
-- relational one the Hoare rules are about, and the functional one that
-- computes -- are identified, and it is three clauses.
-- ==================================================================

-- PRIMITIVE (phase 1)
exec-sound : (p : Program) → Dets p → (h : Heap) → sem p h (exec p h)
exec-sound []              _        h = Eq.refl
exec-sound (nopI ∷ p)      (_ , ds) h = h , Eq.refl , exec-sound p ds h
exec-sound (putI l x ∷ p)  (_ , ds) h =
  h ++h single l x , Eq.refl , exec-sound p ds (h ++h single l x)
exec-sound (newI x ∷ p)    (() , _) h

-- ==================================================================
-- THE OBSERVATION RULE, once, for every program at once.
--
-- A triple `⟪ ⌈ h ⌉ ⟫ p ⟪ ⌈ k ⌉ ⟫ᵖ` between representables says exactly
-- that running `p` from `h` lands on `k`.  `observe` is the only exit
-- from the calculus in this development, and everything downstream uses
-- it in a `refl` line.
-- ==================================================================

observe : (p : Program) → Dets p → (h k : Heap)
        → ⟪ ⌈ h ⌉ ⟫ p ⟪ ⌈ k ⌉ ⟫ᵖ → exec p h Eq.≡ k
observe p d h k t = t h (⌈⌉-pt h) (exec p h) (exec-sound p d h)
