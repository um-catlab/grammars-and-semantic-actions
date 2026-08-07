{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  A SMALL MODEL OF C -- AND THE FACT THAT C DOES NOT ENFORCE ANYTHING.

  This is the C sibling of `Compile.LinToISA.Machine`, built to exactly
  the same specification so that the two backends can be compared:

      SOURCE      `TheoryGrammar.Instances.LinLam.Syntax`'s `TmG`,
                  at a `Usage`
      OBSERVABLE  `Heap` from `TheoryGrammar.Instances.Heap.Base`
      THE SPEC    evaluating the compiled output from the empty heap
                  yields `LinLam.Codegen.layout u`

  Nothing about the observable is C-specific.  That is deliberate: an
  assembly backend, a C backend and a Rust backend that all land on the
  SAME `Heap` can be compared, and their agreement is a composition of
  three equations rather than three separate stories.

  ------------------------------------------------------------------
  THE FRAGMENT, AND WHAT IS DELIBERATELY MISSING
  ------------------------------------------------------------------

      cskip        `;`
      cdecl  l x   `val_t x<l> = <x>;`          -- declare a fresh object
      cstore l x   `*(mem + <l>) = <x>;`        -- store through a pointer
      cmalloc  x   `val_t *p = malloc(...); *p = <x>;`

  DELIBERATELY LEFT OUT, and why:

    * NO `if`, NO `while`, NO `goto`.  Program text in this framework is
      the FREE MONOID on statements (`ISA.Program` at `CStmt`), and a
      free monoid has concatenation and nothing else.  Control flow needs
      a different program-text promodel -- one whose `Split appop` is not
      merely "write `p` as `p₁ ++ p₂`".  A sibling agent is looking at
      that; it is not attempted here, and no statement below pretends to
      branch.

    * NO expressions, NO arithmetic, NO function calls.  The observable
      is a heap of `Val`s, and `Val` is three-valued so that every test
      is `refl`.  An expression language would buy nothing the spec can
      see.

    * NO `free`.  The layout is about OWNERSHIP, not lifetime; the
      observable heap has no notion of a dead cell.

  What is present is exactly enough to hit the spec, plus `cstore` and
  `cmalloc`, which exist to make the negative half of the argument.

  ------------------------------------------------------------------
  THE INTERESTING PART: C HAS NO OWNERSHIP
  ------------------------------------------------------------------

  The Rust backend is sound in part because Rust's affine ownership
  MATCHES the source's linearity: the target's type system refuses the
  programs the compiler must not emit.  C refuses nothing.  Two pointers
  may name one object; an allocation may leak; a declaration and a store
  through an alias are the same write.

  That last one is a THEOREM here, not a slogan:

      noOwnership : cStep (cdecl l x)  ≡  cStep (cstore l x)

  -- `refl`.  The two statements have literally the same denotation, so
  no property of a C program's meaning can distinguish "I own this
  object" from "I wrote through someone else's pointer".  Consequently:

      alias-freedom of the emitted code cannot be a property of C.
      It has to be a property of the COMPILER.

  And it is.  `Compile.LinToC.Codegen.emittedNoAlias` proves that every
  program this compiler emits declares pairwise-distinct objects, and the
  theorem that does the work is `LinLam.Codegen.layPres`: a context
  splitting `Use⊎ u₁ u₂ u` becomes a DISJOINT heap splitting, because
  `Use⊎` has no `(true,true)` constructor.  The emitted regions are
  disjoint by construction, four modules upstream, and the C target
  simply cannot state that fact about itself.  `aliasC` below is the
  counterweight: a perfectly well-formed program of this fragment whose
  memory is NOT alias-free, hence (by `noSourceForAlias`) the compilation
  of no source term whatsoever.

  In Rust the same disjointness would be a property of the TARGET's type
  system -- two `let` bindings are two distinct places, and the borrow
  checker rejects the aliasing program before it runs.  Here it is a
  property of the map.  That contrast is why both backends are worth
  building.

  ------------------------------------------------------------------
  DETERMINISM VERSUS FRAMING -- the same trade as `LinToISA`
  ------------------------------------------------------------------

  `cdecl`/`cstore` are DETERMINISTIC (`fn (_++h single l x)`), so `wp` at
  them is reindexing, their Hoare axiom is `⌈⌉-E` at a point, and `evalC`
  can run them.  `cmalloc` is NONDETERMINISTIC -- it does not name its
  address -- and that is exactly why it is `Local` and the frame rule
  applies to it.  `noWriteLocal` below shows the trade is real: a
  statement that NAMES an address fails `Local` outright.  This is
  `ISA.Toy`'s remark about `store` and `LinLam/Codegen`'s `noPackPres`,
  one more time: naming an address is what a frame cannot tolerate.

  ------------------------------------------------------------------
  WHAT IS REUSED
  ------------------------------------------------------------------

  Sequencing, the empty program, consequence and framing are NOT proved
  here.  They arrive through

      ISA.Program heapFib CStmt cStep

  -- one line -- whose whole obligation ("`sem` is a monoid
  homomorphism") was discharged once in `ISA.Program`.  `ISA.Toy.Alloc`,
  `allocAx` and `localAlloc` are IMPORTED for `cmalloc`: they are facts
  about `heapFib`, not about an instruction alphabet.

      Hoare sequencing proved in this file:   0
      Hoare framing proved in this file:      0
      inductions over a program in this file: 1   (`evalC-sound`)

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1, all marked: `Write`, `cStep`, `evalS`/`evalC`/`evalC-sound`,
  `WF`/`coeWF`, and the two-line `#-same-loc`.  `writeAx`, `skipAx`,
  `noWriteLocal`, `observe` and everything in `Codegen` are composites.
-}
open import Cubical.Foundations.Prelude

module Compile.LinToC.Machine where

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
              ; Diff ; diff-irrefl ; Fresh ; _#_ ; IsNil
              ; Ilv ; nil ; left ; right
              ; ilv-nilL ; ilv-nilR ; heapFib ) public

-- `Alloc`, its Hoare axiom and its LOCALITY, imported.  All three are
-- statements about `heapFib` alone.
import ISA.Toy as Toy

import ISA.Machine
module M = ISA.Machine heapFib

-- ==================================================================
-- THE STATEMENTS OF THE FRAGMENT.
-- ==================================================================

data CStmt : Type₀ where
  cskip   : CStmt                 -- `;`
  cdecl   : Loc → Val → CStmt     -- `val_t x<l> = <v>;`
  cstore  : Loc → Val → CStmt     -- `*(mem + <l>) = <v>;`
  cmalloc : Val → CStmt           -- `val_t *p = malloc(...); *p = <v>;`

-- PRIMITIVE (phase 1): the deterministic write.  Being an `fn` is the
-- whole of it -- `wp` at a function is the Cartesian lift, so the Hoare
-- axiom below is the Yoneda lemma and `evalS` is the function itself.
Write : Loc → Val → M.Cmd
Write l x = M.fn (λ h → h ++h single l x)

-- PRIMITIVE (phase 1): the machine.  This is the ONLY thing the generic
-- layer asks a concrete target for.
--
-- READ THE MIDDLE TWO CLAUSES.  A declaration and a store through an
-- alias are the SAME command.  That is C's memory model, faithfully:
-- there is no ownership to be had.
cStep : CStmt → M.Cmd
cStep cskip       = M.skip
cStep (cdecl l x) = Write l x
cStep (cstore l x) = Write l x
cStep (cmalloc x) = Toy.Alloc x

-- ... and here is the entire instantiation: sequencing, the empty
-- program, consequence and the frame rule, all of them, for free.
open import ISA.Program heapFib CStmt cStep public

CProg : Type₀
CProg = Program

-- ==================================================================
-- C HAS NO OWNERSHIP, AS A THEOREM.
--
-- The declaration of a fresh object and a store through a pointer that
-- happens to name that object are indistinguishable in the target.  So
-- no invariant of the emitted C's MEANING can express "these two writes
-- own different memory"; that has to come from the compiler.
-- ==================================================================

noOwnership : (l : Loc) (x : Val) → cStep (cdecl l x) ≡ cStep (cstore l x)
noOwnership l x = refl

-- ==================================================================
-- THE HOARE AXIOMS.  Neither of the first two matches a heap.
-- ==================================================================

-- `Write` is deterministic, so its axiom is `wp-fn` (reindexing along
-- the function) transposed by `⌈⌉-E` (Yoneda).  No induction, no heap.
writeAx : (l : Loc) (x : Val) (h : Heap)
        → ⟪ ⌈ h ⌉ ⟫ Write l x ⟪ ⌈ h ++h single l x ⌉ ⟫
writeAx l x h =
  ⌈⌉-E {a = h} {B = wp (Write l x) ⌈ h ++h single l x ⌉}
       ( wp-fn (λ k → k ++h single l x) ⌈ h ++h single l x ⌉ h .Iso.inv
               (⌈⌉-pt (h ++h single l x)) )

declAx : (l : Loc) (x : Val) (h : Heap)
       → ⟪ ⌈ h ⌉ ⟫ cStep (cdecl l x) ⟪ ⌈ h ++h single l x ⌉ ⟫
declAx = writeAx

storeAx : (l : Loc) (x : Val) (h : Heap)
        → ⟪ ⌈ h ⌉ ⟫ cStep (cstore l x) ⟪ ⌈ h ++h single l x ⌉ ⟫
storeAx = writeAx

-- `cskip` needs no axiom at all: it is `skipRule`.
skipAx : (Q : Gr) → ⟪ Q ⟫ cStep cskip ⟪ Q ⟫
skipAx = skipRule

-- `cmalloc` reuses `ISA.Toy`'s axiom verbatim.
mallocAx : (x : Val) (u : Heap)
         → ⟪ ⌈ u ⌉ ⟫ cStep (cmalloc x) ⟪ ⊕ᴰ Loc (λ l → ⌈ u ++h single l x ⌉) ⟫
mallocAx = Toy.allocAx

-- ... and its locality, likewise.
mallocLocal : (x : Val) → Local (cStep (cmalloc x))
mallocLocal = Toy.localAlloc

-- ==================================================================
-- THE NEGATIVE HALF: NAMING AN ADDRESS BREAKS THE FRAME RULE.
--
-- The input splits as `[] ⊎ (l ↦ y)`, so `Local` forces the output's
-- left slot to be what `Write l x` produces from `[]` -- namely
-- `l ↦ x` -- while the frame slot must still be `l ↦ y`.  A splitting
-- owns its two slots disjointly, so that is `Diff l l`, and
-- `Diff l l = ⊥`.
--
-- This is `Compile.LinToISA.Machine.noPutLocal`, and one layer up it is
-- `LinLam/Codegen.noPackPres`.  A frame tolerates an allocator only when
-- the allocator does not choose.
-- ==================================================================

-- PRIMITIVE (phase 1): the one match on `_#_`'s representation.
#-same-loc : (l : Loc) (x y : Val) → single l x # single l y → ⊥
#-same-loc l x y ((d , _) , _) = diff-irrefl l d

noWriteLocal : (l : Loc) (x y : Val) → Local (Write l x) → ⊥
noWriteLocal l x y loc =
  #-same-loc l x y
    (HB.#-Eq (Eq.sym (r .snd .fst)) (r .snd .snd)
             (r .fst .snd .snd .snd))
  where
  h : Heap
  h = single l y

  spl : heapFib .Split appop h
  spl = [] , single l y , ilv-nilL (single l y) , tt

  r = loc h spl (h ++h single l x) Eq.refl

-- ... so in particular a DECLARATION is not local either, which is the
-- statement that C's `val_t x0 = V1;` names its object.
noDeclLocal : (l : Loc) (x y : Val) → Local (cStep (cdecl l x)) → ⊥
noDeclLocal = noWriteLocal

-- ==================================================================
-- THE EXECUTABLE FRAGMENT.
--
-- `Det` marks the statements that are functions, `Dets` the programs
-- built from them.  `cmalloc` is deliberately outside: it has no `evalS`
-- because it has no chosen address, which is precisely the property
-- `mallocLocal` turns into the frame rule.
-- ==================================================================

-- PRIMITIVE (phase 1): the machine, as a function.
evalS : CStmt → Heap → Heap
evalS cskip       h = h
evalS (cdecl l x) h = h ++h single l x
evalS (cstore l x) h = h ++h single l x
evalS (cmalloc x) h = h           -- unreachable: `Det (cmalloc x) = ⊥`

-- PRIMITIVE (phase 1): the ONE recursion over a program in this file.
evalC : CProg → Heap → Heap
evalC []      h = h
evalC (s ∷ p) h = evalC p (evalS s h)

Det : CStmt → Type₀
Det cskip        = Unit
Det (cdecl _ _)  = Unit
Det (cstore _ _) = Unit
Det (cmalloc _)  = ⊥

Dets : CProg → Type₀
Dets []      = Unit
Dets (s ∷ p) = Det s × Dets p

-- ==================================================================
-- ... AND THE BRIDGE.  `evalC` is a run of `sem`, so a Hoare triple
-- about `sem p` is a statement about the machine that runs `p`.
-- ==================================================================

-- PRIMITIVE (phase 1)
evalC-sound : (p : CProg) → Dets p → (h : Heap) → sem p h (evalC p h)
evalC-sound []                _        h = Eq.refl
evalC-sound (cskip ∷ p)       (_ , ds) h = h , Eq.refl , evalC-sound p ds h
evalC-sound (cdecl l x ∷ p)   (_ , ds) h =
  h ++h single l x , Eq.refl , evalC-sound p ds (h ++h single l x)
evalC-sound (cstore l x ∷ p)  (_ , ds) h =
  h ++h single l x , Eq.refl , evalC-sound p ds (h ++h single l x)
evalC-sound (cmalloc x ∷ p)   (() , _) h

-- ==================================================================
-- THE OBSERVATION RULE, once, for every program at once.
--
-- A triple `⟪ ⌈ h ⌉ ⟫ p ⟪ ⌈ k ⌉ ⟫ᵖ` between representables says exactly
-- that running `p` from `h` lands on `k`.  This is the only exit from
-- the calculus in this backend, and everything downstream uses it in a
-- `refl` line.
-- ==================================================================

observe : (p : CProg) → Dets p → (h k : Heap)
        → ⟪ ⌈ h ⌉ ⟫ p ⟪ ⌈ k ⌉ ⟫ᵖ → evalC p h Eq.≡ k
observe p d h k t = t h (⌈⌉-pt h) (evalC p h) (evalC-sound p d h)

-- ==================================================================
-- NO-ALIASING, AS A PREDICATE ON THE TARGET'S MEMORY.
--
-- `WF h` says every location in `h` is named once.  Because `evalC p []`
-- records each write in order, `WF (objects p)` is literally "the
-- program `p` never writes twice to the same object" -- the C-level
-- reading of `_#_`.
--
-- PRIMITIVE (phase 1): recursion on the heap.
-- ==================================================================

WF : Heap → Type₀
WF []            = Unit
WF ((l , _) ∷ h) = Fresh l h × WF h

-- PRIMITIVE (phase 1): `Eq`, so nothing downstream gets a stuck `transp`
coeWF : {a b : Heap} → a Eq.≡ b → WF b → WF a
coeWF Eq.refl w = w

-- the objects a straight-line program brings into being, in order
objects : CProg → Heap
objects p = evalC p []

-- "the emitted C does not alias"
NoAlias : CProg → Type₀
NoAlias p = WF (objects p)

-- ==================================================================
-- ... AND THE COUNTERWEIGHT.  `aliasC` is a program OF THIS FRAGMENT --
-- nothing forbids it, it compiles, it runs -- whose memory is not
-- alias-free.  It is the C the compiler must not emit, and the target
-- gives no reason at all why it should not.
--
-- Compare Rust, where the analogous program is rejected by the borrow
-- checker: there the property is the TARGET's, here it is the MAP's.
-- ==================================================================

aliasC : CProg
aliasC = cdecl 0 v1 ∷ cstore 0 v1 ∷ []

_ : evalC aliasC [] ≡ (0 , v1) ∷ (0 , v1) ∷ []
_ = refl

aliasNotWF : NoAlias aliasC → ⊥
aliasNotWF ((d , _) , _) = diff-irrefl 0 d

-- and the same program written with TWO declarations rather than a
-- declaration and a store is indistinguishable from it -- `noOwnership`
-- at a point.  C offers no way to prefer one over the other.
aliasC' : CProg
aliasC' = cdecl 0 v1 ∷ cdecl 0 v1 ∷ []

_ : evalC aliasC' [] ≡ evalC aliasC []
_ = refl
