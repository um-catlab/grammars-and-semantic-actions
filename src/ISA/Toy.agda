{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  A TOY ISA, TO CHECK THAT THE GENERIC LAYER IS NOT VACUOUS.

  Everything mathematical happened in `ISA.Machine`, `ISA.Interp` and
  `ISA.Program`.  This file exists to instantiate them and see that the
  derived rules actually apply:

      resources     := `heapFib`            (the partial commutative
                                             monoid of heaps)
      instructions  := `nop`, `alloc x`, `store l x`
      program text  := `List ToyI`, i.e. `Strings` at that alphabet.

  The whole instantiation is three lines (`toyStep`, and the
  `open import ISA.Program`).  Nothing about sequencing is proved here.

  ------------------------------------------------------------------
  THE INSTRUCTIONS, AND WHICH OF THEM ARE LOCAL
  ------------------------------------------------------------------

  `nop` is `skip`.

  `alloc x` is NONDETERMINISTIC ALLOCATION: pick any location fresh for
  the current heap and append a cell holding `x`.  It is `Local` --
  `localAlloc` -- and the proof is the interesting one: given a splitting
  `Ilv u v h`, a location fresh for `h` is fresh for both parts
  (`ilv-fresh`), so the allocation can be pushed entirely into the left
  part (`ilv-snoc`, `#-snoc`) leaving the frame `v` literally unchanged.
  That last clause -- `parts h' sp' false Eq.≡ parts h sp false` -- is
  what `Local` demands and what makes the frame rule apply.

  `store l x` is the SMALL-FOOTPRINT store: defined on the singleton heap
  `l ↦ y` and nowhere else.  It has a perfectly good Hoare axiom
  (`storeAx`) and it is deliberately NOT claimed to be `Local`, because
  it is not:

      take h = l ↦ y split as u = [] and v = (l ↦ y).  `store l x` runs
      on h, but there is no u' with `store l x [] u'`, so no splitting of
      the output can have `c u u'` in its left slot.

  This is not a defect of the generic layer; it is `Heap.Hoare`'s `Local`
  (which this generalises verbatim) having no SAFETY side condition.  The
  standard repair is to demand the frame property only where the command
  is safe on the left part, i.e. to replace `wp` by the total-correctness
  `Safe c & wp c Q`; that repair breaks `local-⨟` unless safety of a
  composite is defined as "safe now, and safe after every step", so it is
  a real design decision rather than a one-line fix, and it is left
  alone here.  Locality of a PROGRAM is still compositional
  (`local-⨟` / `local-skip` / `ISA.Program.local-sem`), which is what
  `localProg` below uses.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1, all marked: `Alloc`, `Store`, `toyStep` (the per-instruction
  semantics -- a machine has to be defined somewhere), the three heap
  lemmas `ilv-fresh`, `ilv-snoc`, `#-snoc`, the two axioms `allocAx` /
  `storeAx`, and `localAlloc`.  Everything from `t₁` onward is a
  composite of `seq∷`, `instrRule`, `consequence`, `⊕ᴰ-I`, `⊕ᴰ-E` and
  `frameRule`.
-}
open import Cubical.Foundations.Prelude

module ISA.Toy where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit
open import Cubical.Data.List using (List; []; _∷_; _++_)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Theories.Monoid

open import TheoryGrammar.Instances.Heap.Base
  using ( Loc ; Val ; v0 ; v1 ; v2 ; Cell ; Heap ; single
        ; Diff ; Fresh ; _#_ ; Ilv ; nil ; left ; right
        ; ilv-nilR ; _++h_ ; heapFib )

import ISA.Machine
module M = ISA.Machine heapFib

-- ==================================================================
-- THE INSTRUCTION SET.
-- ==================================================================

data ToyI : Type₀ where
  nop   : ToyI
  alloc : Val → ToyI
  store : Loc → Val → ToyI

-- PRIMITIVE (phase 1): allocation.  Nondeterministic in the location,
-- which is exactly what makes it frame-preserving.
Alloc : Val → M.Cmd
Alloc x h h' = Σ[ l ∈ Loc ] (Fresh l h × (h' Eq.≡ h ++h single l x))

-- PRIMITIVE (phase 1): the small-footprint store.
Store : Loc → Val → M.Cmd
Store l x h h' = Σ[ y ∈ Val ] ((h Eq.≡ single l y) × (h' Eq.≡ single l x))

-- PRIMITIVE (phase 1): the machine.  This is the ONLY thing the generic
-- layer asks a concrete ISA for.
toyStep : ToyI → M.Cmd
toyStep nop         = M.skip
toyStep (alloc x)   = Alloc x
toyStep (store l x) = Store l x

-- ... and here is the entire instantiation.
open import ISA.Program heapFib ToyI toyStep public

-- ==================================================================
-- THREE HEAP LEMMAS -- PRIMITIVES (phase 1), the interface to `Ilv`,
-- `Fresh` and `_#_`.  They are what `localAlloc` needs and all it needs.
-- ==================================================================

-- a location fresh for the whole is fresh for both parts
ilv-fresh : {u v h : Heap} → Ilv u v h → (l : Loc)
          → Fresh l h → Fresh l u × Fresh l v
ilv-fresh nil                l fr       = tt , tt
ilv-fresh (left  {c = k , y} p) l (d , fr) =
  (d , ilv-fresh p l fr .fst) , ilv-fresh p l fr .snd
ilv-fresh (right {c = k , y} p) l (d , fr) =
  ilv-fresh p l fr .fst , (d , ilv-fresh p l fr .snd)

-- appending a cell on the RIGHT of the whole appends it to the LEFT part
ilv-snoc : {u v h : Heap} → Ilv u v h → (c : Cell)
         → Ilv (u ++h (c ∷ [])) v (h ++h (c ∷ []))
ilv-snoc nil        c = ilv-nilR (c ∷ [])
ilv-snoc (left  p)  c = left  (ilv-snoc p c)
ilv-snoc (right p)  c = right (ilv-snoc p c)

-- ... and disjointness survives, given the new cell is fresh for the frame
#-snoc : (u v : Heap) (l : Loc) (x : Val)
       → u # v → Fresh l v → (u ++h single l x) # v
#-snoc []            v l x d        fr = fr , tt
#-snoc ((k , y) ∷ u) v l x (fk , d) fr = fk , #-snoc u v l x d fr

-- ==================================================================
-- THE HOARE AXIOMS OF THE INSTRUCTIONS.  Both are `⌈⌉-E` -- the Yoneda
-- lemma -- applied to a single point, so neither matches on a heap.
-- ==================================================================

-- PRIMITIVE (phase 1)
allocAx : (x : Val) (u : Heap)
        → ⟪ ⌈ u ⌉ ⟫ Alloc x ⟪ ⊕ᴰ Loc (λ l → ⌈ u ++h single l x ⌉) ⟫
allocAx x u = ⌈⌉-E pt
  where
  pt : wp (Alloc x) (⊕ᴰ Loc (λ l → ⌈ u ++h single l x ⌉)) u
  pt _ (l , fr , Eq.refl) = l , Eq.refl

-- PRIMITIVE (phase 1)
storeAx : (l : Loc) (x y : Val) → ⟪ ⌈ single l y ⌉ ⟫ Store l x ⟪ ⌈ single l x ⌉ ⟫
storeAx l x y = ⌈⌉-E pt
  where
  pt : wp (Store l x) ⌈ single l x ⌉ (single l y)
  pt _ (y' , e , Eq.refl) = Eq.refl

-- `nop` needs no axiom at all: it is `skipRule`.
nopAx : (Q : Gr) → ⟪ Q ⟫ toyStep nop ⟪ Q ⟫
nopAx = skipRule

-- ==================================================================
-- LOCALITY OF ALLOCATION.  PRIMITIVE (phase 1): the one place a heap
-- splitting is destructured.
--
-- Read the answer: the output splitting is `(u ++h [l ↦ x] , v)` --
-- the frame slot is the SAME `v`, which is the third component's
-- `Eq.refl`, and that is the whole frame property.
-- ==================================================================

localAlloc : (x : Val) → M.Local (Alloc x)
localAlloc x h (u , v , il , d) _ (l , fr , Eq.refl) =
    ( u ++h single l x , v
    , ilv-snoc il (l , x)
    , #-snoc u v l x d (ilv-fresh il l fr .snd) )
  , (l , ilv-fresh il l fr .fst , Eq.refl)
  , Eq.refl

localNop : M.Local (toyStep nop)
localNop = local-skip

-- ==================================================================
-- THE SEQUENCING TEST.
--
--     prog = alloc v0 ; alloc v1
--
-- The triple below is built with `seq∷` and NOTHING else that knows
-- about sequencing -- `seq∷` is `ISA.Interp.seq` at the canonical
-- splitting, and `ISA.Interp.seq` is `wp-⊑ ∘g seqCmd`.
-- ==================================================================

prog : Program
prog = alloc v0 ∷ alloc v1 ∷ []

-- the free-monoid extension computes
_ : sem prog ≡ (Alloc v0 ⨟ Alloc v1 ⨟ skip)
_ = refl

Mid : Gr
Mid = ⊕ᴰ Loc (λ l → ⌈ single l v0 ⌉)

Post : Gr
Post = ⊕ᴰ Loc (λ l → ⊕ᴰ Loc (λ l' → ⌈ single l v0 ++h single l' v1 ⌉))

t₁ : ⟪ ⌈ [] ⌉ ⟫ alloc v0 ∷ [] ⟪ Mid ⟫ᵖ
t₁ = instrRule (alloc v0) (allocAx v0 [])

t₂ : ⟪ Mid ⟫ alloc v1 ∷ [] ⟪ Post ⟫ᵖ
t₂ = ⊕ᴰ-E λ l →
       instrRule (alloc v1)
         (consequence (Alloc v1) idg
            (⊕ᴰ-I Loc {A = λ k → ⊕ᴰ Loc (λ l' → ⌈ single k v0 ++h single l' v1 ⌉)} l)
            (allocAx v1 (single l v0)))

-- THE RULE, USED.
progTriple : ⟪ ⌈ [] ⌉ ⟫ prog ⟪ Post ⟫ᵖ
progTriple = seq∷ (alloc v0) (alloc v1 ∷ []) t₁ t₂

-- ==================================================================
-- ... AND THE FRAME RULE ON TOP OF IT.  Locality of the program is
-- assembled from locality of its instructions by `local-⨟`, which is
-- the same monoid structure again.
-- ==================================================================

localProg : M.Local (sem prog)
localProg =
  local-⨟ (Alloc v0) (Alloc v1 ⨟ skip) (localAlloc v0)
    (local-⨟ (Alloc v1) skip (localAlloc v1) local-skip)

framed : (R : Gr) → ⟪ ⌈ [] ⌉ ∗ R ⟫ prog ⟪ Post ∗ R ⟫ᵖ
framed R = frameRule R prog localProg progTriple

-- ==================================================================
-- A MIXED PROGRAM, to show the two instruction kinds compose.  `store`
-- is not local, so this one gets no frame rule -- which is exactly the
-- honest situation.
-- ==================================================================

prog2 : Program
prog2 = nop ∷ store 0 v1 ∷ store 0 v2 ∷ []

-- A THREE-INSTRUCTION PROGRAM, sequenced twice.  Every step is
-- `seq∷` + `instrRule` + an axiom; there is no reasoning about
-- concatenation anywhere, because `seq∷` already IS the homomorphism.
prog2Triple : ⟪ ⌈ single 0 v0 ⌉ ⟫ prog2 ⟪ ⌈ single 0 v2 ⌉ ⟫ᵖ
prog2Triple =
  seq∷ nop (store 0 v1 ∷ store 0 v2 ∷ [])
    (instrRule nop (nopAx ⌈ single 0 v0 ⌉))
    (seq∷ (store 0 v1) (store 0 v2 ∷ [])
       (instrRule (store 0 v1) (storeAx 0 v1 v0))
       (instrRule (store 0 v2) (storeAx 0 v2 v1)))

-- `alloc` after `store` needs no new rule either -- only a new axiom
-- instance, since the postcondition of `store` is a representable.
prog3 : Program
prog3 = store 0 v1 ∷ alloc v2 ∷ []

prog3Triple : ⟪ ⌈ single 0 v0 ⌉ ⟫ prog3
              ⟪ ⊕ᴰ Loc (λ l → ⌈ single 0 v1 ++h single l v2 ⌉) ⟫ᵖ
prog3Triple =
  seq∷ (store 0 v1) (alloc v2 ∷ [])
    (instrRule (store 0 v1) (storeAx 0 v1 v0))
    (instrRule (alloc v2) (allocAx v2 (single 0 v1)))
