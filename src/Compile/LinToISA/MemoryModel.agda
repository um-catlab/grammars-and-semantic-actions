{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE MEMORY MODEL AT THE CONCRETE MACHINE -- AND WHY IT DOES NOT FIT
  YET.

  `ISA.Memory` builds the relaxed theory of assembly (interleaving
  splittings, `Disj` side condition) and proves the semantics is still
  a `Pass` into commands, under ONE hypothesis:

      Commutes : i ⌣ j → (step i ⨟ step j) ⊑ (step j ⨟ step i)

  This file tries to discharge it for `Compile.LinToISA.Machine`, whose
  instructions are `nopI`/`putI`/`newI`, with the obvious footprint
  relation -- two stores commute when their addresses differ.

  IT IS FALSE, and the reason is worth more than the attempt.

  ------------------------------------------------------------------
  THE OBSTRUCTION
  ------------------------------------------------------------------

  `Heap` is `List Cell`, and `Put l x` is `fn (_++h single l x)` -- it
  APPENDS.  So from the empty heap,

      Put l x ⨟ Put k y   produces   (l,x) ∷ (k,y) ∷ []
      Put k y ⨟ Put l x   produces   (k,y) ∷ (l,x) ∷ []

  and those are different lists whenever `l` and `k` differ.  `⊑` is
  containment of relations on the nose, so the commutation fails even
  though the two heaps have the same cells at the same addresses.

  `noCommutes` below proves it.

  ------------------------------------------------------------------
  WHAT IT MEANS, WHICH IS NOT "THE MEMORY MODEL WAS A BAD IDEA"
  ------------------------------------------------------------------

  Notice this is the SAME complaint as `NoTextPres`, one layer down.
  There, program text was a free monoid and could not be the target of
  a compiler whose source splittings commute.  Here, the STATE is a
  free monoid and cannot be the target of a semantics whose
  instructions commute.

      NoTextPres    the TEXT is ordered, the heap is not
      noCommutes    the HEAP CARRIER is ordered, the addresses are not

  `heapFib` already papers over this at the SPLITTING level -- its
  `Split appop` is `Ilv` with `_#_`, exactly the shape `ISA.Memory`
  gives text -- but `Put`'s semantics is a function into lists, and a
  function into lists sees the order.

  So the memory model is not obtainable by relaxing the syntax alone.
  Both sides have to be relaxed, and the fix is on the carrier:

      Heap = List Cell        ordered, and `Put` cannot commute
      Heap = Loc → Maybe Val  unordered, and `Put` commutes on the nose

  With a functional heap, `Put l x ⨟ Put k y` and `Put k y ⨟ Put l x`
  are the SAME function when `Diff l k`, `Commutes` is a one-line
  extensionality argument, and `ISA.Memory.memPass` instantiates.

  That change is not local: `layout`, `layPres`, `runU`, and every
  `refl` test in `Compile.Showcase` are stated at the list heap.  It is
  recorded here rather than attempted, because the measurement is the
  useful part and the migration is a separate piece of work.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1: a refutation.
-}
open import Cubical.Foundations.Prelude

module Compile.LinToISA.MemoryModel where

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

import TheoryGrammar.Instances.Heap.Base as HB
open import Compile.LinToISA.Machine

-- ==================================================================
-- §1  THE FOOTPRINT RELATION.
--
-- `nopI` touches nothing and commutes with everything.  Two stores
-- commute when their addresses differ.  `newI` has NO fixed address
-- -- which is exactly why `Machine.newLocal` holds and `noPutLocal`
-- fails -- so it is given no commutations beyond `nopI`; two
-- allocations append in the order they run and do not commute either.
-- ==================================================================

_⌣_ : LI → LI → Type₀
nopI     ⌣ j        = Unit
putI l x ⌣ nopI     = Unit
putI l x ⌣ putI k y = Diff l k
putI l x ⌣ newI y   = ⊥
newI x   ⌣ nopI     = Unit
newI x   ⌣ putI k y = ⊥
newI x   ⌣ newI y   = ⊥

-- ==================================================================
-- §2  IT IS SYMMETRIC.  (The half that DOES hold, so the failure below
-- cannot be blamed on a badly chosen relation.)
-- ==================================================================

-- `Heap.Base` has `diff-irrefl` but not this; four clauses.
diff-sym : (l k : Loc) → Diff l k → Diff k l
diff-sym zero    zero    d = d
diff-sym zero    (suc k) d = tt
diff-sym (suc l) zero    d = tt
diff-sym (suc l) (suc k) d = diff-sym l k d

⌣-sym : (i j : LI) → i ⌣ j → j ⌣ i
⌣-sym nopI       nopI       c = tt
⌣-sym nopI       (putI _ _) c = tt
⌣-sym nopI       (newI _)   c = tt
⌣-sym (putI _ _) nopI       c = tt
⌣-sym (putI _ _) (putI _ _) c = diff-sym _ _ c
⌣-sym (putI _ _) (newI _)   ()
⌣-sym (newI _)   nopI       c = tt
⌣-sym (newI _)   (putI _ _) ()
⌣-sym (newI _)   (newI _)   ()

-- ==================================================================
-- §3  THE REFUTATION.
--
-- Run both orders from the EMPTY heap.  The left-to-right order lands
-- on `(l,x) ∷ (k,y) ∷ []`; for the other order to land there too, the
-- two cells would have to be the same cell, so `l` is `k`.
-- ==================================================================

-- the address of the FIRST cell -- all that is needed to tell the two
-- heaps apart, and it avoids an `Eq.refl` match that would want K
headLoc : Heap → Loc
headLoc []            = zero
headLoc ((l , _) ∷ _) = l

noCommutes : (l k : Loc) → Diff l k
           → ((Put l v1 ⨟ Put k v1) ⊑ (Put k v1 ⨟ Put l v1)) → ⊥
noCommutes l k d cm
  with cm [] (single l v1 ++h single k v1) (single l v1 , Eq.refl , Eq.refl)
... | (_ , Eq.refl , e) =
  HB.diff-irrefl l (Eq.transport (λ z → Diff l z) (Eq.ap headLoc e) d)

-- ==================================================================
-- §4  ... AND THEREFORE THE HYPOTHESIS OF `ISA.Memory` IS NOT
-- AVAILABLE AT THIS MACHINE.
--
-- `liStep (putI l x)` is `Put l x` definitionally, so a `Commutes` for
-- `_⌣_` would supply exactly the arrow §3 refutes.
-- ==================================================================

noLICommutes : ((i j : LI) → i ⌣ j → (liStep i ⨟ liStep j) ⊑ (liStep j ⨟ liStep i))
             → (l k : Loc) → Diff l k → ⊥
noLICommutes cm l k d = noCommutes l k d (cm (putI l v1) (putI k v1) d)
