{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  REGISTER ALLOCATION IS COMPACTION, AND COMPACTION IS NOT
  SPLIT-PRESERVING.

  `LinLam/Codegen` proves two things about laying variables out in
  memory.  Positively, `layPres`: the layout "variable `i` lives at
  address `i`" preserves splittings, so a linear context split becomes a
  DISJOINT heap split and no-aliasing is the pass's type rather than a
  theorem about it.  Negatively, `noPackPres`: the COMPACTING layout --
  drop the dead slots, address the live ones consecutively from 0 -- does
  NOT, because at a two-variable application both premises compact to
  location 0 and `_#_` is uninhabited.  The criterion it extracts is

      a linear source language buys no-aliasing for free precisely when
      the ALLOCATOR IS INJECTIVE ON VARIABLES, uniformly in the context.

  `ISA/RiscV/Base` memory-maps the register file into `heapFib`, so a
  register allocator is literally a map `Usage → Heap` landing in the
  register block.  The prediction is then immediate and this file tests
  it.  THE PREDICTION HOLDS, and it holds for TWO INDEPENDENT REASONS,
  which is worth separating because only one of them is about register
  pressure.

  ------------------------------------------------------------------
  WHAT AN ALLOCATOR IS HERE
  ------------------------------------------------------------------

  `ralloc ρ` below is the pointwise allocator at an assignment
  `ρ : ℕ → Loc`: walk the usage keeping an offset, and give live position
  `i` the location `ρ i`.  It subsumes both ends of the story:

      ρ = identity              `ralloc-lay`: this IS `Codegen.lay`,
                                i.e. SSA / virtual registers -- one
                                register per variable, never reused.

      ρ = round-robin over
          `t0..t3`              `regFile`: linear scan with reuse, the
                                thing a real backend does.

  and `allocMap ρ : Reindex linFib heapFib` is the pass.

  ------------------------------------------------------------------
  FAILURE 1 -- CONTEXT DEPENDENCE.  Already proved, upstream.
  ------------------------------------------------------------------

  `Codegen.pack` is compaction, and compaction is exactly "give the k-th
  LIVE variable register k", i.e. linear scan into an UNBOUNDED register
  file.  `noPackPres` refutes its `SplitPresAt appop`.  Note what that
  says: the failure is NOT register pressure -- there are infinitely many
  registers available -- it is that the address a variable receives
  depends on HOW MANY OTHER VARIABLES ARE LIVE.  Split preservation asks
  about `alloc u₁` and `alloc u₂` where `u₁`, `u₂` are the two HALVES of
  the context, and in each half the other premise's variables are dead,
  so compaction slides everything down and the halves collide.

  Any allocator whose numbering is derived from the live set --
  linear scan, live-range numbering, graph colouring -- is context
  dependent in this sense.  It is not a pointwise `ρ` at all.

  ------------------------------------------------------------------
  FAILURE 2 -- REGISTER PRESSURE.  Proved here, and it is the sharper
  one, because it bites an allocator that is NOT context dependent.
  ------------------------------------------------------------------

  Take the most innocent allocator imaginable: `regFile i = t_{i mod 4}`.
  It is pointwise (a variable's register depends on nothing but its own
  position), it is injective on any four consecutive variables, and it is
  what you get by simply spilling nothing.  It still fails, and the
  counterexample is the `noPackPres` counterexample verbatim:

      uColl  = ⟨x₀ live, x₁..x₃ dead, x₄ live⟩
      uCollL = ⟨x₀⟩          allocates  t0     (location 0)
      uCollR = ⟨x₄⟩          allocates  t0     (location 0)

  both `≡ single 0 v1` by `refl`, so `SplitPresAt` would hand us
  `single 0 v1 # single 0 v1` and `H.#-self` refutes it.  That is
  `noRegAllocPres`.

  `presInj` is the general form, and it is the theorem this file exists
  to state:

      SplitPresAt (allocMap ρ) appop  →  (i m : ℕ) → Diff (ρ i) (ρ (i+1+m))

  SPLIT PRESERVATION FORCES THE ASSIGNMENT TO BE INJECTIVE ON POSITIONS,
  uniformly in the context.  The proof builds, for each pair of positions
  `i < j`, the two-variable usage `twoU` live at exactly those two and
  splits it into the two singletons; `homParts` identifies the halves'
  allocations, `split-#` extracts disjointness, and disjointness of two
  singleton heaps IS `Diff` of their locations.

  `injPres` is the converse -- an injective `ρ` DOES preserve splittings,
  at both operations -- so the characterisation is exact:

      allocMap ρ preserves splittings   ⟺   ρ is injective.

  ("⟸" is proved for the symmetric hypothesis `Inj`; "⟹" delivers every
  pair `i < j`, and `Codegen.diff-sym` covers `j < i`.  The two meet up
  to trichotomy of `Diff`, which is not formalised here.)

  An injective `ρ : ℕ → Loc` whose range lies in a FINITE register block
  does not exist.  So:

  ------------------------------------------------------------------
  THE VERDICT
  ------------------------------------------------------------------

      A REGISTER-ALLOCATING BACKEND CANNOT BE SPLIT-PRESERVING, and
      therefore does not get no-aliasing for free.

  It is exactly as bad as the prediction, and the reason is not an
  artefact of this encoding: an allocator's whole job is to make two
  variables share a register, and sharing a register is the negation of
  `_#_`.  `SplitPresAt` is a statement UNIFORM IN THE CONTEXT, whereas a
  register allocation is injective only AT A PROGRAM POINT -- reuse
  across disjoint live ranges is a fact about time, and `Usage` (like any
  resource algebra) has no time in it.  The uniformity is the whole gap.

  WHAT A BACKEND MUST DO INSTEAD.  Three options, and only these:

    (1) SPILL.  Keep a fixed, context-independent, injective core of at
        most `numRegs` variables in registers and put every other
        variable in memory, where `Codegen.layout` (positions are
        addresses) IS split-preserving, `layPres`.  So the STACK FRAME
        inherits no-aliasing for free and the REGISTER FILE does not.
        This is the honest reading of the caller-saved/callee-saved
        convention: a calling convention is precisely a fixed injective
        assignment, and it is the only part of a register allocation
        that survives the theorem.

    (2) STAY IN SSA.  Virtual registers are `ρ = identity`, `ssaPres`
        below: unbounded, injective, split-preserving.  Every pass BEFORE
        register allocation gets no-aliasing for free; the moment you
        colour, you lose it.  This is a formal reason why an optimiser
        wants to run on SSA and why colouring is last.

    (3) CARRY THE SIDE CONDITION EXPLICITLY.  Weaken `SplitPresAt` to
        hold only at splits `Use⊎ u₁ u₂ u` for which
        `allocOf ρ u₁ # allocOf ρ u₂`.  That hypothesis, read across all
        splits of all program points, IS THE INTERFERENCE GRAPH.  So the
        interference graph is not an implementation device: it is exactly
        the proof obligation that split preservation was supposed to
        discharge for you, handed back.

  PHASE.  Phase 1, all marked: `sh` and its two lemmas, `ralloc`, the
  usage families `solo`/`twoU`/`twoL`/`twoR` with `soloR`/`twoSp`, the
  four `ralloc-*` computation lemmas, `freshR`/`apartR`/`ilvR`/`emptyR`
  (the mirror of `Codegen`'s `freshLay`/`apartLay`/`ilvLay`/`emptyLay`),
  and `coeD`.  `presInj`, `injPres`, `ssaPres`, `noRegAllocPres` and
  `noRegAlloc` are composites of those, `#-Eq`, `split-#`, `#-self`,
  `diff-irrefl` and `boolΠ`.
-}
open import Cubical.Foundations.Prelude

module ISA.RiscV.RegAlloc where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.CarrierMap

-- the SOURCE theory (linear contexts) and the two layouts already
-- proved right and wrong: `layPres` and `noPackPres`
open import TheoryGrammar.Instances.LinLam.Codegen

-- the TARGET theory, qualified, exactly as `Codegen` does
import TheoryGrammar.Instances.Heap.Graded as H

-- the register file, memory-mapped
import ISA.RiscV.Base as R

-- ==================================================================
-- OFFSET ARITHMETIC, WITHOUT `_+_`.
--
-- `sh m i` is `i + 1 + ... ` -- concretely `m + i` -- but written by
-- recursion on `m` with the offset in the ACCUMULATOR, which is the
-- shape `ralloc` recurses in.  Written this way every computation lemma
-- below is `Eq.refl` or a direct appeal to the induction hypothesis,
-- and no `subst` at a variable index ever appears.
-- ==================================================================

sh : ℕ → ℕ → ℕ                                       -- PRIMITIVE
sh zero    i = i
sh (suc m) i = sh m (suc i)

sh-suc : (m i : ℕ) → sh m (suc i) Eq.≡ suc (sh m i)  -- PRIMITIVE
sh-suc zero    i = Eq.refl
sh-suc (suc m) i = sh-suc m (suc i)

sh-0 : (m : ℕ) → sh m 0 Eq.≡ m                       -- PRIMITIVE
sh-0 zero    = Eq.refl
sh-0 (suc m) = sh-suc m 0 Eq.∙ Eq.ap suc (sh-0 m)

-- ==================================================================
-- THE POINTWISE ALLOCATOR.  PRIMITIVE (phase 1): recursion on the
-- usage, exactly `Codegen.lay` with the address `i` replaced by `ρ i`.
-- ==================================================================

ralloc : (ℕ → H.Loc) → ℕ → Usage → H.Heap
ralloc ρ i []          = []
ralloc ρ i (true  ∷ u) = (ρ i , H.v1) ∷ ralloc ρ (suc i) u
ralloc ρ i (false ∷ u) = ralloc ρ (suc i) u

allocOf : (ℕ → H.Loc) → Usage → H.Heap
allocOf ρ = ralloc ρ 0

allocMap : (ℕ → H.Loc) → Reindex linFib H.heapFib
allocMap ρ .hom _ = allocOf ρ

-- SSA IS THE IDENTITY ASSIGNMENT.  `Codegen.layout` is `allocOf` at
-- `ρ = id`, so `layPres` is the `ρ` injective case of `injPres` below,
-- and "virtual registers" is not a metaphor.
ralloc-lay : (i : ℕ) (u : Usage) → ralloc (λ j → j) i u Eq.≡ lay i u
ralloc-lay i []          = Eq.refl
ralloc-lay i (true  ∷ u) = Eq.ap ((i , H.v1) ∷_) (ralloc-lay (suc i) u)
ralloc-lay i (false ∷ u) = ralloc-lay (suc i) u

-- ==================================================================
-- TWO VARIABLES, AT ARBITRARY POSITIONS, AND THE SPLIT BETWEEN THEM.
--
-- `twoU i m` has exactly positions `i` and `sh m (suc i)` live -- as `m`
-- ranges over ℕ that is every position strictly after `i`.  PRIMITIVE
-- (phase 1): these are the witnesses `presInj` needs and nothing else
-- uses them.
-- ==================================================================

solo : ℕ → Usage                        -- length `suc m`, live at `m`
solo zero    = true ∷ []
solo (suc m) = false ∷ solo m

twoU twoL twoR : ℕ → ℕ → Usage
twoU zero    m = true  ∷ solo m
twoU (suc i) m = false ∷ twoU i m
twoL zero    m = true  ∷ none (suc m)
twoL (suc i) m = false ∷ twoL i m
twoR zero    m = false ∷ solo m
twoR (suc i) m = false ∷ twoR i m

soloR : (m : ℕ) → Use⊎ (none (suc m)) (solo m) (solo m)
soloR zero    = uright unil
soloR (suc m) = uskip (soloR m)

twoSp : (i m : ℕ) → Use⊎ (twoL i m) (twoR i m) (twoU i m)
twoSp zero    m = uleft (soloR m)
twoSp (suc i) m = uskip (twoSp i m)

-- ==================================================================
-- ... and what the allocator does to them.  Each half is a SINGLETON
-- heap, so its disjointness from the other half is a single `Diff`.
-- ==================================================================

ralloc-none : (ρ : ℕ → H.Loc) (k i : ℕ) → ralloc ρ i (none k) Eq.≡ []
ralloc-none ρ zero    i = Eq.refl
ralloc-none ρ (suc k) i = ralloc-none ρ k (suc i)

ralloc-solo : (ρ : ℕ → H.Loc) (m i : ℕ)
            → ralloc ρ i (solo m) Eq.≡ H.single (ρ (sh m i)) H.v1
ralloc-solo ρ zero    i = Eq.refl
ralloc-solo ρ (suc m) i = ralloc-solo ρ m (suc i)

ralloc-twoL : (ρ : ℕ → H.Loc) (i m j : ℕ)
            → ralloc ρ j (twoL i m) Eq.≡ H.single (ρ (sh i j)) H.v1
ralloc-twoL ρ zero    m j = Eq.ap ((ρ j , H.v1) ∷_) (ralloc-none ρ (suc m) (suc j))
ralloc-twoL ρ (suc i) m j = ralloc-twoL ρ i m (suc j)

ralloc-twoR : (ρ : ℕ → H.Loc) (i m j : ℕ)
            → ralloc ρ j (twoR i m) Eq.≡ H.single (ρ (sh m (suc (sh i j)))) H.v1
ralloc-twoR ρ zero    m j = ralloc-solo ρ m (suc j)
ralloc-twoR ρ (suc i) m j = ralloc-twoR ρ i m (suc j)

-- ==================================================================
-- THE FORCING THEOREM.
--
-- Split preservation at `appop` says the two halves of EVERY context
-- split allocate disjointly.  Instantiate at the split of `twoU i m`
-- into its two singleton usages and read off `Diff`.
-- ==================================================================

private
  coeD : {a b a' b' : H.Loc} → a Eq.≡ a' → b Eq.≡ b'
       → H.Diff a b → H.Diff a' b'
  coeD Eq.refl Eq.refl d = d                          -- PRIMITIVE

presApart : (ρ : ℕ → H.Loc) → SplitPresAt (allocMap ρ) appop
          → (i m : ℕ)
          → H.single (ρ (sh i 0)) H.v1
            H.# H.single (ρ (sh m (suc (sh i 0)))) H.v1
presApart ρ P i m =
  H.#-Eq (ralloc-twoL ρ i m 0) (ralloc-twoR ρ i m 0)
    (H.#-Eq (P .homParts (twoU i m) sp true) (P .homParts (twoU i m) sp false)
            (H.split-# (allocOf ρ (twoU i m)) (P .homSplit (twoU i m) sp)))
  where
  sp : linFib .Split appop (twoU i m)
  sp = twoL i m , twoR i m , twoSp i m

-- THE RESULT.  `sh m (suc i)` is `i + 1 + m`, so this says: `ρ` sends
-- distinct positions to distinct locations, with no reference to any
-- particular context.  A register allocator does the opposite by
-- definition.
presInj : (ρ : ℕ → H.Loc) → SplitPresAt (allocMap ρ) appop
        → (i m : ℕ) → H.Diff (ρ i) (ρ (sh m (suc i)))
presInj ρ P i m =
  coeD (Eq.ap ρ (sh-0 i))
       (Eq.ap ρ (Eq.ap (λ z → sh m (suc z)) (sh-0 i)))
       (presApart ρ P i m .fst .fst)

-- ==================================================================
-- THE CONVERSE: an INJECTIVE assignment does preserve splittings.  Each
-- clause is `Codegen`'s corresponding clause with `below→Diff j i`
-- replaced by `inj j i (below→Diff j i)` -- that single substitution is
-- the entire difference between "positions are addresses" and "an
-- injective renaming of positions is addresses".
-- ==================================================================

Inj : (ℕ → H.Loc) → Type₀
Inj ρ = (j k : ℕ) → H.Diff j k → H.Diff (ρ j) (ρ k)

-- PRIMITIVE (phase 1), all four: the mirror of `freshLay` / `apartLay`
-- / `ilvLay` / `emptyLay`.
freshR : (ρ : ℕ → H.Loc) → Inj ρ → (u : Usage) (i j : ℕ)
       → Below j i → H.Fresh (ρ j) (ralloc ρ i u)
freshR ρ inj []          i j b = tt
freshR ρ inj (true  ∷ u) i j b =
  inj j i (below→Diff j i b) , freshR ρ inj u (suc i) j (below-weak j i b)
freshR ρ inj (false ∷ u) i j b = freshR ρ inj u (suc i) j (below-weak j i b)

ilvR : (ρ : ℕ → H.Loc) → ∀ {u₁ u₂ u} → Use⊎ u₁ u₂ u → (i : ℕ)
     → H.Ilv (ralloc ρ i u₁) (ralloc ρ i u₂) (ralloc ρ i u)
ilvR ρ unil       i = H.nil
ilvR ρ (uleft s)  i = H.left  (ilvR ρ s (suc i))
ilvR ρ (uright s) i = H.right (ilvR ρ s (suc i))
ilvR ρ (uskip s)  i = ilvR ρ s (suc i)

apartR : (ρ : ℕ → H.Loc) → Inj ρ → ∀ {u₁ u₂ u} → Use⊎ u₁ u₂ u → (i : ℕ)
       → ralloc ρ i u₁ H.# ralloc ρ i u₂
apartR ρ inj unil               i = tt
apartR ρ inj (uleft  {v = v} s) i =
  freshR ρ inj v (suc i) i (below-suc i) , apartR ρ inj s (suc i)
apartR ρ inj (uright {u = u} s) i =
  #-cons-r (ralloc ρ (suc i) u) _ (ρ i) H.v1
           (freshR ρ inj u (suc i) i (below-suc i)) (apartR ρ inj s (suc i))
apartR ρ inj (uskip s)          i = apartR ρ inj s (suc i)

emptyR : (ρ : ℕ → H.Loc) (u : Usage) (i : ℕ) → Empty u → H.IsNil (ralloc ρ i u)
emptyR ρ []          i e = tt
emptyR ρ (true  ∷ u) i e = e
emptyR ρ (false ∷ u) i e = emptyR ρ u (suc i) e

injPres : (ρ : ℕ → H.Loc) → Inj ρ → (o : MonOp) → SplitPresAt (allocMap ρ) o
injPres ρ inj nilop .homSplit u e = emptyR ρ u 0 e
injPres ρ inj nilop .homParts u e ()
injPres ρ inj appop .homSplit u (u₁ , u₂ , s) =
  allocOf ρ u₁ , allocOf ρ u₂ , ilvR ρ s 0 , apartR ρ inj s 0
injPres ρ inj appop .homParts u (u₁ , u₂ , s) =
  boolΠ {M = λ a → H.boolΠ {M = λ _ → H.Heap} (allocOf ρ u₁) (allocOf ρ u₂) a
                     Eq.≡ allocOf ρ (boolΠ {M = λ _ → Usage} u₁ u₂ a)}
        Eq.refl Eq.refl

-- SSA / VIRTUAL REGISTERS: the identity assignment is injective on the
-- nose, so it preserves splittings.  This is `Codegen.layPres` again,
-- via `ralloc-lay`, and it is option (2) of the verdict.
ssaPres : (o : MonOp) → SplitPresAt (allocMap (λ j → j)) o
ssaPres = injPres (λ j → j) (λ j k d → d)

-- ==================================================================
-- THE ALLOCATOR THAT A BACKEND ACTUALLY WRITES.
--
-- Round-robin over `t0..t3`: pointwise (a variable's register depends on
-- nothing but its own position), injective on any four consecutive
-- variables, and spilling nothing.  It is about as well behaved as a
-- reusing allocator can be.
-- ==================================================================

regOf : ℕ → R.Reg                                     -- PRIMITIVE
regOf zero                            = R.t0
regOf (suc zero)                      = R.t1
regOf (suc (suc zero))                = R.t2
regOf (suc (suc (suc zero)))          = R.t3
regOf (suc (suc (suc (suc n))))       = regOf n

regFile : ℕ → H.Loc
regFile i = R.regLoc (regOf i)

-- ==================================================================
-- THE COUNTEREXAMPLE, in the style of `noPackPres`: a two-variable
-- program whose halves both allocate `t0`, so `_#_` is uninhabited.
--
-- Five variables and four registers -- pigeonhole, made concrete.
-- ==================================================================

uColl uCollL uCollR : Usage
uColl  = true  ∷ false ∷ false ∷ false ∷ true  ∷ []
uCollL = true  ∷ false ∷ false ∷ false ∷ false ∷ []
uCollR = false ∷ false ∷ false ∷ false ∷ true  ∷ []

collSplit : Use⊎ uCollL uCollR uColl
collSplit = uleft (uskip (uskip (uskip (uright unil))))

-- both halves of the split allocate the SAME register ...
_ : allocOf regFile uCollL ≡ H.single 0 H.v1
_ = refl

_ : allocOf regFile uCollR ≡ H.single 0 H.v1
_ = refl

-- ... and for contrast, SSA does not: `x₀ ↦ 0`, `x₄ ↦ 4`
_ : allocOf (λ j → j) uCollL ≡ H.single 0 H.v1
_ = refl

_ : allocOf (λ j → j) uCollR ≡ H.single 4 H.v1
_ = refl

-- ... so `SplitPresAt` would hand us `single 0 v1 # single 0 v1`, and
-- `H.#-self` refutes it.  Word for word `Codegen.noPackPres`.
noRegAllocPres : SplitPresAt (allocMap regFile) appop → ⊥
noRegAllocPres P =
  H.#-self 0 H.v1
    (H.#-Eq (P .homParts uColl sp true) (P .homParts uColl sp false)
            (H.split-# (allocOf regFile uColl) (P .homSplit uColl sp)))
  where
  sp : linFib .Split appop uColl
  sp = uCollL , uCollR , collSplit

-- ... and the same fact obtained from the GENERAL theorem instead: the
-- forced injectivity of `regFile` at the pair `(0 , 4)` is `Diff 0 0`.
noRegAlloc : SplitPresAt (allocMap regFile) appop → ⊥
noRegAlloc P = H.diff-irrefl 0 (presInj regFile P 0 3)

-- ==================================================================
-- AND THE OTHER FAILURE, for the record: `Codegen.pack` is linear scan
-- into an UNBOUNDED register file, and `Codegen.noPackPres` already
-- refutes it.  So the two failures are genuinely independent --
-- adding registers does not fix compaction, and removing compaction
-- does not fix register pressure.
-- ==================================================================

noCompactingAlloc : SplitPresAt packMap appop → ⊥
noCompactingAlloc = noPackPres
