{-
  PRECISION OVER HEAPS -- THE INSTANCE.  The notions are `TheoryGrammar.
  Precision`'s; nothing generic is restated here.

  `Decidable.Tensor.DecReadable.splitProp` says a heap has AT MOST ONE
  splitting.  A one-cell heap has two, so the module `Decidable.Tensor.
  UniqueSplit` -- which is parameterised by it -- is unavailable over
  heaps (`splitProp-fails`).  That module used to be called `Precise`,
  and this file is why it is not: its hypothesis is unique readability,
  which heaps refute, while precision over heaps is perfectly good.

  Separation logic's precision RELATIVISES that to a predicate, and the
  generic file proves `splitProp` is its unrelativised case.  `⊤G` is
  what separates them: imprecise here, hence `splitProp` false.

  WHAT THIS FILE OWES THE GENERIC ONE: `slotDet` -- under DISJOINTNESS a
  part determines its complement -- which is exactly the hypothesis
  `preciseP→preciseI` takes, and the one place the `u # v` conjunct of
  `HeapSplit` does work.  `ilv-det` is its PRIMITIVE.

  Read beside `Heap/Precise.agda`, which takes the STRONGER, splitting-
  free `Pins A = A u → A v → u ≡ v` and gets non-duplication from it.
  Precision constrains only the parts of a COMMON whole, so `Pins`
  implies it and not conversely -- §6, with `∃v. l ↦ v` separating.

  DEFINES `Precise` (pointwise) and `PreciseI` (internal); the positive
  cases `precise-rep`/`precise-emp`/`precise-↦` and `preciseI-rep`/
  `preciseI-emp`/`preciseI-↦`; the refutations `imprecise-⊤`,
  `imprecise-⊕`, `impreciseI-⊤`, `splitProp-fails`, `decReadable-fails`,
  `merge-fails`; the PRIMITIVE `ilv-det` with the hypothesis `slotDet`
  it feeds; and the bridge `pins→precise`/`pins→preciseI` with its
  converse's refutation `not-pins-∃↦`.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Heap.Precision where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Precision

open import TheoryGrammar.Instances.Heap.Emp public

-- `Pins` is `Heap/Precise`'s; §6 below is the one implication between
-- the two files, and it runs in only one direction.
open import TheoryGrammar.Instances.Heap.Precise using (Pins)

-- the generic notions, at this promodel.  `PreciseI` is hidden only
-- because the ∗-spelling below re-earns the name.
open Prec heapFib public hiding (PreciseI)

-- `MonAr appop` is `Bool` and `boolΠ` is its eliminator, so the binary
-- reading is available and both computation rules are `Eq.refl`.
open Binary appop true false boolΠ (λ _ _ → Eq.refl) (λ _ _ → Eq.refl) public

-- ==================================================================
-- 1.  POINTWISE PRECISION, and the framework's hypothesis.
-- ==================================================================

Precise : Gr → Type₀
Precise = PreciseP appop true

-- `splitProp` implies precision of EVERYTHING -- the generic degenerate
-- case, cited rather than reproved
splitProp→precise : SplitPropAt appop → (A : Gr) → Precise A
splitProp→precise sp A =
  partsPropAt→preciseP appop true A (splitPropAt→partsPropAt appop sp)

-- ==================================================================
-- 2.  THE PRECISE EXAMPLES.  A representable is precise for a trivial
-- reason: two things equal to `c` are equal.  `emp` and `l ↦ x` are
-- both representables, so both come from the generic `preciseP-⌈⌉`.
-- ==================================================================

precise-rep : (c : Heap) → Precise ⌈ c ⌉
precise-rep = preciseP-⌈⌉ appop true

precise-emp : Precise empR
precise-emp = precise-rep []

precise-↦ : (l : Loc) (x : Val) → Precise (l ↦ x)
precise-↦ l x = precise-rep (single l x)

-- ==================================================================
-- 3.  THE IMPRECISE ONES.  One cell splits two ways, with left parts
-- `[]` and the cell itself, so any predicate holding at both is
-- imprecise.  `⊤G` is the extreme case, `emp ⊕ (l ↦ x)` the textbook
-- one.
-- ==================================================================

nil≢cons : {c : Cell} {h : Heap} → ([] Eq.≡ (c ∷ h)) → ⊥
nil≢cons ()

private
  s : Heap
  s = single 0 v0

  pL pR : heapFib .Split appop s
  pL = [] , s , ilv-nilL s , tt
  pR = s , [] , ilv-nilR s , #-nil s

imprecise-⊤ : Precise ⊤G → ⊥
imprecise-⊤ pr = nil≢cons (pr s pL pR tt tt)

imprecise-⊕ : Precise (empR ⊕ (0 ↦ v0)) → ⊥
imprecise-⊕ pr = nil≢cons
  (pr s pL pR (⊕-I₁ {A = empR} {B = 0 ↦ v0} [] Eq.refl)
              (⊕-I₂ {B = 0 ↦ v0} {A = empR} s  Eq.refl))

-- ... and therefore `splitProp` itself fails, so `Decidable.Tensor`'s
-- `UniqueSplit` module cannot be instantiated over heaps.  Stated at
-- the one operation that refutes it; `DecReadable`'s field is stronger.
splitProp-fails : SplitPropAt appop → ⊥
splitProp-fails sp = imprecise-⊤ (splitProp→precise sp ⊤G)

decReadable-fails : SplitProp → ⊥
decReadable-fails sp = splitProp-fails (sp appop)

-- ... equivalently: `⊤` is not precise INTERNALLY either, which by the
-- generic `merge→partsProp` is the same fact one step earlier
merge-fails : MergeAt ℓ-zero appop → ⊥
merge-fails mg = imprecise-⊤ (partsPropAt→preciseP appop true ⊤G
                                (merge→partsProp appop mg))

-- ==================================================================
-- 4.  PRECISION, INTERNALLY: `∗` distributes over `&`.
--
-- The generic form is `Binary.PreciseB`, and at `boolΠ` it IS the
-- separation-logic statement -- `refl`, below.  What the instance owes
-- is `slotDet`: without `_#_` it is FALSE (`Ilv [a] v [a,b,a]` has two
-- solutions), so this is a place where the partiality HELPS.
-- ==================================================================

-- No-confusion for the cell list, in `Eq`.  Needed because the two
-- interleavings must be matched TOGETHER and `Cell` is a Σ: sharing the
-- whole as an INDEX makes the unifier ask to delete a reflexive
-- equation at Σ, which `--without-K` refuses.  Passing the coincidence
-- of the wholes as an `Eq` argument instead keeps every index flexible,
-- and these three lemmas do by hand what the unifier would have done.
cons-inj-head : {c c' : Cell} {w w' : Heap} → (c ∷ w) Eq.≡ (c' ∷ w') → c Eq.≡ c'
cons-inj-head Eq.refl = Eq.refl

cons-inj-tail : {c c' : Cell} {w w' : Heap} → (c ∷ w) Eq.≡ (c' ∷ w') → w Eq.≡ w'
cons-inj-tail Eq.refl = Eq.refl

cons-Eq : {c c' : Cell} {w w' : Heap} → c Eq.≡ c' → w Eq.≡ w' → (c ∷ w) Eq.≡ (c' ∷ w')
cons-Eq Eq.refl Eq.refl = Eq.refl

cons≢nil : {c : Cell} {h : Heap} → ((c ∷ h) Eq.≡ []) → ⊥
cons≢nil ()

cell-diff-irrefl : {c c' : Cell} → c Eq.≡ c' → Diff (c .fst) (c' .fst) → ⊥
cell-diff-irrefl Eq.refl d = diff-irrefl _ d

-- PRIMITIVE (recursion on the two interleavings).  The two mixed cases
-- are the ones disjointness kills: the same cell would sit in both
-- parts, and a location is never apart from itself.
ilv-det : {u v v' h h' : Heap} → Ilv u v h → Ilv u v' h' → h Eq.≡ h'
        → u # v → u # v' → v Eq.≡ v'
ilv-det nil       nil       e d d' = Eq.refl
ilv-det nil       (right q) e d d' = E.rec (nil≢cons e)
ilv-det (left p)  (left q)  e d d' = ilv-det p q (cons-inj-tail e) (d .snd) (d' .snd)
ilv-det (left p)  (right q) e d d' =
  E.rec (cell-diff-irrefl (cons-inj-head e) (d' .fst .fst))
ilv-det (right p) nil       e d d' = E.rec (cons≢nil e)
ilv-det (right p) (left q)  e d d' =
  E.rec (cell-diff-irrefl (Eq.sym (cons-inj-head e)) (d .fst .fst))
ilv-det (right p) (right q) e d d' =
  cons-Eq (cons-inj-head e)
          (ilv-det p q (cons-inj-tail e) (#-tail _ _ _ d) (#-tail _ _ _ d'))

-- THE HYPOTHESIS THE GENERIC BRIDGE TAKES: the left part of a disjoint
-- splitting determines the right one.  `ilv-det` is the whole content;
-- `boolΠ` is the arity's eliminator, as everywhere in this instance.
slotDet : SlotDet appop true
slotDet h (u , v , ilv , d) (u' , v' , ilv' , d') e =
  boolΠ e (ilv-det ilv (coeEq (λ z → Ilv z v' h) (Eq.sym e) ilv') Eq.refl d
                   (#-Eq (Eq.sym e) Eq.refl d'))

-- `PreciseI A` DENOTES "A knows which part of the heap it owns": given
-- one whole satisfied two ways with the same A-factor, the SAME
-- splitting carries both complements, so `∗` distributes over `&`.  No
-- splitting is mentioned in the statement -- that is what makes it the
-- internal form.  It is the separation-logic spelling of
-- `Binary.PreciseB`, and it is that module's statement on the nose.
PreciseI : Gr → Type₁
PreciseI A = (B C : Gr) → ((A ∗ B) & (A ∗ C)) ⊢ (A ∗ (B & C))

_ : PreciseI ≡ PreciseB
_ = refl

-- POINTWISE ⟹ INTERNAL is generic; `slotDet` is what it costs, so
-- every representable is precise in BOTH senses.
preciseI-rep : (c : Heap) → PreciseI ⌈ c ⌉
preciseI-rep c = preciseP→preciseB ⌈ c ⌉ slotDet (precise-rep c)

preciseI-emp : PreciseI empR
preciseI-emp = preciseI-rep []

preciseI-↦ : (l : Loc) (x : Val) → PreciseI (l ↦ x)
preciseI-↦ l x = preciseI-rep (single l x)

-- ... and `⊤G` fails internally too: `⊤ ∗ emp` and `⊤ ∗ (0 ↦ v0)` both
-- hold at one cell, but their complements are different heaps, so no
-- single splitting can carry `emp & (0 ↦ v0)`.
impreciseI-⊤ : PreciseI ⊤G → ⊥
impreciseI-⊤ pr = nil≢cons (Eq.sym (dist .snd false .fst) Eq.∙ dist .snd false .snd)
  where dist : (⊤G ∗ (empR & (0 ↦ v0))) s
        dist = pr empR (0 ↦ v0) s
                 ( ((s , [] , ilv-nilR s , #-nil s) , boolΠ tt Eq.refl)
                 , (([] , s , ilv-nilL s , tt)      , boolΠ tt Eq.refl) )

-- ==================================================================
-- 5.  ... AND IT COMPUTES.  The generic merge hands back the FIRST
-- splitting, so at a one-cell heap owned by `0 ↦ v0` the left part is
-- that cell.  (`Heap/Tests` runs the two-cell version.)
-- ==================================================================

private
  both : (((0 ↦ v0) ∗ empR) & ((0 ↦ v0) ∗ empR)) s
  both = (pR , boolΠ Eq.refl Eq.refl) , (pR , boolΠ Eq.refl Eq.refl)

  _ : heapFib .parts appop s (preciseI-↦ 0 v0 empR empR s both .fst) true Eq.≡ s
  _ = Eq.refl

-- ==================================================================
-- 6.  PINNING ⟹ PRECISION, AND NOT CONVERSELY.
--
-- `Heap/Precise.Pins A = A u → A v → u ≡ v` asks `A` to determine its
-- heap OUTRIGHT.  Precision asks much less: only that `A` determine the
-- slot it occupies IN A GIVEN WHOLE -- the two heaps it compares are
-- already the parts of one `m`, at one operation, at one slot.  So the
-- implication is a forgetting of hypotheses and nothing more, and it is
-- the bridge the two files were missing.
-- ==================================================================

pins→precise : (A : Gr) → Pins A → Precise A
pins→precise A pins m p q x y = Eq.pathToEq (pins x y)

-- ... and via §4 the internal form comes free, since `slotDet` is what
-- `preciseP→preciseB` costs and this instance has it.
pins→preciseI : (A : Gr) → Pins A → PreciseI A
pins→preciseI A pins = preciseP→preciseB A slotDet (pins→precise A pins)

-- THE CONVERSE FAILS, and `∃v. l ↦ v` is the separating example: the
-- cell at `l` holds SOMETHING.  It does not pin -- `l ↦ v0` and
-- `l ↦ v1` are different heaps, and that is `not-pins-∃↦` below -- yet
-- it IS precise, because a splitting's left part is a sublist of the
-- whole and `u # v` forbids the whole from carrying `l` twice, so at a
-- fixed `m` there is only one cell it can be.  (Precision is exactly
-- the relativisation that survives this: `Heap/Precise` needs the
-- stronger hypothesis because `precise-no-dup` compares parts of TWO
-- different composites.)
--
-- `⌈ c ⌉ h` is `h Eq.≡ c`, so this is `Σ` over the value.
∃↦ : Loc → Gr
∃↦ l h = Σ[ x ∈ Val ] ⌈ single l x ⌉ h

private
  -- no-confusion for `Val`, and for a heap's head cell.  Stated as
  -- recursive predicates so `coeEq` (a strict transport) moves them.
  isV0 : Val → Type₀
  isV0 v0 = Unit
  isV0 v1 = ⊥
  isV0 v2 = ⊥

  headIsV0 : Heap → Type₀
  headIsV0 []            = ⊥
  headIsV0 ((_ , x) ∷ _) = isV0 x

single-inj-val : (l : Loc) → single l v0 ≡ single l v1 → ⊥
single-inj-val l e = coeEq headIsV0 (Eq.pathToEq e) tt

not-pins-∃↦ : (l : Loc) → Pins (∃↦ l) → ⊥
not-pins-∃↦ l pins =
  single-inj-val l (pins {single l v0} {single l v1}
                         (v0 , Eq.refl) (v1 , Eq.refl))
