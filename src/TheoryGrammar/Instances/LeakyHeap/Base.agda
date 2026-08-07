{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE LEAKY HEAP: SEPARATION LOGIC THAT PERMITS GARBAGE, AND WHAT ONE
  CONSTRUCTOR COSTS.

  `Instances/Heap/Base` presents heaps as a partial commutative monoid,
  and its splitting relation is EXACT interleaving:

      data Ilv : Heap → Heap → Heap → Type₀ where
        nil   : Ilv [] [] []
        left  : Ilv u v w → Ilv (c ∷ u) v (c ∷ w)
        right : Ilv u v w → Ilv u (c ∷ v) (c ∷ w)

  Every cell of the whole is claimed by exactly one part.  That is the
  CLASSICAL (exact, "tight") reading of `∗`.  Add one constructor:

        leak  : SubIlv u v w → SubIlv u v (c ∷ w)

  -- a cell of the whole that NEITHER part owns.  This file is the
  consequence of that one line.

  It is precisely the heap-side mirror of `Instances/Affine/Base`'s

        adrop : Aff⊎ u v w → Aff⊎ (false ∷ u) (false ∷ v) (true ∷ w)

  read at cells instead of at variable slots, and the two files have the
  same shape for that reason: the same row degrades, the same row
  survives, the same unit law breaks, the same monad appears.  What is
  new is that on the separation-logic side the monad HAS A NAME --
  see `LeakyHeap/Intuitionistic.agda`.

  ------------------------------------------------------------------
  THREE RELAXATIONS, THREE DIFFERENT AXES.

  `HeapSplit appop h = Σ u, Σ v, Ilv u v h × (u # v)` is a conjunction of
  two independent conditions, and there are two ways to weaken it.
  `Heap/Base` already contains one of them:

      cellFib  DELETES the `u # v` conjunct.       (the DISJOINTNESS axis)
      leakyFib WEAKENS `Ilv` to `SubIlv`.          (the EXACTNESS axis)

  These are ORTHOGONAL and it matters that they are:

    * `cellFib` allows two parts to claim the SAME cell.  It is `Bags` at
      `Cell`, it gains a `LaxPoint` (`cellPoint`, bag union), and it
      keeps everything else -- the interleaving is untouched, so the
      grading is still an equation and the unit law still holds.

    * `leakyFib` allows the WHOLE to carry a cell no part claims.  It
      KEEPS `u # v` in full -- disjointness is not what is being relaxed
      -- so it still has no lax point (`noLeakyPoint` below is
      `Heap/Connectives.noHeapPoint` verbatim, and the proof goes through
      unchanged precisely because the conjunct that carries it survived).
      What it loses instead is the additivity EQUATION and the RIGHT UNIT
      LAW.

  So the two relaxations trade in opposite directions: `cellFib` buys a
  point at the cost of separation, `leakyFib` buys weakening at the cost
  of exactness, and neither implies the other.

  ------------------------------------------------------------------
  THE TABLE.  Each cell names the theorem that backs it.

                   EXACT (`Ilv`)          LEAKY (`SubIlv`)       NO-DISJOINTNESS
                   `heapFib`              `leakyFib`, HERE       `cellFib`
  ---------------  ---------------------  ---------------------  ---------------------
  what is          --                     `Ilv` ⇝ `SubIlv`       `u # v` conjunct
  relaxed                                 (one new constructor)  DELETED; the
                                          `u # v` KEPT IN FULL   interleaving KEPT
  ---------------  ---------------------  ---------------------  ---------------------
  grading          HOLDS, and additivity  HOLDS, but additivity  HOLDS, EQUATION
  (`deg≤`/`deg<`)  is an EQUATION         is only an INEQUALITY  -- same `Ilv`, so
                   `ilvLen≡` (§5)         `subIlvLen≤` (§5);     `ilvLen≡` again
                   `Heap/Graded`          the equation is        (§8)
                                          REFUTED, `noSubIlvLen≡`
                                          `leakyGrading` (§5)
  ---------------  ---------------------  ---------------------  ---------------------
  frame rule       HOLDS                  HOLDS -- `frame`,      HOLDS
                   `Heap/Connectives`     `frameL` (§6), and     (a fortiori; §6's
                   `.frame`               INSENSITIVE: see §6    argument is generic)
  ---------------  ---------------------  ---------------------  ---------------------
  right unit       HOLDS                  REFUTED                HOLDS
  `A ∗ emp ⊢ A`    `Heap/Emp.∗-emp`       `no-∗-unitR`, and      `Cell.∗ᶜ-empR` (§8)
                                          `⇓ A = A ∗ emp` is a
                                          nontrivial MONAD
                                          (`Intuitionistic.agda`)
  ---------------  ---------------------  ---------------------  ---------------------
  lax point        REFUTED                REFUTED                HOLDS
                   `Heap/Connectives`     `noLeakyPoint` (§7);   `Heap/Base.cellPoint`
                   `.noHeapPoint`         the `#` conjunct is
                                          what carries this, and
                                          it was not touched
  ---------------  ---------------------  ---------------------  ---------------------

  Reading the table by ROWS rather than columns is the point: no single
  row separates the three, but the pair (unit law, lax point) does --
  exact has both, leaky has neither in the same place, and cellFib has
  both but for a different reason.

  ------------------------------------------------------------------
  WHY THE GRADING SURVIVES, AND WHY THAT IS NOT AUTOMATIC.

  `Heap/Graded` grades a heap by its cell count and gets

      length u + length v ≡ length w                     (`ilvLen≡`)

  from `Ilv`.  `leak` destroys it -- the whole has a cell neither part
  has -- and `noSubIlvLen≡` refutes it outright with the two-line
  witness `leak snil : SubIlv [] [] ((0,v0) ∷ [])`.  What replaces it is

      length u + length v ≤ length w                     (`subIlvLen≤`)

  and reading `deg≤`/`deg<` again shows this is all they ever needed:
  `deg≤` wants `length u ≤ length w`, which follows from `length u ≤
  length u + length v` and the inequality; `deg<` wants strictness when
  the SIBLING is nonempty, which follows from `length u < length u +
  length v` and the inequality.  Both uses were already ONE-SIDED.  This
  is `Affine/Base`'s `liveSplit≤` argument transposed to cells, verbatim,
  and the slogan is the same: leaking makes the degree drop FASTER, and
  a well-founded recursion is never harmed by losing resources, only by
  gaining them.  So `Ind`/`Guard`/`hyloC`/`löb` remain available over
  the leaky promodel.

  ------------------------------------------------------------------
  PRIMITIVE (matching the representation): `SubIlv`, `LeakySplit`,
  `LeakyParts`, the `∗`-interface (`∗-mk`, `∗-E'`, `∗-map`), `emp-mk`,
  `split-#`, and the length lemmas of §5.  `boolΠ`, `Ilv`, `_#_`,
  `IsNil`, `Heap` are imported from `Heap/Base` and REUSED rather than
  re-declared -- in particular `boolΠ` is nominally the SAME function
  there and here, which is what lets the two files' `∗`s be compared at
  all.  Everything after §6 is a term of the calculus.
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.LeakyHeap.Base where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Unit
open import Cubical.Data.List using (List; []; _∷_; length)
open import Cubical.Data.Empty as E using (⊥; ⊥*)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib
open import TheoryGrammar.Grading
open import TheoryGrammar.Precision using (coeEq)

-- `Heap`, `Cell`, `Loc`, `Val`, `single`, `Diff`, `Fresh`, `_#_`,
-- `#-nil`, `#-self`, `#-Eq`, `IsNil`, `Ilv`, `ilv-nilR-inv`, `boolΠ`,
-- `cellFib`, `cellPoint`, and `monoidSig`.  Read-only.
open import TheoryGrammar.Instances.Heap.Base public

-- ==================================================================
-- §1  THE LEAKY SPLITTING.
--
-- `Ilv` plus `leak`.  Read the three inherited constructors as the exact
-- discipline and `leak` as the garbage one: the whole is responsible for
-- a cell that NEITHER premise claims, so it is leaked at this node.
--
-- Still absent: any clause putting one cell into BOTH parts.  That
-- absence is what `_#_` also enforces at the level of locations, and it
-- is why §7 goes through: leaking is a way to LOSE a cell, not to share
-- one.
-- ==================================================================

data SubIlv : Heap → Heap → Heap → Type₀ where     -- PRIMITIVE
  snil   : SubIlv [] [] []
  sleft  : ∀ {c u v w} → SubIlv u v w → SubIlv (c ∷ u) v (c ∷ w)
  sright : ∀ {c u v w} → SubIlv u v w → SubIlv u (c ∷ v) (c ∷ w)
  -- THE ONE NEW CONSTRUCTOR.  A cell claimed by neither part: leaked.
  leak   : ∀ {c u v w} → SubIlv u v w → SubIlv u v (c ∷ w)

-- the inclusion, constructor for constructor
ilv→subIlv : ∀ {u v w} → Ilv u v w → SubIlv u v w
ilv→subIlv nil       = snil
ilv→subIlv (left s)  = sleft  (ilv→subIlv s)
ilv→subIlv (right s) = sright (ilv→subIlv s)

-- ... and it is STRICT.  A one-cell heap splits leakily into two empty
-- parts, and exactly interleaves into nothing of the sort.
noIlv-leak : Ilv [] [] (single 0 v0) → ⊥
noIlv-leak ()

subIlv⊋ilv : SubIlv [] [] (single 0 v0) × (Ilv [] [] (single 0 v0) → ⊥)
subIlv⊋ilv = leak snil , noIlv-leak

-- the empty middle: a leaky splitting with a nil right part is a
-- SUBLIST inclusion, and this projection is used everywhere below
subIlv-nilM : ∀ {u v w} → SubIlv u v w → IsNil v → SubIlv u [] w
subIlv-nilM snil       e = snil
subIlv-nilM (sleft s)  e = sleft (subIlv-nilM s e)
subIlv-nilM (sright s) e = E.rec e
subIlv-nilM (leak s)   e = leak (subIlv-nilM s e)

-- the unit splitting that DOES exist: keep everything
subIlv-nilR : (u : Heap) → SubIlv u [] u
subIlv-nilR []      = snil
subIlv-nilR (c ∷ u) = sleft (subIlv-nilR u)

subIlv-nilL : (v : Heap) → SubIlv [] v v
subIlv-nilL []      = snil
subIlv-nilL (c ∷ v) = sright (subIlv-nilL v)

-- THE LEAKY AXIOM, at the index.  EVERYTHING can be thrown away.  In
-- `Ilv` this is refuted: `Ilv [] [] w` forces `w ≡ []`.  Compare
-- `Affine/Base.affDropAll`.
leakAll : (h : Heap) → SubIlv [] [] h
leakAll []      = snil
leakAll (c ∷ h) = leak (leakAll h)

-- ==================================================================
-- §2  THE PROMODEL.
--
-- Note what is NOT changed: `LeakySplit nilop` is still `IsNil`, and
-- the `u # v` conjunct of `appop` is still there in full.  Exactly one
-- thing moved.
-- ==================================================================

LeakySplit : (o : MonOp) → Heap → Type₀              -- PRIMITIVE
LeakySplit nilop h = IsNil h
LeakySplit appop h = Σ[ u ∈ Heap ] Σ[ v ∈ Heap ] (SubIlv u v h × (u # v))

LeakyParts : (o : MonOp) (h : Heap) → LeakySplit o h → MonAr o → Heap
LeakyParts nilop h sp ()                             -- PRIMITIVE
LeakyParts appop h (u , v , _) = boolΠ u v

leakyFib : Fibered monoidSig ℓ-zero ℓ-zero
leakyFib .carrier _ = Heap
leakyFib .Split     = LeakySplit
leakyFib .parts     = LeakyParts

-- the promodel inclusion, at the level of splittings
heapSplit→leakySplit : (o : MonOp) (h : Heap)
                     → heapFib .Split o h → leakyFib .Split o h
heapSplit→leakySplit nilop h e = e
heapSplit→leakySplit appop h (u , v , i , d) = u , v , ilv→subIlv i , d

-- ... and it preserves the parts DEFINITIONALLY, which is the honest
-- statement that `heapFib` is a sub-promodel of `leakyFib` on the nose
-- rather than up to a transport.
heapSplit→leakySplit-parts :
  (o : MonOp) (h : Heap) (sp : heapFib .Split o h) (a : MonAr o)
  → leakyFib .parts o h (heapSplit→leakySplit o h sp) a
    ≡ heapFib .parts o h sp a
heapSplit→leakySplit-parts nilop h sp ()
heapSplit→leakySplit-parts appop h (u , v , i , d) = boolΠ refl refl

-- ==================================================================
-- §3  GENERIC: a partiality located at a TUPLE refutes every total
-- point.  Copied from `Heap/Connectives.Generic` (which may not be
-- edited, and whose module opens `RulesF heapFib` publicly, so it cannot
-- be imported here without a name clash).  Placed BEFORE `RulesF` is
-- opened, so that `FibNotation Fib` for an abstract `Fib` does not
-- collide with the leaky heap's own connectives.
-- ==================================================================

module Generic {S : Type₀} {σ : SortedSig S ℓ-zero ℓ-zero}
               (Fib : Fibered σ ℓ-zero ℓ-zero) where

  open FibNotation Fib

  no-tuple-point : (o : σ .ops)
                   (m⃗ : (a : σ .arities o) → Fib .carrier (σ .sortOf o a))
                 → (⊗ˢ o (λ a → ⌈ m⃗ a ⌉) ⊢ ⊥G)
                 → LaxPoint Fib → ⊥
  no-tuple-point o m⃗ k P =
    E.rec* (k (P .op o m⃗)
              ( P .split o m⃗
              , λ a → Eq.pathToEq (funExt⁻ (P .parts-split o m⃗) a) ))

open RulesF leakyFib public

Gr : Type₁
Gr = TheoryTy ℓ-zero tt

-- ==================================================================
-- §4  THE SEPARATING CONJUNCTION AND THE EMPTY HEAP, and the
-- `∗`-interface, written ONCE.
--
-- `Heap/Connectives` writes these for the exact promodel and may not be
-- edited, so they are re-derived here.  Writing them once is the point:
-- every extended lambda over `Bool` would otherwise be a fresh nominal
-- function failing to reduce against the others -- which is exactly the
-- trap `boolΠ` exists to avoid, and `boolΠ` here IS `Heap/Base`'s.
-- ==================================================================

emp : Gr
emp = ⊗ˢ nilop (λ ())

-- `⊗ˢ` at the LEAKY operation.  `(A ∗ B) h` is inhabited when `h` has
-- DISJOINT sub-heaps satisfying `A` and `B` -- and, unlike `Heap`'s,
-- says nothing about the cells of `h` outside them.
_∗_ : Gr → Gr → Gr
A ∗ B = ⊗ˢ appop (boolΠ A B)

infixr 20 _∗_

-- PRIMITIVE (phase 1): intro for `∗`
∗-mk : (A B : Gr) (h u v : Heap) → SubIlv u v h → u # v → A u → B v → (A ∗ B) h
∗-mk A B h u v s d x y =
  ⊗ˢ-I appop {A = boolΠ A B} h (u , v , s , d)
    (boolΠ {M = λ a → boolΠ {M = λ _ → Gr} A B a
                        (leakyFib .parts appop h (u , v , s , d) a)} x y)

-- PRIMITIVE (phase 1): elim for `∗`.  Note it hands back the
-- disjointness as well; `Heap/Connectives` has to project that
-- separately (`split-#`) because `⊛-E'` upstream does not.
∗-E' : (A B : Gr) {C : Gr}
     → ((h u v : Heap) → SubIlv u v h → u # v → A u → B v → C h)
     → (A ∗ B) ⊢ C
∗-E' A B {C} f = ⊗ˢ-E appop {A = boolΠ A B} {B = C}
  (λ h sp k → f h (sp .fst) (sp .snd .fst)
                (sp .snd .snd .fst) (sp .snd .snd .snd) (k true) (k false))

∗-map : {A A' B B' : Gr} → A ⊢ A' → B ⊢ B' → (A ∗ B) ⊢ (A' ∗ B')
∗-map {A} {A'} {B} {B'} f g =
  ⊗ˢ-map appop {A = boolΠ A B} {B = boolΠ A' B'}
    (boolΠ {M = λ a → boolΠ {M = λ _ → Gr} A  B  a
                    ⊢ boolΠ {M = λ _ → Gr} A' B' a} f g)

-- the unit, as a payload.  `MonAr nilop` is `⊥`, so `emp h` really is
-- `IsNil h` with a vacuous slot family attached.
emp-mk : {h : Heap} → IsNil h → emp h        -- PRIMITIVE
emp-mk e = e , λ ()

emp-IsNil : {h : Heap} → emp h → IsNil h
emp-IsNil = fst

-- ==================================================================
-- §5  THE GRADING.  QUESTION 1, ANSWERED.
--
-- The degree is still the cell count.  The additivity EQUATION of
-- `Heap/Graded` degrades to an INEQUALITY -- and the equation is not
-- merely unproved but REFUTED -- and that is exactly enough.
-- ==================================================================

-- what `Ilv` gives, and `cellFib` keeps: the EQUATION.  (`Heap/Graded`
-- states the two one-sided halves; this is the sharp form, and it is
-- proved here so that the first and third columns of the table have a
-- theorem of their own rather than a citation.)
ilvLen≡ : ∀ {u v w} → Ilv u v w → length u + length v ≡ length w
ilvLen≡ nil                        = refl
ilvLen≡ (left s)                   = cong suc (ilvLen≡ s)
ilvLen≡ (right {u = u} {v = v} s)  =
  +-suc (length u) (length v) ∙ cong suc (ilvLen≡ s)

-- PRIMITIVE (phase 1): THE REPLACEMENT.  `leak` is the one clause where
-- the two sides genuinely differ, and it is exactly the clause that
-- turns the equation into an inequality: the whole gained a cell that no
-- part has.  Compare `Affine/Base.liveSplit≤`, clause for clause.
subIlvLen≤ : ∀ {u v w} → SubIlv u v w → length u + length v ≤ length w
subIlvLen≤ snil                       = ≤-refl
subIlvLen≤ (sleft s)                  = suc-≤-suc (subIlvLen≤ s)
subIlvLen≤ (sright {u = u} {v = v} {w = w} s) =
  subst (_≤ suc (length w)) (sym (+-suc (length u) (length v)))
        (suc-≤-suc (subIlvLen≤ s))
subIlvLen≤ (leak s)                   = ≤-suc (subIlvLen≤ s)   -- <-- THE LOSSY CLAUSE

-- ... and the equation really is gone.  One-line witness: a single cell
-- splits leakily into nothing at all.
noSubIlvLen≡ : ((u v w : Heap) → SubIlv u v w → length u + length v ≡ length w) → ⊥
noSubIlvLen≡ f = znots (f [] [] (single 0 v0) (leak snil))

private
  weak : (a b : ℕ) → a ≤ a + b
  weak a b = b , +-comm b a

  strict : (a b : ℕ) → 0 < b → a < a + b
  strict a zero    p = E.rec (¬-<-zero p)
  strict a (suc b) _ = subst (suc a ≤_) (sym (+-suc a b)) (suc-≤-suc (weak a b))

leakyGrading : Grading leakyFib
leakyGrading .deg _ = length

-- `Proper` says the SIBLING is nonempty -- the phrasing every instance
-- uses, and the one that dodges needing `Discrete (arities o)`.
leakyGrading .Proper nilop h sp ()
leakyGrading .Proper appop h (u , v , _) b = 0 < length (boolΠ {M = λ _ → Heap} v u b)

-- `deg≤`:  length slot ≤ length slot + length sibling ≤ length whole.
-- ONLY THE SECOND STEP CHANGED, and it changed from `≡` to `≤`.
leakyGrading .deg≤ nilop h sp ()
leakyGrading .deg≤ appop h (u , v , s , _) =
  boolΠ {M = λ a → length (boolΠ {M = λ _ → Heap} u v a) ≤ length h}
        (≤-trans (weak (length u) (length v)) (subIlvLen≤ s))
        (≤-trans (subst (length v ≤_) (+-comm (length v) (length u))
                        (weak (length v) (length u)))
                 (subIlvLen≤ s))

-- `deg<`: a nonempty sibling makes the first step strict, and the
-- inequality carries it the rest of the way.
leakyGrading .deg< nilop h sp ()
leakyGrading .deg< appop h (u , v , s , _) =
  boolΠ {M = λ a → 0 < length (boolΠ {M = λ _ → Heap} v u a)
                 → length (boolΠ {M = λ _ → Heap} u v a) < length h}
        (λ pr → <≤-trans (strict (length u) (length v) pr) (subIlvLen≤ s))
        (λ pr → <≤-trans
                  (subst (length v <_) (+-comm (length v) (length u))
                         (strict (length v) (length u) pr))
                  (subIlvLen≤ s))

-- ... bundled, so `Ind` / `Guard` / `hyloC` / `löb` apply over the
-- LEAKY promodel too.  Recursion does not notice the leak: it only ever
-- asked that slots not GROW.
leakyGraded : GradedFib monoidSig ℓ-zero ℓ-zero
leakyGraded = graded leakyFib leakyGrading

-- ==================================================================
-- §6  THE FRAME RULE.  QUESTION 2, ANSWERED: IT SURVIVES, AND IT WAS
-- NEVER GOING TO DO ANYTHING ELSE.
--
-- `Heap/Connectives` builds it as `⊗ˢ-map`, and `⊗ˢ-map` is
--
--     ⊗ˢ-map f m (sp , h) = sp , λ a → f a _ (h a)
--
-- -- generic in `Fib`, and it PASSES THE SPLITTING THROUGH UNTOUCHED.
-- The frame rule is the functoriality of `⊗ˢ` in its slot arguments;
-- functoriality is a statement about the PAYLOADS at a fixed splitting,
-- and says nothing whatever about which splittings exist.  So it is
-- insensitive to every change of `Split`, which is worth stating
-- honestly in both directions:
--
--   * it is why the frame rule is free here, and free at `cellFib`, and
--     free at any relaxation anyone cares to write;
--   * it is therefore also why "the frame rule holds" carries NO
--     information about a promodel.  The content of separation logic is
--     never in `⊗ˢ-map`; it is in `Split`, i.e. in §7's refutation and
--     in the unit law of `Intuitionistic.agda`.
--
-- Phase 2: `⊗ˢ-map` and `boolΠ`, nothing else.
-- ==================================================================

frame : {A B : Gr} (C : Gr) → A ⊢ B → (A ∗ C) ⊢ (B ∗ C)
frame {A} {B} C f = ∗-map {A} {B} {C} {C} f idg

frameL : {A B : Gr} (C : Gr) → A ⊢ B → (C ∗ A) ⊢ (C ∗ B)
frameL {A} {B} C f = ∗-map {C} {C} {A} {B} idg f

-- ==================================================================
-- §7  STILL NO LAX POINT.  QUESTION 4, ANSWERED.
--
-- Everything here is `Heap/Connectives.apart-self`/`noHeapPoint` with
-- `heapFib` replaced by `leakyFib`, and the reason it goes through
-- unedited is exactly the reason the axes are different: the refutation
-- reads the `u # v` conjunct and NOTHING ELSE, and that conjunct is what
-- `leak` did not touch.  Leaking is a way to lose a cell, not to share
-- one, so it cannot help a total point exist.
--
-- The honest reading of the cost, then: the leak buys weakening and pays
-- for it with the unit law, NOT with the point.  `cellFib` pays the
-- other way round.
-- ==================================================================

-- PRIMITIVE (phase 1): a splitting entails disjointness of its parts.
split-# : (h : Heap) (sp : leakyFib .Split appop h)
        → leakyFib .parts appop h sp true # leakyFib .parts appop h sp false
split-# h (u , v , _ , d) = d

-- THEOREM (phase 2): `⊗ˢ-E` supplies the splitting and the two
-- representable payloads; `#-Eq` moves disjointness onto them; `#-self`
-- refutes it.  All three are primitives of `Heap/Base`.
apart-self : (l : Loc) (x : Val)
           → (⌈ single l x ⌉ ∗ ⌈ single l x ⌉) ⊢ ⊥G
apart-self l x =
  ⊗ˢ-E appop {A = boolΠ ⌈ single l x ⌉ ⌈ single l x ⌉}
       (λ h sp k → E.rec (#-self l x (#-Eq (k true) (k false) (split-# h sp))))

-- pure coercion between two spellings of one family; see
-- `Heap/Connectives.respell` for why it cannot be `idg`
respell : {u v : Heap} (a : Bool) → ⌈ boolΠ u v a ⌉ ⊢ boolΠ ⌈ u ⌉ ⌈ v ⌉ a
respell {u} {v} = boolΠ {M = λ a → ⌈ boolΠ u v a ⌉ ⊢ boolΠ ⌈ u ⌉ ⌈ v ⌉ a} idg idg

noLeakyPoint : LaxPoint leakyFib → ⊥
noLeakyPoint =
  Generic.no-tuple-point leakyFib appop (boolΠ s s)
    ( apart-self 0 v0
    ∘g ⊗ˢ-map appop {A = λ a → ⌈ boolΠ s s a ⌉}
                    {B = boolΠ ⌈ s ⌉ ⌈ s ⌉} respell )
  where s = single 0 v0

-- ==================================================================
-- §8  THE THIRD COLUMN, so the table is backed and not merely asserted:
-- `cellFib`, `Heap/Base`'s OTHER relaxation, along the DISJOINTNESS
-- axis.
--
-- It keeps `Ilv`, so the unit law is available and the additivity
-- equation is `ilvLen≡` unchanged; and it has a lax point,
-- `Heap/Base.cellPoint`.  What it loses is `apart-self`: two parts may
-- claim the same cell, which is precisely what `_#_` forbade.  So the
-- two relaxations move DISJOINT cells of the table, and neither is a
-- special case of the other.
--
-- Kept as a qualified submodule (`module C = RulesF cellFib`) so that
-- opening it does not shadow the leaky connectives above.
-- ==================================================================

module Cell where

  private module C = RulesF cellFib

  Grᶜ : Type₁
  Grᶜ = C.TheoryTy ℓ-zero tt

  empᶜ : Grᶜ
  empᶜ = C.⊗ˢ nilop (λ ())

  _∗ᶜ_ : Grᶜ → Grᶜ → Grᶜ
  A ∗ᶜ B = C.⊗ˢ appop (boolΠ A B)

  -- `Ilv u v w` with `v` nil is `u ≡ w` on the nose -- the fact `leak`
  -- destroys, and the whole reason the unit law splits the columns.
  ilv-nilM : ∀ {u v w} → Ilv u v w → IsNil v → Ilv u [] w
  ilv-nilM nil       e = nil
  ilv-nilM (left s)  e = left (ilv-nilM s e)
  ilv-nilM (right s) e = E.rec e

  -- THE RIGHT UNIT LAW, WITHOUT DISJOINTNESS.  Compare `no-∗-unitR` in
  -- `Intuitionistic.agda`: deleting `u # v` costs nothing here, weakening
  -- `Ilv` costs everything.
  ∗ᶜ-empR : (A : Grᶜ) → (A ∗ᶜ empᶜ) C.⊢ A
  ∗ᶜ-empR A h ((u , v , i) , k) =
    coeEq A (ilv-nilR-inv (ilv-nilM i (k false .fst))) (k true)

  -- ... and the point that `heapFib` and `leakyFib` both refute.
  cellHasPoint : LaxPoint cellFib
  cellHasPoint = cellPoint
