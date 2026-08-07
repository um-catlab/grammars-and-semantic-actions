{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  DYNAMIC PROGRAMMING, FROM LÖB.

  `Later.WFLater` says a recurrence over a well-founded order has a
  solution (`löb`) and that the solution is UNIQUE (`löb-unique`).  This
  file adds the one thing tabulation needs on top of that -- the
  dependencies of a subproblem must be finitely LISTED -- and derives the
  table.

  The division of labour, and it is the point of the file:

      löb          the recurrence has a solution
      löb-unique   ... and nothing else solves it
      Table        the answers so far, as DATA rather than as a function
      correct      so any tabulation that satisfies the recurrence
                   IS `löb step`, by one appeal to uniqueness

  That last line is what "DP follows from Löb" actually buys.  The memo
  table is ordinary data and nothing about it is deep; what is not free
  is knowing that the fast implementation computes the specified thing,
  and uniqueness of the fixed point delivers exactly that, generically,
  for every recurrence at once.  Optimising stops being a
  reimplementation and becomes a one-line proof obligation.

  WHY THE TABLE CANNOT BE A `▷`.

      ▷ A i = (j : I) → j ≺ i → A j

  is already "the answers at every earlier subproblem" -- the chart, as a
  type.  But it is a Π, and a Π is a function: Agda shares nothing across
  distinct applications, so every consultation recomputes.  `Table`
  below is the same information as a nested `×`, which is data, forced
  once and projected many times.  Tabulation is therefore not a change of
  TYPE but a change of REPRESENTATIVE -- `Π` over a finite index versus a
  finite product -- and the two are isomorphic, which is precisely why
  the type theory cannot tell you which one you have.  See the measured
  blow-up in `Instances/Spans/Bench.agda`.

  WHY A ℕ-DEGREE WILL NOT DO.  `Graded`'s order is `deg i < deg j`
  pulled back from ℕ, and it is NOT finitary: at spans `deg (i , n) = n`,
  so the subproblems below `(i , 20)` are all spans of length < 20 at
  EVERY start position -- infinitely many.  A measure makes
  well-foundedness cheap and tabulation impossible.  DP must be built on
  the ORDER, which is why `WFLater` is generic in `_≺_` and why `Graded`
  is one instance of it rather than the base.

  The right order is NOT a per-theory invention.  `DPGraded._≺ᵖ_` below
  reads it off `Split`/`parts`/`Proper`: "v is a proper slot of some
  splitting of w".  At spans that IS the subspan relation, but no span
  ever has to say so.

  WHY THERE ARE TWO TABLES IN THIS FILE.

      Table / Chain / build / build-correct       spine is a List
      QTable / ChainQ / buildQ / buildQ-correct   spine is a DP.Seq

  and the second is the one to use.  A `List` spine addresses its `d`th
  cell by `there^d here` and there is no other path to it, so a
  consultation costs `O(d)` to BUILD the address and `O(d)` to WALK it.
  Both halves are real -- `DPTests` measures each on its own, and each
  alone already accounts for the whole running time -- so neither can be
  repaired without the other, and what has to change is the SPINE.
  `DP.Seq` reassociates it into a tree of concatenations; an address
  becomes a PATH, and at a balanced schedule both halves are
  `O(log n)`.  On the deep recurrence in `DPTests` that is quadratic
  against flat: 17.9s against 0.2s at 4096 cells, net of start-up, and
  the tree spine still runs 131073 cells in 5.6s.

  The two share `Step`, `löb`, `löb-unfold` and the shape of the
  correctness proof, and they are both kept: the list version is the
  legible statement of what a memo table is, and having both is what
  makes the cost model a measurement rather than a claim.
-}
module TheoryGrammar.DP where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Induction.WellFounded

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Graded
open import TheoryGrammar.Later
open import TheoryGrammar.Enumerable
open import TheoryGrammar.DP.Seq

private variable ℓS ℓ ℓ' ℓX ℓP ℓI ℓR ℓM : Level

module DP {I : Type ℓI} (_≺_ : I → I → Type ℓR) (≺-wf : WellFounded _≺_)
          (A : I → Type ℓM) where

  open WFLater _≺_ ≺-wf public

  -- ================================================================
  -- THE RECURRENCE, as a type.  A dynamic programming problem IS a
  -- term of this type: "solve me, given solutions to my dependencies".
  -- Nothing else about the problem has to be said.
  -- ================================================================

  Step : Type (ℓ-max ℓI (ℓ-max ℓR ℓM))
  Step = (i : I) → ▷ A i → A i

  -- ... and `löb : Step → (i : I) → A i` is its solution, `löb-unique`
  -- says it is the only one.  Both are inherited from `WFLater`.

  -- ================================================================
  -- THE TABLE.  `AllYes'` (Enumerable) is a nested `×` -- DATA, forced
  -- once and projected many times -- over a list of subproblems.  This
  -- is the only difference from `▷`, and it is the whole of DP.
  --
  -- THIS ONE IS THE SPECIFICATION, NOT THE IMPLEMENTATION.  Everything
  -- from here to `correct` is the list-spined table, and its access is
  -- `O(offset)` -- see the cost model on `untab`.  `QTable`/`ChainQ`/
  -- `buildQ` further down are the same construction over `DP.Seq`'s
  -- tree spine, `O(log n)` per access, with the identical correctness
  -- theorem; new instances should use those.  The list version is kept
  -- because it is the readable one, and because the two together are
  -- what makes the cost model measurable rather than asserted.
  -- ================================================================

  Table : List I → Type (ℓ-max ℓI ℓM)
  Table = AllYes' A

  -- A table that covers everything below `i` serves the `later` at `i`.
  -- This is the coercion from data back to the Π, and it is where the
  -- sharing is cashed in: `tbl` is ONE value, and every consultation
  -- projects it instead of recomputing.
  --
  -- COST MODEL, and it is the one number an instance has to care about.
  -- `cov j q` is an ADDRESS -- `there^d here` for an offset `d` -- so a
  -- consultation costs `O(d)` to build and `O(d)` to walk, and both
  -- halves are real (measured in `DPTests`).  What an instance controls
  -- is `d`, and it controls it through the ORDER: if `_≺_` is an
  -- inductive family whose proof already carries the offset, `cov` is a
  -- rename and the cost is whatever the recurrence's own reach is.  If
  -- `_≺_` is a Σ of equations -- `Cubical.Data.Nat.Order._<_`, say --
  -- `cov` has to rediscover the offset by counting, which costs `O(i)`
  -- at EVERY edge no matter how near the dependency is, and the table
  -- goes quadratic.  `_≺ᵖ_` below is a family for this reason and not
  -- only for the transport-freeness.
  --
  -- ... AND THE ORDER IS ONLY HALF OF IT.  A sharp order makes the
  -- `≺`-proof `O(1)`; `there^d here` is still `O(d)` to build and
  -- `O(d)` to walk, so a recurrence with a DEEP edge -- a long span
  -- consulting a short one, which is what a chart is -- is quadratic
  -- however sharp the order is.  Measured, both ways round, in
  -- `DPTests`.  The fix is `untabQ` below: the spine branches and the
  -- address becomes a path.
  untab : {i : I} (is : List I) → ((j : I) → j ≺ i → j ∈L is)
        → Table is → ▷ A i
  untab is cov tbl j q = lookupYes' is j (cov j q) tbl

  -- ================================================================
  -- ONE ROW.  Extend a table to a further batch of subproblems, all of
  -- whose dependencies the table already covers.
  --
  -- `tbl` is bound ONCE and shared by every entry of the row -- which is
  -- the entire content of "dynamic programming".  Compare `löb`, where
  -- the corresponding argument is a function and each entry rebuilds its
  -- own copy of everything beneath it.
  -- ================================================================

  row : Step → (is : List I) → Table is
      → (js : List I) → ((j : I) → j ∈L js → (k : I) → k ≺ j → k ∈L is)
      → Table js
  row st is tbl []       cov = tt*
  row st is tbl (j ∷ js) cov =
      st j (untab is (cov j here) tbl)
    , row st is tbl js (λ j' p → cov j' (there p))

  -- ... and rows compose, so a schedule is a list of batches
  append : (is js : List I) → Table is → Table js → Table (is ++ js)
  append []       js tt*       t = t
  append (i ∷ is) js (a , t) u = a , append is js t u

  -- ================================================================
  -- THE SCHEDULE, with its invariant IN THE TYPE.
  --
  -- A `Chain is` is an enumeration of subproblems in which every
  -- element's dependencies appear LATER in the list -- so the table for
  -- the tail can be built first and every new entry merely projects it.
  -- Carrying the invariant as an index is what makes `build` below
  -- total with no side conditions: the covering proof is right there in
  -- the constructor.
  -- ================================================================

  data Chain : List I → Type (ℓ-max ℓI ℓR) where
    nil  : Chain []
    cons : {is : List I} (i : I) → ((k : I) → k ≺ i → k ∈L is)
         → Chain is → Chain (i ∷ is)

  -- ================================================================
  -- BUILDING A SCHEDULE, ONE BATCH AT A TIME.
  --
  -- `chainOf` prepends a whole batch to an existing chain, given only
  -- that every dependency of every member of the batch already lies in
  -- that chain.  Members of the batch may not depend on each other --
  -- which is exactly what "a level of the chart" means, and why a CYK
  -- row is a batch: all spans of length k depend only on shorter ones.
  --
  -- So a schedule is built by folding this over the levels, shortest
  -- first, and the only thing an instance has to prove is the batch
  -- hypothesis -- never anything about `Chain` itself.
  -- ================================================================

  chainOf : (bs rest : List I) → Chain rest
          → ((i : I) → i ∈L bs → (k : I) → k ≺ i → k ∈L rest)
          → Chain (bs ++ rest)
  chainOf []       rest ch cov = ch
  chainOf (i ∷ bs) rest ch cov =
    cons i (λ k q → ∈++ʳ bs (cov i here k q))
           (chainOf bs rest ch λ j p → cov j (there p))

  -- ================================================================
  -- THE TABULATED FIXED POINT.
  --
  -- `share` takes the tail's table as an ARGUMENT, so it is evaluated
  -- once and both its uses -- serving `untab` and being re-emitted as
  -- the tail of the result -- project the same value.  That single
  -- binding is the difference between this and `löb`, and it is the
  -- difference between cubic and exponential.
  -- ================================================================

  private
    share : (st : Step) {is : List I} (i : I)
          → ((k : I) → k ≺ i → k ∈L is)
          → Table is → Table (i ∷ is)
    share st i cov t = st i (untab _ cov t) , t

  build : Step → {is : List I} → Chain is → Table is
  build st nil            = tt*
  build st (cons i cov ch) = share st i cov (build st ch)

  -- ... and reading the answer off the schedule
  solveAt : Step → {is : List I} → Chain is → (i : I) → i ∈L is → A i
  solveAt st {is} ch i p = lookupYes' is i p (build st ch)

  -- ================================================================
  -- ... AND IT IS THE RIGHT ANSWER.
  --
  -- Four lines, and the middle two are the whole argument: at the head
  -- of the chain the table's entry is `st j` applied to the tail's
  -- table, `löb-unfold` says `löb st j` is `st j` applied to `löb`, and
  -- the induction hypothesis identifies the two arguments pointwise.
  --
  -- So a tabulated implementation is not a second definition to be
  -- trusted alongside the specification -- it is PROVED equal to it,
  -- once, generically, for every recurrence over every well-founded
  -- order at once.  That is what the Löb principle buys here, and it is
  -- the reason `Later.löb-unfold` / `löb-unique` are worth having.
  -- ================================================================

  build-correct : (st : Step) {is : List I} (ch : Chain is)
                  (i : I) (p : i ∈L is)
                → lookupYes' is i p (build st ch) ≡ löb st i
  build-correct st nil i ()
  build-correct st (cons j cov ch) .j here =
      cong (st j) (funExt λ k → funExt λ q → build-correct st ch k (cov k q))
    ∙ sym (löb-unfold st j)
  build-correct st (cons j cov ch) i (there p) = build-correct st ch i p

  solveAt≡ : (st : Step) {is : List I} (ch : Chain is) (i : I) (p : i ∈L is)
           → solveAt st ch i p ≡ löb st i
  solveAt≡ = build-correct

  -- ================================================================
  -- CORRECTNESS, and it is one line.
  --
  -- Whatever schedule an instance uses, whatever order it fills the
  -- table in, it need only show its result satisfies the recurrence.
  -- That it computes THE answer -- the one `löb` specifies -- is then
  -- `löb-unique`.  This is the theorem the whole file exists for.
  -- ================================================================

  correct : (st : Step) (f : (i : I) → A i)
          → ((i : I) → f i ≡ st i (λ j _ → f j))
          → (i : I) → f i ≡ löb st i
  correct = löb-unique

  -- ================================================================
  -- ================================================================
  -- THE SAME THING WITH A TREE SPINE -- AND IT IS THE ONE TO USE.
  --
  -- Everything above is correct and, at a DEEP recurrence, quadratic.
  -- The cost model note on `untab` says why: the address is `there^d
  -- here`, so a consultation at offset `d` costs `O(d)` to BUILD and
  -- `O(d)` to WALK.  Measured (`DPTests`), each half alone is already
  -- as expensive as the whole run, so neither is fixable on its own --
  -- what has to change is the SPINE, because a list has exactly one
  -- path to its `d`th cell and it has length `d`.
  --
  -- `DP.Seq` reassociates the spine into a tree (`Seq`, `Tab`, `_∈Q_`)
  -- and the address becomes a PATH: at a balanced schedule, `O(log n)`
  -- to build and `O(log n)` to walk, both halves together.  Nothing
  -- else about the development moves -- `Step` is the same type, `löb`
  -- is the same solution, and `buildQ-correct` below is the same four
  -- lines of proof.
  --
  -- THE ONE DEFINITIONAL FACT THAT MAKES IT WORK is
  --
  --     Tab A (s ⋈ t) = Tab A s × Tab A t
  --
  -- so extending a table by a batch is PAIRING: `O(1)`, and it
  -- re-indexes nothing already in the table.  With the list spine the
  -- corresponding move is `++`, and `++` on the index is exactly the
  -- `subst` that `CLAUDE.md`'s third trap warns about.  That is the
  -- whole reason the spine is a tree of concatenations rather than a
  -- random-access list addressed by a number.
  -- ================================================================

  QTable : Seq I → Type ℓM
  QTable = Tab A

  -- `untab`, at the tree spine.  Same three words -- look the address
  -- up in the table -- except that `cov k q` is now a PATH, so this is
  -- `O(log n)` on both sides of the composition instead of `O(offset)`
  -- on both.
  untabQ : {i : I} (c : Seq I) → ((k : I) → k ≺ i → k ∈Q c)
         → QTable c → ▷ A i
  untabQ c cov tb k q = lookupQ (cov k q) tb

  -- ================================================================
  -- THE SCHEDULE, WITH ITS CONTEXT IN THE TYPE.
  --
  -- `ChainQ s c` reads: `s` is a block of subproblems, laid out
  -- left-to-right in the order they will be READ, and every member's
  -- dependencies lie either further right inside `s` or anywhere in the
  -- already-solved CONTEXT `c`.  `Chain is` is the case `c = εQ`: at a
  -- list the context could stay implicit, because a list has only one
  -- way to be a suffix of itself and `cons` could just name it.
  --
  -- Carrying `c` explicitly is what lets the spine branch.  At `qapp`
  -- the right half `t` is solved against `c`, and then the left half
  -- `s` is solved against `t ⋈ c` -- a context ONE PAIRING bigger, not
  -- a context that has been rebuilt.  Nesting `qapp` `d` deep therefore
  -- costs `d` extra `rQ`s on an address, and `d` is the schedule's
  -- DEPTH: `O(log n)` when balanced, and the old `O(n)` exactly when
  -- the schedule is a right-nested comb, i.e. a list.
  -- ================================================================

  data ChainQ : Seq I → Seq I → Type (ℓ-max ℓI ℓR) where
    qnil : {c : Seq I} → ChainQ εQ c
    qone : {c : Seq I} (i : I) → ((k : I) → k ≺ i → k ∈Q c)
         → ChainQ (oneQ i) c
    qapp : {s t c : Seq I} → ChainQ t c → ChainQ s (t ⋈ c)
         → ChainQ (s ⋈ t) c

  -- ================================================================
  -- THE TABULATED FIXED POINT, AGAIN.
  --
  -- `shareQ` is `share`'s job at the branching spine: the right half's
  -- table is a lambda-bound ARGUMENT, so it is forced once and its two
  -- uses -- serving the left half's context and being re-emitted as the
  -- right component of the answer -- project the same value.  Take that
  -- binding away and the table is rebuilt at every level, which is the
  -- difference between this and `löb`.
  -- ================================================================

  buildQ  : Step → {s c : Seq I} → ChainQ s c → QTable c → QTable s
  shareQ  : (st : Step) {s t c : Seq I}
          → ChainQ s (t ⋈ c) → QTable c → QTable t → QTable s × QTable t

  buildQ st qnil           tc = tt*
  buildQ st (qone i cov)   tc = st i (untabQ _ cov tc)
  buildQ st (qapp cht chs) tc = shareQ st chs tc (buildQ st cht tc)

  shareQ st chs tc tb = buildQ st chs (tb , tc) , tb

  solveQ : Step → {s : Seq I} → ChainQ s εQ → (i : I) → i ∈Q s → A i
  solveQ st ch i p = lookupQ p (buildQ st ch tt*)

  -- ================================================================
  -- ... AND IT IS STILL THE RIGHT ANSWER.
  --
  -- `GoodQ st s tb` says "every entry of `tb` is what `löb` says it
  -- is".  That is the invariant the branching spine needs and the list
  -- version did not: `buildQ` is given a context table, so the theorem
  -- has to be RELATIVE -- if the context is right then the block is --
  -- and `goodPair` is the one extra line, saying a paired context is
  -- right when both halves are.
  --
  -- The middle case is unchanged from `build-correct`, and it is still
  -- the whole argument: at a leaf the entry is `st i` applied to the
  -- context, `löb-unfold` says `löb st i` is `st i` applied to `löb`,
  -- and the invariant identifies the two arguments pointwise.
  -- ================================================================

  GoodQ : Step → (s : Seq I) → QTable s → Type (ℓ-max ℓI ℓM)
  GoodQ st s tb = (i : I) (p : i ∈Q s) → lookupQ p tb ≡ löb st i

  goodPair : (st : Step) {t c : Seq I} {tb : QTable t} {tc : QTable c}
           → GoodQ st t tb → GoodQ st c tc
           → (i : I) (p : i ∈Q (t ⋈ c)) → lookupQ p (tb , tc) ≡ löb st i
  goodPair st gL gR i (lQ p) = gL i p
  goodPair st gL gR i (rQ p) = gR i p

  buildQ-correct : (st : Step) {s c : Seq I} (ch : ChainQ s c) (tc : QTable c)
                 → GoodQ st c tc
                 → (i : I) (p : i ∈Q s) → lookupQ p (buildQ st ch tc) ≡ löb st i
  buildQ-correct st qnil tc gc i ()
  buildQ-correct st (qone j cov) tc gc .j hereQ =
      cong (st j) (funExt λ k → funExt λ q → gc k (cov k q))
    ∙ sym (löb-unfold st j)
  buildQ-correct st (qapp cht chs) tc gc i (lQ p) =
    buildQ-correct st chs (buildQ st cht tc , tc)
                   (goodPair st (buildQ-correct st cht tc gc) gc) i p
  buildQ-correct st (qapp cht chs) tc gc i (rQ p) =
    buildQ-correct st cht tc gc i p

  solveQ≡ : (st : Step) {s : Seq I} (ch : ChainQ s εQ) (i : I) (p : i ∈Q s)
          → solveQ st ch i p ≡ löb st i
  solveQ≡ st ch = buildQ-correct st ch tt* (λ i ())

  -- ================================================================
  -- BATCHES, WHICH IS WHAT A CHART WANTS.
  --
  -- `batchQ` turns a whole block into a chain in one move, given only
  -- that no member depends on another member -- which is exactly what
  -- "a level of the chart" means, and why a CYK row is a batch: all
  -- spans of length `k` depend only on shorter ones.  It is `chainOf`
  -- with the spine branching, and the layout of `bs` is the caller's
  -- choice: hand it a balanced `Seq` and every cell of the level is
  -- `O(log |bs|)` away.
  --
  -- `levelQ` stacks one batch on a schedule already built.  Stacking
  -- `n` levels with it gives a right-nested comb of levels, so reaching
  -- `d` levels down costs `d`.  A chart that needs better should build
  -- the LEVELS by divide and conquer too -- `qapp` directly, upper half
  -- of the levels against the lower half -- which costs `O(log n)` to
  -- reach any level and needs no new combinator.  That the same
  -- constructor does both is the point of carrying the context.
  -- ================================================================

  batchQ : (bs : Seq I) (c : Seq I)
         → ((i : I) → i ∈Q bs → (k : I) → k ≺ i → k ∈Q c)
         → ChainQ bs c
  batchQ εQ       c cov = qnil
  batchQ (oneQ i) c cov = qone i (cov i hereQ)
  batchQ (s ⋈ t)  c cov =
    qapp (batchQ t c        (λ i p     → cov i (rQ p)))
         (batchQ s (t ⋈ c)  (λ i p k q → rQ (cov i (lQ p) k q)))

  levelQ : {rest : Seq I} (bs : Seq I) {c : Seq I}
         → ChainQ rest c
         → ((i : I) → i ∈Q bs → (k : I) → k ≺ i → k ∈Q (rest ⋈ c))
         → ChainQ (bs ⋈ rest) c
  levelQ bs ch cov = qapp ch (batchQ bs _ cov)

  -- ================================================================
  -- THE HYPOTHESIS AN INSTANCE MUST SUPPLY.
  --
  -- Finitary dependencies -- and NOT a measure.  `depsOk` is what
  -- `untab` consumes; `deps` is what a schedule is built from.
  -- ================================================================

  record Finitary : Type (ℓ-max ℓI ℓR) where
    field
      deps   : I → List I
      depsOk : (i j : I) → j ≺ i → j ∈L deps i

-- ==================================================================
-- THE DEPENDENCY ORDER OF A GRADED THEORY.
--
-- A DP interface is only worth having if the order comes from the
-- theory rather than being invented per instance.  It does: the
-- recursion at a world consults the PROPER SLOTS of its splittings, and
-- nothing else, so
--
--     v ≺ᵖ w   =   v is a proper slot of some splitting of w
--
-- is the dependency relation, read straight off `Split` / `parts` /
-- `Proper`.  Stating it as an inductive FAMILY rather than as a Σ of
-- equations is what keeps it transport-free: the constructor carries
-- the sort and the splitting, so matching on it gives everything back
-- definitionally.
--
-- This retracts a claim I made while designing this: that tabulating
-- spans would need a bespoke `subspan` order plus lemmas that a cut's
-- slots are subspans.  Neither is needed.  The lemmas are the
-- constructor, and the order is generic.
--
-- Well-foundedness is `deg<` and nothing else -- so `Graded`'s measure
-- still earns its keep, it just is not the ORDER.  `Finitary` (above)
-- remains a hypothesis: it is `DecEnumerable` restated, and every
-- instance that can enumerate its splittings can supply it.
-- ==================================================================

module DPGraded {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
                (GS : GradedFib σ ℓX ℓP) where

  private
    Fib : Fibered σ ℓX ℓP
    Fib = GS .fib

  World : Type (ℓ-max ℓS ℓX)
  World = Σ[ s ∈ S ] Fib .carrier s

  degW : World → ℕ
  degW (s , m) = GS .deg s m

  data _≺ᵖ_ : World → World → Type (ℓ-max ℓS (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓX ℓP)))) where
    slot : (o : σ .ops) (m : Fib .carrier (σ .resultSort o))
           (sp : Fib .Split o m) (a : σ .arities o)
         → GS .Proper o m sp a
         → (σ .sortOf o a , Fib .parts o m sp a) ≺ᵖ (σ .resultSort o , m)

  -- a proper slot is strictly smaller -- the ONE fact, and it is `deg<`
  ≺ᵖ-deg : {v w : World} → v ≺ᵖ w → degW v < degW w
  ≺ᵖ-deg (slot o m sp a pr) = GS .deg< o m sp a pr

  ≺ᵖ-wf : WellFounded _≺ᵖ_
  ≺ᵖ-wf w = go (degW w) (<-wellfounded (degW w)) w refl
    where
      go : (n : ℕ) → Acc _<_ n → (v : World) → degW v ≡ n → Acc _≺ᵖ_ v
      go n (acc h) v p =
        acc λ u q → go (degW u)
                       (h (degW u) (subst (degW u <_) p (≺ᵖ-deg q))) u refl

  -- ... and so every graded theory has the DP interface, for free
  module Problem {ℓM : Level} (A : World → Type ℓM) = DP _≺ᵖ_ ≺ᵖ-wf A
