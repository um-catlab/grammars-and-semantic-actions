{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE DP MODULE, EXERCISED.

  A recurrence small enough to check by hand and steep enough that the
  difference between `löb` and `build` is not a matter of opinion:
  Fibonacci over `(ℕ , _≺_)`.

      fib 0 = 0     fib 1 = 1     fib (n+2) = fib (n+1) + fib n

  Naively this is exponential -- each call rebuilds both subtrees --
  and tabulated it is linear.  `DP` gives both from the SAME `Step`,
  and `solveAt≡` proves they agree, so the tests below check the fast
  one and the theorem carries the slow one along.

  What is being demonstrated:
    (1) the recurrence, as a `Step`, computes the right numbers;
    (2) the TABLE is real data -- the dumps below are the chart itself,
        checked entry by entry against a literal tuple;
    (3) `solveAt≡` holds definitionally at these points;
    (4) the runtimes differ by orders of magnitude, and the tabulated
        one is LINEAR in the number of cells (see `THE COST MODEL`).

  ==================================================================
  THE ORDER IS AN INDUCTIVE FAMILY, AND THAT IS THE WHOLE COST MODEL.
  ==================================================================

  The obvious thing to instantiate `DP` with here is
  `Cubical.Data.Nat.Order._<_`, i.e. `Σ[ d ∈ ℕ ] d + suc k ≡ n`.  Do not.
  Tabulation asks each recurrence, at each dependency edge, to say WHERE
  in the schedule the dependency sits -- that is the `cons` field of
  `Chain`, `(k : I) → k ≺ i → k ∈L is` -- and with a Σ-of-equations order
  the only way to answer is to compare `k` against `n` and count down,
  which is `O(min(k,n))` per EDGE.  With `n` cells that is `O(n²)`, and it
  is not a constant factor: measured, a 4000-cell table took 43s.

  As an inductive family the offset IS the proof:

      k ≺ n      is     `there`-free `≺-here`, or one `≺-there` per step

  so `∈down` -- the covering function -- is a rename of the proof, at
  cost `O(n - k)`.  Fibonacci's two edges are `≺-here` and
  `≺-there ≺-here`, hence `O(1)` each, hence a linear table.  Same
  `Step`, same schedule, same theorem; the sweep in `THE COST MODEL`
  below is the difference.

  This is the same lesson `DP`'s own header draws for `_≺ᵖ_`: state the
  dependency relation as a FAMILY whose constructor carries the witness,
  not as a Σ of equations that has to be re-derived at every use.
-}
module TheoryGrammar.DPTests where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.List
open import Cubical.Induction.WellFounded

open import TheoryGrammar.Enumerable
open import TheoryGrammar.DP.Seq
open import TheoryGrammar.DP

-- ==================================================================
-- THE ORDER.  `k ≺ n` means "k is below n", and the proof is the
-- OFFSET: `≺-here` is "one below", each `≺-there` is one more step.
-- ==================================================================

data _≺_ : ℕ → ℕ → Type₀ where
  ≺-here  : {n : ℕ}   → n ≺ suc n
  ≺-there : {m n : ℕ} → m ≺ n → m ≺ suc n

-- well-founded, and by structural recursion on the proof -- no measure
≺-wf : WellFounded _≺_
≺-wf n = acc (go n)
  where go : (n m : ℕ) → m ≺ n → Acc _≺_ m
        go (suc n) .n ≺-here      = acc (go n)
        go (suc n) m  (≺-there q) = go n m q

open DP _≺_ ≺-wf (λ _ → ℕ)

-- ==================================================================
-- The recurrence, as a `Step`.  The `≺` proofs are the dependency
-- edges: `fib (n+2)` may consult `n+1` and `n`, and nothing else --
-- and it says so in `O(1)`, which is what makes the table linear.
-- ==================================================================

fibStep : Step
fibStep zero                _   = 0
fibStep (suc zero)          _   = 1
fibStep (suc (suc n))       rec = rec (suc n) ≺-here + rec n (≺-there ≺-here)

-- ==================================================================
-- The schedule: `down n = [n-1 , … , 0]`, biggest first, so every
-- element's dependencies sit in its tail.  This is `Chain` with the
-- covering proof supplied once.
-- ==================================================================

down : ℕ → List ℕ
down zero    = []
down (suc n) = n ∷ down n

-- The covering function, and it is a RENAME: `≺-here` is `here`,
-- `≺-there` is `there`.  No comparison, no counting, no equality test
-- -- which is exactly why the order was chosen inductive.  An edge of
-- offset `d` costs `d`, so Fibonacci's cost `1`.
∈down : (n k : ℕ) → k ≺ n → k ∈L down n
∈down (suc n) .n ≺-here      = here
∈down (suc n) k  (≺-there q) = there (∈down n k q)

chainDown : (n : ℕ) → Chain (down n)
chainDown zero    = nil
chainDown (suc n) = cons n (∈down n) (chainDown n)

-- the two solutions of the SAME recurrence
fibNaive : ℕ → ℕ
fibNaive = löb fibStep

fibTab : ℕ → ℕ
fibTab n = solveAt fibStep (chainDown (suc n)) n (∈down (suc n) n ≺-here)

-- ==================================================================
-- (1) IT COMPUTES.
-- ==================================================================

_ : fibTab 0 ≡ 0
_ = refl
_ : fibTab 1 ≡ 1
_ = refl
_ : fibTab 7 ≡ 13
_ = refl
_ : fibTab 15 ≡ 610
_ = refl
_ : fibTab 25 ≡ 75025
_ = refl

-- ==================================================================
-- (2) THE TABLE, DUMPED.
--
-- `Table (down n)` is `AllYes'`, i.e. a nested `×` -- so the chart is
-- an ordinary value and can be checked against a literal.  Reading
-- right to left this is fib 0 … fib 9.
-- ==================================================================

_ : build fibStep (chainDown 10)
  ≡ (34 , 21 , 13 , 8 , 5 , 3 , 2 , 1 , 1 , 0 , tt*)
_ = refl

_ : build fibStep (chainDown 5) ≡ (3 , 2 , 1 , 1 , 0 , tt*)
_ = refl

_ : build fibStep (chainDown 0) ≡ tt*
_ = refl

-- ==================================================================
-- (3) AND IT IS THE SAME ANSWER.
--
-- `solveAt≡` is the general theorem; at these points it also holds on
-- the nose, which is the check that the two really are one recurrence.
-- ==================================================================

_ : fibTab 15 ≡ fibNaive 15
_ = refl

_ : (n : ℕ) (p : n ∈L down (suc n))
  → solveAt fibStep (chainDown (suc n)) n p ≡ löb fibStep n
_ = λ n p → solveAt≡ fibStep (chainDown (suc n)) n p

-- ==================================================================
-- THE COST MODEL, MEASURED.
--
-- Fibonacci's own numbers grow too fast to time a big table with, so
-- the sweep below uses a recurrence with Fibonacci's DEPENDENCY SHAPE
-- and no arithmetic: every cell is `0`, both edges are still forced.
-- What is being timed is the DP machinery and nothing else.
-- ==================================================================

flatStep : Step
flatStep zero          _   = 0
flatStep (suc zero)    _   = 0
flatStep (suc (suc n)) rec = rec (suc n) ≺-here + rec n (≺-there ≺-here)

flatTab : ℕ → ℕ
flatTab n = solveAt flatStep (chainDown (suc n)) n (∈down (suc n) n ≺-here)

_ : flatTab 400 ≡ 0
_ = refl
_ : flatTab 4000 ≡ 0
_ = refl

{-
  Elapsed for `flatTab N ≡ 0`, whole-file `agda` invocation, with the
  Σ-of-equations order (`ltOrEq`, the old `∈down`) against the inductive
  order above.  Both columns include ≈1.1s of process start-up.

      cells    Σ-order      ≺-family
         50     1.09s         1.15s
        100     1.12s         1.12s
        200     1.12s         1.10s
        400     1.30s         1.15s
       1000     2.82s         1.15s
       2000     9.91s         1.15s
       4000    44.27s         1.18s
       8000       --          1.23s
      16000       --          1.38s
      32000       --          1.63s
      64000       --          1.90s

  The left column is quadratic in the cell count (×4 per doubling from
  1000 on); the right is linear -- net of start-up, 0.13 / 0.28 / 0.53 /
  0.80 at 8k / 16k / 32k / 64k.

  ==================================================================
  WHAT IS STILL LINEAR PER ACCESS: THE ADDRESS IS UNARY.
  ==================================================================

  `lookupYes'` walks the `∈L` proof, so reading the table at offset `d`
  costs `d`.  Above `d ≤ 1`, so it never shows.  `deepStep` below is the
  recurrence that does show it: every cell consults its predecessor AND
  cell `0`, whose offset from cell `n` is `n`.  That run is quadratic
  (table below), and it is the shape a CYK chart has -- a long span
  consulting a short one is a deep lookup.

  Three measurements say where the cost is, and it is not in
  `lookupYes'` alone:

    * the covering proof ALONE -- build `∈down n 0 …`, i.e. the term
      `there^(n-1) here`, and consume it without ever touching a table
      -- is already as expensive as the whole DP run (8.0s vs 7.8s at
      3200 cells).  The address costs `O(offset)` to PRODUCE.
    * threading the deep address through the chain, so each node's
      covering proof is `O(1)` and only `lookupYes'` is left walking, is
      STILL quadratic (11.9s at 3200 cells).  The address costs
      `O(offset)` to CONSUME.
    * both halves are within a small factor of each other.

  So neither half is fixable on its own: an `O(1)` address that
  `lookupYes'` still walks buys nothing, and a sublinear `lookupYes'`
  applied to an address that took `O(offset)` to build buys nothing
  either.  What has to change is the SPINE, because a list has exactly
  one path to its `d`th cell and that path has length `d`.  `DP.Seq`
  changes it -- see `THE TREE SPINE` at the bottom of this file, where
  the same recurrence at 4096 cells goes from 17.9s to 0.2s net of
  start-up, and both halves move together because a path IS the
  address.
-}

deepBelow : (n : ℕ) → 0 ≺ suc n
deepBelow zero    = ≺-here
deepBelow (suc n) = ≺-there (deepBelow n)

deepStep : Step
deepStep zero          _   = 0
deepStep (suc n)       rec = rec n ≺-here + rec 0 (deepBelow n)

deepTab : ℕ → ℕ
deepTab n = solveAt deepStep (chainDown (suc n)) n (∈down (suc n) n ≺-here)

_ : deepTab 0 ≡ 0
_ = refl
_ : deepTab 200 ≡ 0
_ = refl

{-
      cells    deepTab      flatTab
        200     1.08s        1.10s
        400     1.11s        1.15s
        800     1.57s         --
       1600     3.28s         --
       3200    10.75s        1.18s (at 4000)

  Quadratic, against a flat column that does not move.  The offset, not
  the number of cells, is what is being paid for.
-}

-- ==================================================================
-- ==================================================================
-- THE TREE SPINE.
--
-- Same recurrence, same theorem, `O(log n)` per access.  Two things
-- change and BOTH are necessary -- the sweep at the bottom measures
-- them one at a time, and the first alone buys a constant factor and
-- leaves the curve quadratic:
--
--   (1) the ORDER is sharpened.  `_≺_` above says "anything below",
--       so `0 ≺ n` is a unary distance and `deepStep` pays `O(n)` just
--       to NAME its own dependency.  `_≺ᵈ_` below is the recurrence's
--       actual dependency relation -- predecessor, and zero -- and both
--       edges are one constructor.  This is the lesson the header
--       already drew, applied honestly: an over-approximating order is
--       a cost, not a convenience.
--
--   (2) the SPINE is a tree.  `Chain`/`AllYes'` address the `d`th cell
--       by `there^d here`; `ChainQ`/`Tab` address it by a PATH through
--       `DP.Seq`'s `_⋈_`, which at a balanced schedule has length
--       `O(log n)` -- and the path is `O(log n)` to build as well as to
--       walk, which is what the two controls in `THE COST MODEL` said
--       was required.
-- ==================================================================

data _≺ᵈ_ : ℕ → ℕ → Type₀ where
  ≺ᵈ-pred : {n : ℕ} → n ≺ᵈ suc n
  ≺ᵈ-zero : {n : ℕ} → 0 ≺ᵈ suc n

≺ᵈ-acc0 : Acc _≺ᵈ_ 0
≺ᵈ-acc0 = acc λ m ()

≺ᵈ-wf : WellFounded _≺ᵈ_
≺ᵈ-wf zero    = ≺ᵈ-acc0
≺ᵈ-wf (suc n) = acc go
  where go : (m : ℕ) → m ≺ᵈ suc n → Acc _≺ᵈ_ m
        go .n ≺ᵈ-pred = ≺ᵈ-wf n
        go .0 ≺ᵈ-zero = ≺ᵈ-acc0

module Deep where
  -- `DP` is instantiated at a SECOND order in this file, so it is
  -- aliased rather than opened: the unqualified `Step`, `löb`, `solveQ`
  -- already mean the ones at `_≺_`.  `open D public` at the end of the
  -- module re-exports them under `Deep.`.
  private module D = DP _≺ᵈ_ ≺ᵈ-wf (λ _ → ℕ)

  -- The recurrence.  `deepStep` above, with its two edges named
  -- rather than counted -- and it is the SAME function of `rec`.
  step : D.Step
  step zero    _   = 0
  step (suc n) rec = rec n ≺ᵈ-pred + rec 0 ≺ᵈ-zero

  -- ... and a variant whose answers are all distinct, so that a dump
  -- of the table is a real check: cell `n` holds `1 + cell (n-1)`,
  -- hence `n`.
  cnt : D.Step
  cnt zero    _   = 0
  cnt (suc n) rec = suc (rec n ≺ᵈ-pred) + rec 0 ≺ᵈ-zero

  -- ================================================================
  -- THE SCHEDULE, LAID OUT BALANCED.
  --
  -- `blk d lo` is a perfect block of `2^d` cells, read left to right
  -- as `top d lo` down to `lo`.  Nothing here is generic DP: it is the
  -- instance choosing its own chart layout, which is exactly what
  -- `Seq` leaves open.
  --
  -- The one design constraint is that no ARITHMETIC may appear in an
  -- index -- `lo + 2^d` would not reduce at a variable `lo`, and a
  -- schedule whose type does not reduce needs a `subst` to address.
  -- Hence `top` is defined by the same recursion as `blk` and the left
  -- half starts at `suc (top d lo)`: a manifest successor, so `blk`'s
  -- lowest cell always has a syntactic predecessor to point at.
  -- ================================================================

  top : ℕ → ℕ → ℕ
  top zero    lo = lo
  top (suc d) lo = top d (suc (top d lo))

  blk : ℕ → ℕ → Seq ℕ
  blk zero    lo = oneQ lo
  blk (suc d) lo = blk d (suc (top d lo)) ⋈ blk d lo

  -- the address of a block's HIGHEST cell -- `lQ`-only, so `O(d)`
  blkTop : (d lo : ℕ) → top d lo ∈Q blk d lo
  blkTop zero    lo = hereQ
  blkTop (suc d) lo = lQ (blkTop d (suc (top d lo)))

  -- ================================================================
  -- THE CHAIN.  Divide and conquer, and the covering proofs are
  -- THREADED rather than searched for: a block is entered knowing the
  -- address of the cell just below it (`pM`) and of cell `0` (`pZ`),
  -- and hands its two halves the same two facts.  The right half gets
  -- them unchanged; the left half gets `pM = lQ (blkTop …)` -- the
  -- right half's own top cell, which is by construction its
  -- predecessor -- and `pZ` one `rQ` deeper.
  --
  -- So no edge is ever located by counting or comparing.  Every
  -- covering proof costs `O(log n)`, and so does reading it.
  -- ================================================================

  chain : (d m : ℕ) (c : Seq ℕ) → m ∈Q c → 0 ∈Q c → D.ChainQ (blk d (suc m)) c
  chain zero    m c pM pZ = D.qone (suc m) cov
    where cov : (k : ℕ) → k ≺ᵈ suc m → k ∈Q c
          cov .m ≺ᵈ-pred = pM
          cov .0 ≺ᵈ-zero = pZ
  chain (suc d) m c pM pZ =
    D.qapp (chain d m c pM pZ)
           (chain d (top d (suc m)) (blk d (suc m) ⋈ c)
                  (lQ (blkTop d (suc m))) (rQ pZ))

  -- the whole schedule: cell `0` at the bottom, then `2^d` cells above
  sched : (d : ℕ) → D.ChainQ (blk d 1 ⋈ oneQ 0) εQ
  sched d = D.qapp (D.qone 0 (λ k ()))
                   (chain d 0 (oneQ 0 ⋈ εQ) (lQ hereQ) (lQ hereQ))

  solve : D.Step → (d : ℕ) → ℕ
  solve st d = D.solveQ st (sched d) (top d 1) (lQ (blkTop d 1))

  open D public

-- ==================================================================
-- (1) THE CHART IS THE TREE.
--
-- `Tab` over `((c₄ ⋈ c₃) ⋈ (c₂ ⋈ c₁)) ⋈ c₀` is that same tree of
-- pairs, and with `cnt` the cell values are their own indices -- so
-- the dump below reads left to right as cells 4,3,2,1,0.  This is the
-- `build … ≡ (34 , 21 , …)` test again, at the new spine.
-- ==================================================================

_ : Deep.buildQ Deep.cnt (Deep.sched 2) tt*
  ≡ (((4 , 3) , (2 , 1)) , 0)
_ = refl

_ : Deep.solve Deep.cnt 0 ≡ 1
_ = refl
_ : Deep.solve Deep.cnt 4 ≡ 16
_ = refl
_ : Deep.solve Deep.step 6 ≡ 0
_ = refl

-- ==================================================================
-- (2) AND IT IS STILL LÖB.
--
-- `solveQ≡` is the general theorem -- the whole reason the module
-- exists -- and it survives the change of spine unaltered: same
-- statement, same three-line proof by `löb-unfold`.  At these points
-- it also holds on the nose.
-- ==================================================================

_ : Deep.solve Deep.cnt 4 ≡ Deep.löb Deep.cnt (Deep.top 4 1)
_ = refl

_ : (d : ℕ) (p : Deep.top d 1 ∈Q (Deep.blk d 1 ⋈ oneQ 0))
  → Deep.solveQ Deep.cnt (Deep.sched d) (Deep.top d 1) p
  ≡ Deep.löb Deep.cnt (Deep.top d 1)
_ = λ d p → Deep.solveQ≡ Deep.cnt (Deep.sched d) (Deep.top d 1) p

-- ==================================================================
-- (3) THE SWEEP.
-- ==================================================================

_ : Deep.solve Deep.step 12 ≡ 0     -- 4097 cells
_ = refl

{-
  Elapsed for the DEEP recurrence -- cell `n` consults `n-1` and `0` --
  whole-file `agda` invocation.  Process start-up is 1.03s, measured on
  a file that imports `DP` and does nothing; the second figure in each
  column is net of it.

    cells   A: ≺ + list     B: ≺ᵈ + list    C: ≺ᵈ + Seq
      257    1.18s  0.15     1.25s  0.22     1.13s  0.10
      513    1.32s  0.29     1.39s  0.36     1.10s  0.07
     1025    2.00s  0.97     1.88s  0.85     1.09s  0.06
     2049    5.04s  4.01     3.88s  2.85     1.13s  0.10
     4097   18.91s 17.88     13.12s 12.09    1.23s  0.20

  A is the shipped `deepTab` above.  B sharpens the ORDER only, so the
  `≺`-proof is `O(1)` but the address is still `there^d here`: still
  quadratic, ×4.2 per doubling, and the sharper order bought a constant
  factor of 1.5 and nothing else.  Only C -- order AND spine -- flattens,
  and at 4096 cells it is 90× on the wall clock and 90× net.  This is
  the third measurement in `THE COST MODEL` cashed in: the two halves of
  the address cost had to be paid off together, and B is what paying off
  one of them looks like.

  C continued, past where A can be run at all:

    cells      C
    16385    1.69s  0.66
    32769    2.27s  1.24
    65537    3.82s  2.79
   131073    6.68s  5.65

  Net, that is ×1.9 / ×2.2 / ×2.0 per doubling of the cell count -- a
  little over linear, i.e. `O(n log n)`, which is exactly `n` cells at
  `O(log n)` per access.

  WHERE THE REMAINING LOG GOES, AND WHY IT IS NOT ELIMINABLE HERE.
  Both the covering proof and `lookupQ` walk one path of length `d` =
  the schedule's depth.  A shallower schedule would need a wider
  branching `Seq`, which is a change of layout in the INSTANCE, not in
  `DP`; `Seq` is deliberately unbalanced-by-default for that reason.

  WHERE THE REMAINING LOG GOES.  Both the covering proof and `lookupQ`
  walk one path of length `d` = the schedule's DEPTH.  Making `d`
  smaller means a wider `Seq`, which is a change of layout in the
  INSTANCE, not in `DP` -- and `DP.Seq` leaves layout open for exactly
  that reason.
-}

-- ==================================================================
-- ==================================================================
-- BATCHING, WHICH IS WHAT THE NEXT CONSUMER WANTS.
--
-- `Deep.chain` builds its schedule one cell at a time only because
-- that recurrence is a LINE.  A chart is not: all spans of length `k`
-- depend on shorter spans and NOT on each other, so a whole level goes
-- in at once.  `batchQ`'s hypothesis is exactly "no member of the
-- batch depends on another",
--
--     batchQ : (bs c : Seq I)
--            → ((i : I) → i ∈Q bs → (k : I) → k ≺ i → k ∈Q c)
--            → ChainQ bs c
--
-- and the level's own layout is the caller's `bs`, so a balanced level
-- is `O(log |bs|)` to address.  `levelQ` stacks one level onto a
-- schedule already built.
--
-- The order below is the smallest thing with a level: cell `0`, and
-- then a whole batch of cells each of which consults `0` and nothing
-- else.  It is a smoke test, but it is the one that matters -- it is
-- the CYK wiring in miniature, and `sched` is one `levelQ`.
-- ==================================================================

data _≺ᵇ_ : ℕ → ℕ → Type₀ where
  ≺ᵇ-base : {n : ℕ} → 0 ≺ᵇ suc n

≺ᵇ-acc0 : Acc _≺ᵇ_ 0
≺ᵇ-acc0 = acc λ m ()

≺ᵇ-wf : WellFounded _≺ᵇ_
≺ᵇ-wf zero    = ≺ᵇ-acc0
≺ᵇ-wf (suc n) = acc go
  where go : (m : ℕ) → m ≺ᵇ suc n → Acc _≺ᵇ_ m
        go .0 ≺ᵇ-base = ≺ᵇ-acc0

module Batch where
  private module D = DP _≺ᵇ_ ≺ᵇ-wf (λ _ → ℕ)

  st : D.Step
  st zero    _   = 7
  st (suc n) rec = suc (rec 0 ≺ᵇ-base)

  -- one level, laid out balanced -- three cells that do not see each
  -- other, so `batchQ` may have them in any order it likes
  lvl : Seq ℕ
  lvl = (oneQ 3 ⋈ oneQ 2) ⋈ oneQ 1

  -- ... stacked on the schedule `[0]`.  One `levelQ`, one covering
  -- proof for the whole level, and it is `O(1)` because every edge of
  -- this recurrence points at the same cell.
  cov : (i : ℕ) → i ∈Q lvl → (k : ℕ) → k ≺ᵇ i → k ∈Q (oneQ 0 ⋈ εQ)
  cov i p .0 ≺ᵇ-base = lQ hereQ

  sched : D.ChainQ (lvl ⋈ oneQ 0) εQ
  sched = D.levelQ lvl (D.qone 0 (λ k ())) cov

  open D public

-- the chart: the level's three cells all read `7` and report `8`
_ : Batch.buildQ Batch.st Batch.sched tt* ≡ (((8 , 8) , 8) , 7)
_ = refl

-- ... and it is still löb, by the same theorem, at a batched schedule
_ : (i : ℕ) (p : i ∈Q (Batch.lvl ⋈ oneQ 0))
  → Batch.solveQ Batch.st Batch.sched i p ≡ Batch.löb Batch.st i
_ = Batch.solveQ≡ Batch.st Batch.sched

{-
  STACKING MANY LEVELS.  `levelQ` alone gives a right-nested comb of
  levels -- `O(d)` to reach `d` levels down -- which is the list
  problem again, one dimension up.  The fix needs no new combinator:
  `qapp` takes the LOWER half of the levels and then the UPPER half
  against it, so a chart built by divide and conquer over LENGTHS is
  `O(log n)` in the level direction as well as within a level.

  That the same constructor serves "one cell", "one level" and "half
  the chart" is the point of `ChainQ` carrying its context: extending a
  table is `_⋈_`, i.e. pairing, and pairing never re-indexes what is
  already there.
-}
