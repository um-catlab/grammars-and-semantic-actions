{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- THE DP MODULE, EXERCISED. A recurrence small enough to check by hand and
   steep enough that the difference between `löb` and `build` is not a
   matter of opinion: Fibonacci over `(ℕ , _≺_)`. fib 0 = 0 fib 1 = 1 fib
   (n+2) = fib (n+1) + fib n Naively this is exponential -- each call
   rebuilds both... -}
module TheoryGrammar.DPTests where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.List
open import Cubical.Induction.WellFounded

open import TheoryGrammar.Enumerable
open import TheoryGrammar.DP.Seq
open import TheoryGrammar.DP

-- THE ORDER.  `k ≺ n` means "k is below n", and the proof is the
-- OFFSET: `≺-here` is "one below", each `≺-there` is one more step.

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

-- The recurrence, as a `Step`.  The `≺` proofs are the dependency
-- edges: `fib (n+2)` may consult `n+1` and `n`, and nothing else --
-- and it says so in `O(1)`, which is what makes the table linear.

fibStep : Step
fibStep zero                _   = 0
fibStep (suc zero)          _   = 1
fibStep (suc (suc n))       rec = rec (suc n) ≺-here + rec n (≺-there ≺-here)

-- The schedule: `down n = [n-1 , … , 0]`, biggest first, so every
-- element's dependencies sit in its tail.  This is `Chain` with the
-- covering proof supplied once.

down : ℕ → List ℕ
down zero    = []
down (suc n) = n ∷ down n

-- The covering function, and it is a RENAME: `≺-here` is `here`, `≺-there`
-- is `there`.
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

-- (1) IT COMPUTES.

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

-- (2) THE TABLE, DUMPED. `Table (down n)` is `AllYes'`, i.e. a nested `×`
-- -- so the chart is an ordinary value and can be checked against a
-- literal.

_ : build fibStep (chainDown 10)
  ≡ (34 , 21 , 13 , 8 , 5 , 3 , 2 , 1 , 1 , 0 , tt*)
_ = refl

_ : build fibStep (chainDown 5) ≡ (3 , 2 , 1 , 1 , 0 , tt*)
_ = refl

_ : build fibStep (chainDown 0) ≡ tt*
_ = refl

-- (3) AND IT IS THE SAME ANSWER. `solveAt≡` is the general theorem; at
-- these points it also holds on the nose, which is the check that the two
-- really are one recurrence.

_ : fibTab 15 ≡ fibNaive 15
_ = refl

_ : (n : ℕ) (p : n ∈L down (suc n))
  → solveAt fibStep (chainDown (suc n)) n p ≡ löb fibStep n
_ = λ n p → solveAt≡ fibStep (chainDown (suc n)) n p

-- THE COST MODEL, MEASURED. Fibonacci's own numbers grow too fast to time
-- a big table with, so the sweep below uses a recurrence with Fibonacci's
-- DEPENDENCY SHAPE and no arithmetic: every cell is `0`, both edges are
-- still forced.

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

{- Elapsed for `flatTab N ≡ 0`, whole-file `agda` invocation, with the
   Σ-of-equations order (`ltOrEq`, the old `∈down`) against the inductive
   order above. -}

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

{- cells deepTab flatTab 200 1.08s 1.10s 400 1.11s 1.15s 800 1.57s -- 1600
   3.28s -- 3200 10.75s 1.18s (at 4000) Quadratic, against a flat column
   that does not move. -}

-- THE TREE SPINE. Same recurrence, same theorem, `O(log n)` per access.

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
  -- `DP` is instantiated at a SECOND order in this file, so it is aliased
  -- rather than opened: the unqualified `Step`, `löb`, `solveQ` already
  -- mean the ones at `_≺_`.
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

  -- THE SCHEDULE, LAID OUT BALANCED. `blk d lo` is a perfect block of
  -- `2^d` cells, read left to right as `top d lo` down to `lo`.

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

  -- THE CHAIN. Divide and conquer, and the covering proofs are THREADED
  -- rather than searched for: a block is entered knowing the address of
  -- the cell just below it (`pM`) and of cell `0` (`pZ`), and hands its
  -- two halves the same two facts.

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

-- (1) THE CHART IS THE TREE. `Tab` over `((c₄ ⋈ c₃) ⋈ (c₂ ⋈ c₁)) ⋈ c₀` is
-- that same tree of pairs, and with `cnt` the cell values are their own
-- indices -- so the dump below reads left to right as cells 4,3,2,1,0.

_ : Deep.buildQ Deep.cnt (Deep.sched 2) tt*
  ≡ (((4 , 3) , (2 , 1)) , 0)
_ = refl

_ : Deep.solve Deep.cnt 0 ≡ 1
_ = refl
_ : Deep.solve Deep.cnt 4 ≡ 16
_ = refl
_ : Deep.solve Deep.step 6 ≡ 0
_ = refl

-- (2) AND IT IS STILL LÖB. `solveQ≡` is the general theorem -- the whole
-- reason the module exists -- and it survives the change of spine
-- unaltered: same statement, same three-line proof by `löb-unfold`.

_ : Deep.solve Deep.cnt 4 ≡ Deep.löb Deep.cnt (Deep.top 4 1)
_ = refl

_ : (d : ℕ) (p : Deep.top d 1 ∈Q (Deep.blk d 1 ⋈ oneQ 0))
  → Deep.solveQ Deep.cnt (Deep.sched d) (Deep.top d 1) p
  ≡ Deep.löb Deep.cnt (Deep.top d 1)
_ = λ d p → Deep.solveQ≡ Deep.cnt (Deep.sched d) (Deep.top d 1) p

-- (3) THE SWEEP.

_ : Deep.solve Deep.step 12 ≡ 0     -- 4097 cells
_ = refl

{- Elapsed for the DEEP recurrence -- cell `n` consults `n-1` and `0` --
   whole-file `agda` invocation. -}

-- BATCHING, WHICH IS WHAT THE NEXT CONSUMER WANTS.

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

{- STACKING MANY LEVELS. `levelQ` alone gives a right-nested comb of levels
   -- `O(d)` to reach `d` levels down -- which is the list problem again,
   one dimension up. -}
