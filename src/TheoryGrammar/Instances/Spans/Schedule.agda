{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE SPAN SCHEDULE -- i.e. the CYK chart, as a `DP.Chain`.

  `DP` says a recurrence over a well-founded order is tabulated by a
  `Chain`: an enumeration of subproblems in which every element's
  DEPENDENCIES appear later in the list, so the table for the tail is
  built first and every new entry merely projects it.  This file builds
  that enumeration for the subspans of a root span, and it is the whole
  of "CYK is cubic".

  THE ORDER, and why it is not the textbook one.  The textbook fills the
  chart by increasing LENGTH, in levels; `DP.chainOf` would take each
  level as a batch.  This file instead lays the chart out ROW BY ROW --
  by increasing START, and within a row by decreasing length --

      (i,n) (i,n-1) … (i,0)   (i+1,n-1) … (i+1,0)   …   (i+n,0)

  which is also a valid schedule, for the two reasons that are the
  recurrence:

      the LEFT slot of a cut of `(i,m)` is `(i,l)` with `l < m`
          -- same row, further along it;
      the RIGHT slot is `(i+l,r)` with `l > 0`
          -- a LATER row, hence after the whole of this one.

  and it is the one that keeps ADDRESSES short.  A left consultation
  costs `m - l` steps -- it never leaves the row -- where a level layout
  would charge it the width of every level in between.

  ==================================================================
  WHY THIS FILE IS ALL INDUCTIVE FAMILIES.

  A schedule is only worth building if its addresses COMPUTE.  `∈L` is
  `there^d here`, and `d` is discovered by whatever proves membership --
  so if that proof goes through a `subst`, every consultation carries a
  transport and the chart stops reducing (`CLAUDE.md`'s third trap).

  So the three facts a lookup needs are carried as DATA:

      `l ≼ n`        carries `n - l`, which IS the address inside a row
      `Fits x r n`   carries `x`, which IS the number of rows to skip
      `Start b x j`  carries "the start `j` is `x` places after `b`"

  and each is transported by a rename (`s≼`, `fitW`, `bumpStart`), never
  by an equation.  `cutFits` reads the second straight off a `Cut`,
  which is itself an inductive family over the length -- so the cut a
  decision is scanning already knows where in the chart its slots live.

  THE ONE EQUATION, and it is `Eq`.  `SpanParts` writes the right slot's
  start as `i + l`; the schedule, recursing on the offset, writes it as
  `l + i`.  `_+_` recurses on its FIRST argument, so neither reduces at
  a variable `i` and the two must be identified.  `swapE` does it in
  `Cubical.Data.Equality` -- at a concrete span both sides are the same
  numeral, the proof reduces to `refl`, and `Eq.transport` along `refl`
  is definitionally the identity.  A path would leave a `transp`.
-}
module TheoryGrammar.Instances.Spans.Schedule where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Unit
open import Cubical.Data.List
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Graded
open import TheoryGrammar.Enumerable
open import TheoryGrammar.DP

open import TheoryGrammar.Instances.Spans.Graded
open import TheoryGrammar.Instances.Spans.DP

-- ==================================================================
-- A COUNTING ORDER.  `l ≼ n` is `≤` with the DIFFERENCE as its spine,
-- so it is already the address of `l` in a list that counts down from
-- `n`.  `Cubical.Data.Nat.Order._≤_` is a Σ of an equation and would
-- have to rediscover that number at every use.
-- ==================================================================

data _≼_ (m : ℕ) : ℕ → Type₀ where
  ≼-refl : m ≼ m
  ≼-suc  : {n : ℕ} → m ≼ n → m ≼ suc n

z≼ : (n : ℕ) → 0 ≼ n
z≼ zero    = ≼-refl
z≼ (suc n) = ≼-suc (z≼ n)

s≼ : {m n : ℕ} → m ≼ n → suc m ≼ suc n
s≼ ≼-refl    = ≼-refl
s≼ (≼-suc p) = ≼-suc (s≼ p)

sub1≼ : {a b : ℕ} → suc a ≼ b → a ≼ b
sub1≼ ≼-refl    = ≼-suc ≼-refl
sub1≼ (≼-suc p) = ≼-suc (sub1≼ p)

pred≼ : {a b : ℕ} → suc a ≼ suc b → a ≼ b
pred≼ ≼-refl    = ≼-refl
pred≼ (≼-suc p) = sub1≼ p

-- ==================================================================
-- THE CHART, AS A LIST.  A row is one start position, longest span
-- first; the chart is the rows, leftmost start first.
-- ==================================================================

rowL : ℕ → ℕ → List World
rowL j zero    = (tt , (j , 0)) ∷ []
rowL j (suc n) = (tt , (j , suc n)) ∷ rowL j n

chartL : ℕ → ℕ → List World
chartL i zero    = (tt , (i , 0)) ∷ []
chartL i (suc n) = rowL i (suc n) ++ chartL (suc i) n

hdRow : (j n : ℕ) → (tt , (j , n)) ∈L rowL j n
hdRow j zero    = here
hdRow j (suc n) = here

-- INSIDE A ROW: the address is the length difference, and nothing else.
memRow : (j n l : ℕ) → l ≼ n → (tt , (j , l)) ∈L rowL j n
memRow j .l      l ≼-refl    = hdRow j l
memRow j (suc n) l (≼-suc p) = there (memRow j n l p)

memRowIn : (b n r : ℕ) → r ≼ n → (tt , (b , r)) ∈L chartL b n
memRowIn b zero    r p = memRow b 0 r p
memRowIn b (suc n) r p = ∈++ˡ (memRow b (suc n) r p)

-- ==================================================================
-- WHERE A CUT'S RIGHT SLOT LIVES.
--
-- `Fits x r n` says "a span of length `r` starting `x` places in still
-- ends inside a span of length `n`" -- and `x` is exactly the number of
-- rows to skip.  `cutFits` reads it off the cut: `shift` moves the
-- cut one place right, which is one row further down the chart.  That
-- correspondence is why nothing here has to compute a subtraction.
-- ==================================================================

data Fits : ℕ → ℕ → ℕ → Type₀ where
  fitH : {r n : ℕ} → r ≼ n → Fits zero r n
  fitS : {x r n : ℕ} → Fits x r n → Fits (suc x) r (suc n)

fitW : {x r n : ℕ} → Fits x r n → Fits x r (suc n)
fitW (fitH p) = fitH (≼-suc p)
fitW (fitS q) = fitS (fitW q)

fitWeak : {x r a b : ℕ} → a ≼ b → Fits x r a → Fits x r b
fitWeak ≼-refl    f = f
fitWeak (≼-suc p) f = fitW (fitWeak p f)

cutFits : {n : ℕ} (c : Cut n) → Fits (cutL c) (cutR c) n
cutFits here      = fitH ≼-refl
cutFits (shift c) = fitS (cutFits c)

-- `Start b x j` : the start `j` is `x` places after `b`.  Shifting the
-- base is `bumpStart`, a rename -- which is the whole reason the chart
-- recursion `chartL i (suc n) = … ++ chartL (suc i) n` costs nothing.
data Start (b : ℕ) : ℕ → ℕ → Type₀ where
  st0 : Start b zero b
  stS : {x j : ℕ} → Start b x j → Start b (suc x) (suc j)

bumpStart : {b x j : ℕ} → Start b x j → Start (suc b) x (suc j)
bumpStart st0     = st0
bumpStart (stS s) = stS (bumpStart s)

startOf : (b x : ℕ) → Start b x (x + b)
startOf b zero    = st0
startOf b (suc x) = stS (startOf b x)

memFit : (b : ℕ) {x j r n : ℕ} → Start b x j → Fits x r n
       → (tt , (j , r)) ∈L chartL b n
memFit b st0     (fitH p) = memRowIn b _ _ p
memFit b (stS s) (fitS {n = n} q) =
  ∈++ʳ (rowL b (suc n)) (memFit (suc b) (bumpStart s) q)

-- ==================================================================
-- THE ONE EQUATION.  See the header: `i + l` versus `l + i`, in `Eq`
-- so that the transport vanishes at a concrete span.
-- ==================================================================

+sucE : (a b : ℕ) → (a + suc b) Eq.≡ suc (a + b)
+sucE zero    b = Eq.refl
+sucE (suc a) b = Eq.ap suc (+sucE a b)

+0E : (a : ℕ) → (a + 0) Eq.≡ a
+0E zero    = Eq.refl
+0E (suc a) = Eq.ap suc (+0E a)

+commE : (a b : ℕ) → (a + b) Eq.≡ (b + a)
+commE a zero    = +0E a
+commE a (suc b) = +sucE a b Eq.∙ Eq.ap suc (+commE a b)

swapE : (x i : ℕ) → (x + suc i) Eq.≡ (i + suc x)
swapE x i = +sucE x i Eq.∙ (Eq.ap suc (+commE x i) Eq.∙ Eq.sym (+sucE i x))

memRight : (i : ℕ) {x r n : ℕ} → Fits x r n
         → (tt , (i + suc x , r)) ∈L chartL (suc i) n
memRight i {x} {r} {n} f =
  Eq.transport (λ j → (tt , (j , r)) ∈L chartL (suc i) n) (swapE x i)
               (memFit (suc i) (startOf (suc i) x) f)

-- ==================================================================
-- THE TWO SLOTS OF A CUT, LOCATED.
--
-- Both are read off the cut itself, and both use the resource
-- certificate the recursion already carries: the LEFT slot is shorter
-- because the right one is non-empty, the RIGHT slot is in a later row
-- because the left one is non-empty.  That is `Spans.Graded`'s
-- `SpanProper` and nothing more.
-- ==================================================================

cutL≼ : {n : ℕ} (c : Cut (suc n)) → 0 < cutR c → cutL c ≼ n
cutL≼ {n}     here          q = z≼ n
cutL≼ {zero}  (shift here)  q = E.rec (¬-<-zero q)
cutL≼ {suc n} (shift c)     q = s≼ (cutL≼ c q)

covRight : (i n : ℕ) {m : ℕ} (c : Cut m) → 0 < cutL c → m ≼ suc n
         → (tt , (i + cutL c , cutR c)) ∈L chartL (suc i) n
covRight i n here      q p = E.rec (¬-<-zero q)
covRight i n (shift c) q p = memRight i (fitWeak (pred≼ p) (cutFits c))

-- ==================================================================
-- ... AND THE CHAIN.
--
-- `Chain` carries the covering invariant as an index, so building the
-- schedule IS proving it: each `cons` names the span and hands over the
-- proof that its dependencies are already in the tail.  Nothing about
-- well-foundedness is re-argued -- `DP` has it -- and nothing about
-- correctness is argued at all, since `DP.solveAt≡` gives it.
-- ==================================================================

module _ {ℓM : Level} (A : World → Type ℓM) where
  open Problem A

  -- one row, prepended to a chain that already covers its RIGHT slots
  chainRow : (i m : ℕ) {rest : List World}
           → ((m' : ℕ) → m' ≼ m → (c : Cut m') → 0 < cutL c
              → (tt , (i + cutL c , cutR c)) ∈L rest)
           → Chain rest → Chain (rowL i m ++ rest)
  chainRow i zero {rest} covR ch = cons (tt , (i , 0)) dep0 ch
    where
      -- a span of length 0 has NO proper slot: both slots of its only
      -- cut are empty, and properness of a slot is non-emptiness of its
      -- complement.
      dep0 : (v : World) → v ≺ᵖ (tt , (i , 0)) → v ∈L rest
      dep0 _ (slot cat _ here true  pr) = E.rec (¬-<-zero (neLen pr))
      dep0 _ (slot cat _ here false pr) = E.rec (¬-<-zero (neLen pr))
  chainRow i (suc m) {rest} covR ch =
    cons (tt , (i , suc m)) dep (chainRow i m (λ m' p → covR m' (≼-suc p)) ch)
    where
      dep : (v : World) → v ≺ᵖ (tt , (i , suc m)) → v ∈L (rowL i m ++ rest)
      dep _ (slot cat _ c true  pr) =
        ∈++ˡ (memRow i m (cutL c) (cutL≼ c (neLen pr)))
      dep _ (slot cat _ c false pr) =
        ∈++ʳ (rowL i m) (covR (suc m) ≼-refl c (neLen pr))

  chainL : (i n : ℕ) → Chain (chartL i n)
  chainL i zero = cons (tt , (i , 0)) dep0 nil
    where
      dep0 : (v : World) → v ≺ᵖ (tt , (i , 0)) → v ∈L []
      dep0 _ (slot cat _ here true  pr) = E.rec (¬-<-zero (neLen pr))
      dep0 _ (slot cat _ here false pr) = E.rec (¬-<-zero (neLen pr))
  chainL i (suc n) =
    chainRow i (suc n) {rest = chartL (suc i) n}
             (λ m' p c q → covRight i n c q p) (chainL (suc i) n)

  rootIn : (i n : ℕ) → (tt , (i , n)) ∈L chartL i n
  rootIn i zero    = here
  rootIn i (suc n) = here

  -- THE SCHEDULE, at every root span.
  spanSched : (w : World) → Σ[ is ∈ List World ] Σ[ _ ∈ Chain is ] (w ∈L is)
  spanSched (tt , (i , n)) = chartL i n , chainL i n , rootIn i n
