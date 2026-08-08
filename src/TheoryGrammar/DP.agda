{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- DYNAMIC PROGRAMMING, FROM LÖB. `Later.WFLater` gives a recurrence a
   solution (`löb`) and says it is UNIQUE (`löb-unique`). -}
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

  -- THE RECURRENCE, as a type.  A dynamic programming problem IS a
  -- term of this type: "solve me, given solutions to my dependencies".
  -- Nothing else about the problem has to be said.

  Step : Type (ℓ-max ℓI (ℓ-max ℓR ℓM))
  Step = (i : I) → ▷ A i → A i

  -- ... and `löb : Step → (i : I) → A i` is its solution, `löb-unique`
  -- says it is the only one.  Both are inherited from `WFLater`.

  -- THE TABLE: `AllYes'` (Enumerable), a nested `×` over a list of
  -- subproblems.

  Table : List I → Type (ℓ-max ℓI ℓM)
  Table = AllYes' A

  -- A table covering everything below `i` serves the `later` at `i`: the
  -- coercion from data back to the Π, and where the sharing is cashed in.
  untab : {i : I} (is : List I) → ((j : I) → j ≺ i → j ∈L is)
        → Table is → ▷ A i
  untab is cov tbl j q = lookupYes' is j (cov j q) tbl

  -- ONE ROW: extend a table to a batch whose dependencies it already
  -- covers.

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

  -- THE SCHEDULE, with its invariant in the type: a `Chain is`
  -- enumerates subproblems so that every element's dependencies appear
  -- LATER, hence `build` is total with no side conditions.

  data Chain : List I → Type (ℓ-max ℓI ℓR) where
    nil  : Chain []
    cons : {is : List I} (i : I) → ((k : I) → k ≺ i → k ∈L is)
         → Chain is → Chain (i ∷ is)

  -- `chainOf` prepends a batch to a chain, given only that every
  -- dependency of every member already lies in it.

  chainOf : (bs rest : List I) → Chain rest
          → ((i : I) → i ∈L bs → (k : I) → k ≺ i → k ∈L rest)
          → Chain (bs ++ rest)
  chainOf []       rest ch cov = ch
  chainOf (i ∷ bs) rest ch cov =
    cons i (λ k q → ∈++ʳ bs (cov i here k q))
           (chainOf bs rest ch λ j p → cov j (there p))

  -- THE TABULATED FIXED POINT.  `share` takes the tail's table as an
  -- ARGUMENT, so both its uses project one value.  That single binding
  -- is the difference between cubic and exponential.

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

  -- ... and it is the right answer. The middle two lines are the argument:
  -- at the head of the chain the entry is `st j` applied to the tail's
  -- table, `löb-unfold` says `löb st j` is `st j` applied to `löb`, and
  -- the IH identifies the two arguments pointwise.

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

  -- CORRECTNESS.  Whatever schedule an instance uses, it need only
  -- show its result satisfies the recurrence; that it computes THE
  -- answer is then `löb-unique`.

  correct : (st : Step) (f : (i : I) → A i)
          → ((i : I) → f i ≡ st i (λ j _ → f j))
          → (i : I) → f i ≡ löb st i
  correct = löb-unique

  -- THE SAME THING WITH A TREE SPINE -- the one to use.

  QTable : Seq I → Type ℓM
  QTable = Tab A

  -- `untab`, at the tree spine. Same three words -- look the address up in
  -- the table -- except that `cov k q` is now a PATH, so this is `O(log
  -- n)` on both sides of the composition instead of `O(offset)` on both.
  untabQ : {i : I} (c : Seq I) → ((k : I) → k ≺ i → k ∈Q c)
         → QTable c → ▷ A i
  untabQ c cov tb k q = lookupQ (cov k q) tb

  -- THE SCHEDULE, with its context in the type.

  data ChainQ : Seq I → Seq I → Type (ℓ-max ℓI ℓR) where
    qnil : {c : Seq I} → ChainQ εQ c
    qone : {c : Seq I} (i : I) → ((k : I) → k ≺ i → k ∈Q c)
         → ChainQ (oneQ i) c
    qapp : {s t c : Seq I} → ChainQ t c → ChainQ s (t ⋈ c)
         → ChainQ (s ⋈ t) c
    -- ... and its mirror: same blocks and same dependency direction, laid
    -- out `t ⋈ s`.
    qappR : {s t c : Seq I} → ChainQ t c → ChainQ s (t ⋈ c)
          → ChainQ (t ⋈ s) c

  -- THE TABULATED FIXED POINT, AGAIN. `shareQ` is `share`'s job at the
  -- branching spine: the right half's table is a lambda-bound ARGUMENT, so
  -- it is forced once and its two uses -- serving the left half's context
  -- and being re-emitted as the right component of the answer -- project
  -- the same value.

  buildQ  : Step → {s c : Seq I} → ChainQ s c → QTable c → QTable s
  shareQ  : (st : Step) {s t c : Seq I}
          → ChainQ s (t ⋈ c) → QTable c → QTable t → QTable s × QTable t
  -- `shareQ` with the pair the other way up.  `tb` is still bound ONCE
  -- and still used twice, which is the whole of the sharing.
  shareR  : (st : Step) {s t c : Seq I}
          → ChainQ s (t ⋈ c) → QTable c → QTable t → QTable t × QTable s

  buildQ st qnil           tc = tt*
  buildQ st (qone i cov)   tc = st i (untabQ _ cov tc)
  buildQ st (qapp  cht chs) tc = shareQ st chs tc (buildQ st cht tc)
  buildQ st (qappR cht chs) tc = shareR st chs tc (buildQ st cht tc)

  shareQ st chs tc tb = buildQ st chs (tb , tc) , tb

  shareR st chs tc tb = tb , buildQ st chs (tb , tc)

  solveQ : Step → {s : Seq I} → ChainQ s εQ → (i : I) → i ∈Q s → A i
  solveQ st ch i p = lookupQ p (buildQ st ch tt*)

  -- ... AND IT IS STILL THE RIGHT ANSWER.

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
  -- the mirror, with `lQ`/`rQ` swapped and nothing else
  buildQ-correct st (qappR cht chs) tc gc i (lQ p) =
    buildQ-correct st cht tc gc i p
  buildQ-correct st (qappR cht chs) tc gc i (rQ p) =
    buildQ-correct st chs (buildQ st cht tc , tc)
                   (goodPair st (buildQ-correct st cht tc gc) gc) i p

  solveQ≡ : (st : Step) {s : Seq I} (ch : ChainQ s εQ) (i : I) (p : i ∈Q s)
          → solveQ st ch i p ≡ löb st i
  solveQ≡ st ch = buildQ-correct st ch tt* (λ i ())

  -- BATCHES, WHICH IS WHAT A CHART WANTS. `batchQ` turns a whole block
  -- into a chain in one move, given only that no member depends on another
  -- member -- which is exactly what "a level of the chart" means, and why
  -- a CYK row is a batch: all spans of length `k` depend only on shorter
  -- ones.

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

  -- THE HYPOTHESIS AN INSTANCE MUST SUPPLY. Finitary dependencies -- and
  -- NOT a measure.

  record Finitary : Type (ℓ-max ℓI ℓR) where
    field
      deps   : I → List I
      depsOk : (i j : I) → j ≺ i → j ∈L deps i

-- THE DEPENDENCY ORDER OF A GRADED THEORY. A DP interface is only worth
-- having if the order comes from the theory rather than being invented per
-- instance.

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
