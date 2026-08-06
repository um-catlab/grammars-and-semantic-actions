{-
  THE MULTIPLICATIVE GRADING NEEDS ZERO REMOVED.

  A negative result, and its repair.

  ------------------------------------------------------------------
  1.  THE ADDITIVE HALF WORKS, with `deg n = n`.

  `SplitAdd i j n` gives `i ≤ n` and `j ≤ n` by a direct induction
  (`splitAddL`, `splitAddR`), and a slot strictly shrinks as soon as its
  complement is nonzero (`splitAddL<`, `splitAddR<`).  This is the image
  under `length` of the string instance's `split3Len*`, and if the
  signature had only `{zeroOp, addOp}` we would be done: ℕ with the
  Cauchy product is a graded substrate, and Cauchy-recursive grammars
  (generating functions) exist.

  ------------------------------------------------------------------
  2.  THE MULTIPLICATIVE HALF FAILS, AT n = 0, AND ONLY THERE.

  `deg≤` demands that a factor is no bigger than the product.  But

      0 = 5 · 0,

  so `5` is a slot of a splitting of `0`, and `5 ≤ 0` is false.  That is
  `mul-part-can-exceed-whole` below: a *proved* refutation, not a hole.

  It is worth being exact about WHY this cannot be patched by choosing a
  cleverer `deg`.  One might hope to forbid the offending splitting.  You
  cannot: `Substrate` requires

      split : (o) (m⃗) → Split o (op o m⃗)

  -- every tuple must split its own composite.  `5 · 0 = 0` is a
  composite, so `(5,0)` MUST be a splitting of `0`.  The zero
  splittings are forced by the substrate axioms, not chosen.

  ------------------------------------------------------------------
  3.  AND THE DAMAGE IS TOTAL, NOT LOCAL.

  The natural guess is that ℕ-with-both-products still has SOME grading,
  just not `deg n = n`.  It does not.  Two instances of `deg≤` bracket
  the degree:

      deg k ≤ deg 0   for every k     (k is a factor of 0: 0 · k = 0)
      deg 0 ≤ deg m   for every m     (0 is a summand of m: 0 + m = m)

  so `deg` is CONSTANT, and by `Instances.Group.NoGrading.Degenerate`
  every `Proper` is empty and no description with a recursive position
  is `Guarded`.  This is the SAME phenomenon as the group obstruction,
  one notch weaker: ℕ is not group-like, but `mulOp` IS group-like AT
  THE SINGLE POINT 0 (every element occurs as a factor of 0), and one
  point of degeneracy is enough to flatten the whole degree function
  once the additive structure connects 0 to everything else.

  A single absorbing element destroys well-foundedness of divisibility,
  exactly as a group's invertibility does.

  ------------------------------------------------------------------
  4.  THE REPAIR: DELETE 0.

  On the positive naturals both convolutions are graded, and `posGraded`
  below proves it.  `ℕ₊` is represented as ℕ with `n` DENOTING `n+1`, so
  that the carrier stays a plain type with decidable equality and no
  proof component; the operations are then

      one    =  0                        (denoting 1)
      add    =  λ f → suc (f₁ + f₂)      ((a+1)+(b+1) = (a+b+2))
      mul    =  λ f → f₁·f₂ + f₁ + f₂    ((a+1)(b+1) = ab+a+b+1)

  and `deg n = n` works, with

      addP : EVERY slot is proper -- addition on positives is strictly
             decreasing outright, no side condition;
      mulP : a slot is proper when the OTHER factor is not the unit --
             i.e. exactly at PROPER DIVISORS.

  So Dirichlet-recursive grammars over ℕ₊ (multiplicative functions,
  sieves, factorisation parsers) exist, and Dirichlet-recursive grammars
  over ℕ do not.  Note `zeroOp` is necessarily absent from `posSig`:
  restricting the carrier is not a change of grading, it is a change of
  SIGNATURE, and that is the honest form of the repair.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Ring.Grading where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Substrate
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded

open import TheoryGrammar.Instances.Group.NoGrading
open import TheoryGrammar.Instances.Ring.Base public

-- ==================================================================
-- 1.  The additive half: `deg = id` is monotone, and strict at a
--     nonzero complement.  (Compare `split3Len*` for strings.)
-- ==================================================================

splitAddL : ∀ {i j n} → SplitAdd i j n → i ≤ n
splitAddL zl     = zero-≤
splitAddL (sl s) = suc-≤-suc (splitAddL s)

splitAddR : ∀ {i j n} → SplitAdd i j n → j ≤ n
splitAddR zl     = ≤-refl
splitAddR (sl s) = ≤-suc (splitAddR s)

splitAddL< : ∀ {i j n} → SplitAdd i j n → 0 < j → i < n
splitAddL< zl     pr = pr
splitAddL< (sl s) pr = suc-≤-suc (splitAddL< s pr)

splitAddR< : ∀ {i j n} → SplitAdd i j n → 0 < i → j < n
splitAddR< zl     pr = E.rec (¬-<-zero pr)
splitAddR< (sl s) pr = suc-≤-suc (splitAddR s)

-- ==================================================================
-- 2.  The multiplicative half fails at 0.  PROVED, not assumed.
--
-- `(5 , 0 , Eq.refl) : RingSplit mulOp 0` because `5 · 0` reduces to 0,
-- and its `true` slot is 5.  So `deg = id` cannot satisfy `deg≤`.
-- ==================================================================

zeroSplit : (k : ℕ) → RingSplit mulOp 0
zeroSplit k = 0 , k , Eq.refl          -- 0 · k ≡ 0, so k is a FACTOR of 0

mul-part-can-exceed-whole :
  ((n : ℕ) (sp : RingSplit mulOp n) (a : Bool) → RingParts mulOp n sp a ≤ n) → ⊥
mul-part-can-exceed-whole h = snotz (≤0→≡0 (h 0 (zeroSplit 5) false))

-- ==================================================================
-- 3.  ... and no other `deg` rescues it either: on ℕ with BOTH
--     products, every grading is degenerate.
--
-- The parameters are exactly the fields of `GradedSubstrate` other than
-- `sub`, so this quantifies over every graded substrate over `natSub`.
-- ==================================================================

module AnyGrading
  (deg    : ℕ → ℕ)
  (Proper : (o : RingOp) (n : ℕ) → RingSplit o n → RingAr o → Type₀)
  (deg≤   : (o : RingOp) (n : ℕ) (sp : RingSplit o n) (a : RingAr o)
          → deg (RingParts o n sp a) ≤ deg n)
  (deg<   : (o : RingOp) (n : ℕ) (sp : RingSplit o n) (a : RingAr o)
          → Proper o n sp a → deg (RingParts o n sp a) < deg n)
  where

  natGraded : GradedSubstrate ringSig ℓ-zero ℓ-zero
  natGraded .GradedSubstrate.sub    = natSub
  natGraded .GradedSubstrate.deg _  = deg
  natGraded .GradedSubstrate.Proper = Proper
  natGraded .GradedSubstrate.deg≤   = deg≤
  natGraded .GradedSubstrate.deg<   = deg<

  -- every k is a factor of 0 ...
  deg≤0 : (k : ℕ) → deg k ≤ deg 0
  deg≤0 k = deg≤ mulOp 0 (zeroSplit k) false

  -- ... and 0 is a summand of every m ...
  deg0≤ : (m : ℕ) → deg 0 ≤ deg m
  deg0≤ m = deg≤ addOp m (0 , m , zl) true

  -- ... so the degree cannot distinguish any two naturals.
  deg-const : (k m : ℕ) → deg k ≡ deg m
  deg-const k m =
    ≤-antisym (≤-trans (deg≤0 k) (deg0≤ m)) (≤-trans (deg≤0 m) (deg0≤ k))

  -- Everything the group obstruction gives follows from constancy
  -- alone, so it is reused verbatim: no proper slots, no guarded
  -- description, no `hyloC`, no inductive grammar over (ℕ,+,·).
  open Degenerate natGraded deg-const public

  module OneNonterminal where
    open AtFunctors ℓ-zero ℓ-zero Unit (λ _ → tt) public

    ℕ-no-inductive : (F : Functor tt) (n : ℕ) (sh : Sh F n)
                   → Guarded F → Pos F n sh → ⊥
    ℕ-no-inductive = no-guarded

-- ==================================================================
-- 4.  THE REPAIR.  ℕ₊, represented as ℕ with `n` denoting `n + 1`.
-- ==================================================================

data PosOp : Type₀ where
  oneP addP mulP : PosOp

PosAr : PosOp → Type₀
PosAr oneP = ⊥
PosAr addP = Bool
PosAr mulP = Bool

posSig : SortedSig Unit ℓ-zero ℓ-zero
posSig .ops          = PosOp
posSig .arities      = PosAr
posSig .sortOf _ _   = tt
posSig .resultSort _ = tt

-- "not the multiplicative unit", recursively (so case splits are on ℕ)
IsPos : ℕ → Type₀
IsPos zero    = ⊥
IsPos (suc _) = Unit

posOf : (n : ℕ) → IsPos n → 0 < n
posOf zero    ()
posOf (suc n) _ = suc-≤-suc zero-≤

PosSplit : (o : PosOp) → ℕ → Type₀
PosSplit oneP n = IsZero n
PosSplit addP n = Σ[ i ∈ ℕ ] Σ[ j ∈ ℕ ] (suc (i + j) Eq.≡ n)
PosSplit mulP n = Σ[ i ∈ ℕ ] Σ[ j ∈ ℕ ] (i · j + i + j Eq.≡ n)

PosParts : (o : PosOp) (n : ℕ) → PosSplit o n → PosAr o → ℕ
PosParts oneP n sp ()
PosParts addP n (i , j , _) b = if b then i else j
PosParts mulP n (i , j , _) b = if b then i else j

posSub : Substrate posSig ℓ-zero ℓ-zero
posSub .carrier _ = ℕ
posSub .op oneP _ = 0                                     -- denotes 1
posSub .op addP f = suc (f true + f false)                -- (a+1)+(b+1)
posSub .op mulP f = f true · f false + f true + f false   -- (a+1)(b+1)
posSub .Split     = PosSplit
posSub .parts     = PosParts
posSub .split oneP f = tt
posSub .split addP f = f true , f false , Eq.refl
posSub .split mulP f = f true , f false , Eq.refl
posSub .parts-split oneP f = funExt λ ()
posSub .parts-split addP f = funExt λ { true → refl ; false → refl }
posSub .parts-split mulP f = funExt λ { true → refl ; false → refl }

-- ------------------------------------------------------------------
-- Arithmetic, in the two shapes the degree proofs need.
-- ------------------------------------------------------------------

private
  0<+r : (x y : ℕ) → 0 < y → x < x + y
  0<+r x y p = subst (_< x + y) (+-zero x) (<-k+ p)

  0<+l : (x y : ℕ) → 0 < x → y < x + y
  0<+l x y p = <-+k p          -- 0 + y reduces to y

  ≤A : (i j n : ℕ) → suc (i + j) Eq.≡ n → (b : Bool) → (if b then i else j) ≤ n
  ≤A i j n Eq.refl true  = ≤-suc ≤SumLeft
  ≤A i j n Eq.refl false = ≤-suc ≤SumRight

  ≤M : (i j n : ℕ) → i · j + i + j Eq.≡ n → (b : Bool) → (if b then i else j) ≤ n
  ≤M i j n Eq.refl true  = ≤-trans (≤SumRight {n = i} {k = i · j}) ≤SumLeft
  ≤M i j n Eq.refl false = ≤SumRight

  -- ADDITION ON POSITIVES IS UNCONDITIONALLY STRICT: no side condition,
  -- because there is no empty summand to worry about.
  <A : (i j n : ℕ) → suc (i + j) Eq.≡ n → (b : Bool) → (if b then i else j) < n
  <A i j n Eq.refl true  = suc-≤-suc ≤SumLeft
  <A i j n Eq.refl false = suc-≤-suc ≤SumRight

  -- MULTIPLICATION IS STRICT EXACTLY AT PROPER DIVISORS: the other
  -- factor must not be the unit.
  <M : (i j n : ℕ) → i · j + i + j Eq.≡ n → (b : Bool)
     → IsPos (if b then j else i) → (if b then i else j) < n
  <M i j n Eq.refl true  pr =
    ≤<-trans (≤SumRight {n = i} {k = i · j}) (0<+r (i · j + i) j (posOf j pr))
  <M i j n Eq.refl false pr =
    0<+l (i · j + i) j (<≤-trans (posOf i pr) (≤SumRight {n = i} {k = i · j}))

PosProper : (o : PosOp) (n : ℕ) → PosSplit o n → PosAr o → Type₀
PosProper oneP n sp ()
PosProper addP n sp b = Unit
PosProper mulP n (i , j , _) b = IsPos (if b then j else i)

-- ------------------------------------------------------------------
-- THEOREM.  ℕ₊ with BOTH convolutions is a graded substrate.
-- ------------------------------------------------------------------

posGraded : GradedSubstrate posSig ℓ-zero ℓ-zero
posGraded .sub     = posSub
posGraded .deg _ n = n
posGraded .Proper  = PosProper
posGraded .deg≤ oneP n sp ()
posGraded .deg≤ addP n (i , j , e) b = ≤A i j n e b
posGraded .deg≤ mulP n (i , j , e) b = ≤M i j n e b
posGraded .deg< oneP n sp ()
posGraded .deg< addP n (i , j , e) b pr = <A i j n e b
posGraded .deg< mulP n (i , j , e) b pr = <M i j n e b pr

-- and so the guarded-description machinery is available over ℕ₊
module PosGuard where
  open Guard posGraded ℓ-zero Unit (λ _ → tt) public
