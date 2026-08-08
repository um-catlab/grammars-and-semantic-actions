{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- THE DIRICHLET SUBSTRATE: the multiplicative monoid of positive integers,
   and the convolution it induces. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Dirichlet.Base where

open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib

-- The carrier: positive naturals.

-- `NonZero` (Cubical.Data.Nat.Base) is already the recursive predicate
-- we want: `NonZero zero = ⊥`, `NonZero (suc _) = Unit`.
ℕ₊ : Type₀
ℕ₊ = Σ[ n ∈ ℕ ] NonZero n

val : ℕ₊ → ℕ
val = fst

one₊ : ℕ₊
one₊ = 1 , tt

-- the atoms of the grading: everything ≥ 2, indexed by ℕ
2+_ : ℕ → ℕ₊
2+ k = suc (suc k) , tt

isPropNonZero : (n : ℕ) → isProp (NonZero n)
isPropNonZero zero    = E.isProp⊥
isPropNonZero (suc _) = isPropUnit

ℕ₊≡ : {a b : ℕ₊} → val a ≡ val b → a ≡ b
ℕ₊≡ = Σ≡Prop isPropNonZero

nz· : ∀ {m n} → NonZero m → NonZero n → NonZero (m · n)
nz· {zero}  {n}     ()
nz· {suc m} {zero}  _ ()
nz· {suc m} {suc n} _ _ = tt

-- Defined through PROJECTIONS, not patterns, so that `val (a ·₊ b)`
-- reduces to `val a · val b` on variables.  `split` below depends on it.
_·₊_ : ℕ₊ → ℕ₊ → ℕ₊
a ·₊ b = (val a · val b) , nz· (a .snd) (b .snd)

infixl 30 _·₊_

-- "= 1", as a recursive predicate.  The analogue of `IsNil`.
IsUnit : ℕ → Type₀
IsUnit zero          = ⊥
IsUnit (suc zero)    = Unit
IsUnit (suc (suc _)) = ⊥

-- The graph of addition and multiplication, as inductive families.
-- These are the `Split3` of this instance.

data Plus : ℕ → ℕ → ℕ → Type₀ where
  pzero : ∀ {b}     → Plus zero b b
  psuc  : ∀ {a b n} → Plus a b n → Plus (suc a) b (suc n)

data Times : ℕ → ℕ → ℕ → Type₀ where
  tzero : ∀ {e}       → Times zero e zero
  tsuc  : ∀ {d e r n} → Times d e r → Plus e r n → Times (suc d) e n

-- every pair adds/multiplies to its own sum/product ...
plusAll : (a b : ℕ) → Plus a b (a + b)
plusAll zero    b = pzero
plusAll (suc a) b = psuc (plusAll a b)

timesAll : (d e : ℕ) → Times d e (d · e)
timesAll zero    e = tzero
timesAll (suc d) e = tsuc (timesAll d e) (plusAll e (d · e))

-- ... and conversely, ONE crossing back to ordinary arithmetic.
plusPath : ∀ {a b n} → Plus a b n → a + b ≡ n
plusPath pzero    = refl
plusPath (psuc p) = cong suc (plusPath p)

timesPath : ∀ {d e n} → Times d e n → d · e ≡ n
timesPath tzero              = refl
timesPath (tsuc {e = e} t p) = cong (e +_) (timesPath t) ∙ plusPath p

-- the two unit laws, structurally (no path needed)
plus0 : (a : ℕ) → Plus a zero a
plus0 zero    = pzero
plus0 (suc a) = psuc (plus0 a)

times1L : (e : ℕ) → Times 1 e e
times1L e = tsuc tzero (plus0 e)

times1R : (d : ℕ) → Times d 1 d
times1R zero    = tzero
times1R (suc d) = tsuc (times1R d) (psuc pzero)

-- The signature.  Identical in shape to `monSig`/`cmSig`.

data DirOp : Type₀ where
  oneop mulop : DirOp

DirAr : DirOp → Type₀
DirAr oneop = ⊥
DirAr mulop = Bool

dirSig : SortedSig Unit ℓ-zero ℓ-zero
dirSig .ops          = DirOp
dirSig .arities      = DirAr
dirSig .sortOf _ _   = tt
dirSig .resultSort _ = tt

-- The `Fibered`.  `Split mulop n` is the type of FACTORISATIONS of n.

DirSplit : (o : DirOp) → ℕ₊ → Type₀
DirSplit oneop n = IsUnit (val n)
DirSplit mulop n = Σ[ d ∈ ℕ₊ ] Σ[ e ∈ ℕ₊ ] Times (val d) (val e) (val n)

DirParts : (o : DirOp) (n : ℕ₊) → DirSplit o n → DirAr o → ℕ₊
DirParts oneop n sp ()
DirParts mulop n (d , e , _) b = if b then d else e

dirFib : Fibered dirSig ℓ-zero ℓ-zero
dirFib .carrier _     = ℕ₊
dirFib .Split         = DirSplit
dirFib .parts         = DirParts

-- The total point, separately. Multiplication on ℕ₊ is total, so this
-- instance loses nothing; the payoff is that `RulesF dirFib` and the whole
-- factorisation development never consult it -- they see only the
-- SPLITTINGS, which is the right reading of Dirichlet convolution.
dirPoint : LaxPoint dirFib
dirPoint .op oneop _    = one₊
dirPoint .op mulop f    = f true ·₊ f false
dirPoint .split oneop f = tt
dirPoint .split mulop f = f true , f false , timesAll (val (f true)) (val (f false))
dirPoint .parts-split oneop f = funExt λ ()
dirPoint .parts-split mulop f = funExt λ { false → refl ; true → refl }

open RulesF dirFib public

Gr : Type₁
Gr = TheoryTy ℓ-zero tt
