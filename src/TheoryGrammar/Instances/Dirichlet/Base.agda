{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE DIRICHLET SUBSTRATE: the multiplicative monoid of positive
  integers, and the convolution it induces.

  The SIGNATURE here is literally the same as the one for strings and for
  bags -- a constant and a binary operation, one sort.  Only the MODEL
  changes, from (List Char , [] , ++) to (ℕ₊ , 1 , ·).  Everything
  downstream is forced by that one substitution, and the substitution is
  not cosmetic:

      Strings    a splitting of w is a CUT        w = u ++ v
      Dirichlet  a splitting of n is a FACTORING  n = d · e

  so `⊗ˢ mulop` is DIRICHLET convolution

      (A ⊗ B) n  =  Σ_{d·e = n}  A d × B e

  and not Cauchy convolution.  Every connective reinterprets along the
  same dictionary: `⌈p⌉ ⊗ ⊤` is "divisible by p", the residual `C ⟜ A`
  at e is "for every d with A d, C (d·e)" -- division rather than
  left-quotient -- and `⊤ ⊗ ⊤` is the set of divisors.  Where a grammar
  over strings has an ordinary generating function Σ |A w| x^{|w|} whose
  product is ⊗, a grammar over this promodel has a DIRICHLET series
  Σ |A n| n^(-s) whose product is ⊗.  That is where the name comes from,
  and it is the only reason to expect the two instances to look alike.

  ------------------------------------------------------------------
  WHY POSITIVES, and not ℕ.
  ------------------------------------------------------------------

  0 has to go, and not for hygiene.  0 = 2 · 0, so the splitting (2,0)
  of 0 has a proper left factor and a recursive slot back at 0; with
  `deg n = n` the slot does not shrink and `deg<` is false.  Excluding 0
  is exactly the hypothesis that makes divisibility well-founded, i.e.
  the grading in `Graded.agda` works IF AND ONLY IF the carrier is ℕ₊.

  Following the codebase's preference for RECURSIVE predicates over
  indexed families (see `IsNil` in Instances/Strings/Base and the comment
  there), positivity is `NonZero`, which reduces to `Unit` on successors.
  That reduction is load-bearing: `Unit` has definitional η, so two
  positives with the same value are DEFINITIONALLY equal once the value
  is in constructor form, and `⌈ n ⌉` never has to be repaired with a
  proof-irrelevance lemma.  `IsUnit` is the same trick for "= 1", playing
  the role `IsNil` plays for strings.

  ------------------------------------------------------------------
  SPLITTINGS WITHOUT PROOFS.
  ------------------------------------------------------------------

  CLAUDE.md forbids carrying an equation inside a `Split`, and the reason
  bites harder here than for strings: `val d · val e Eq.≡ val n` is green
  slime twice over -- its left side is a defined function applied to
  bound variables, AND those variables are projections out of a Σ, so
  matching the proof refines nothing at all.

  The cure is the one `Split3` already uses for concatenation: present
  the GRAPH of the operation as an inductive family, so the equation is
  discharged by constructors instead of by a proof term.

      Split3 u v w   is   u ++ v ≡ w     (recursion on u)
      Times  d e n   is   d  ·  e ≡ n    (recursion on d)
      Plus   a b n   is   a  +  b ≡ n    (recursion on a)

  `Times` is stratified over `Plus` exactly as `_·_` is stratified over
  `_+_`, and the recursion argument is chosen to MATCH the library's
  `_·_` (which recurses on its first argument).  That choice is what makes
  `timesAll d e : Times d e (d · e)` a two-line structural recursion
  instead of a lemma about `d · suc e`.

  Two consequences, both wanted:

    * `parts` stays a projection, so `⊗-UP-β` and `⊗-UP-η` from
      TheoryGrammar.Fibered remain `refl`;
    * `split` stays definitional, because `_·₊_` is defined through
      projections and Σ has η, so `val (a ·₊ b)` REDUCES to
      `val a · val b` for variable a, b.

  What an inductive family costs is that ordinary arithmetic has to be
  re-imported: `timesPath` converts a `Times` back into a path, once, and
  the order facts in `Graded.agda` are then plain statements about `_·_`
  from the standard library.  That is a single crossing of the
  abstraction barrier, in phase 1, which is where crossings belong.
-}
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

-- ==================================================================
-- The carrier: positive naturals.
-- ==================================================================

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

-- ==================================================================
-- The graph of addition and multiplication, as inductive families.
-- These are the `Split3` of this instance.
-- ==================================================================

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

-- ==================================================================
-- The signature.  Identical in shape to `monSig`/`cmSig`.
-- ==================================================================

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

-- ==================================================================
-- The promodel.  `Split mulop n` is the type of FACTORISATIONS of n.
-- ==================================================================

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

-- The total point, separately.  Multiplication on ℕ₊ is total, so this
-- instance loses nothing; the payoff is that `RulesF dirFib` and the
-- whole factorisation development never consult it -- they see only the
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
