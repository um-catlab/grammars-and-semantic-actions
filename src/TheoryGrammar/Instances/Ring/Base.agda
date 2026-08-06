{-
  TWO CONVOLUTIONS ON ONE CARRIER: THE CAUCHY AND DIRICHLET PRODUCTS.

  The semiring ℕ, presented as a SINGLE promodel carrying FOUR
  operations -- `zeroOp`/`addOp` and `oneOp`/`mulOp`.  That is the point
  of the file: distributivity is a statement relating two operations of
  the SAME signature, so the two monoid structures must be splittings of
  one promodel, not two promodels that happen to share a carrier.  (It
  is also why this file imports nothing from the Nat or Dirichlet
  instances elsewhere in `Instances/`: those are at different
  signatures.)

  The two convolutions are then the two multiplicatives of one calculus:

      (A ⊗₊ B) n  =  Σ (i,j) with i + j = n.  A i × B j    -- CAUCHY
      (A ⊗× B) n  =  Σ (i,j) with i · j = n.  A i × B j    -- DIRICHLET

  and `ε₊ = ⌈0⌉`-ish, `ε× = ⌈1⌉`-ish arise as `⊗ˢ` at the nullary
  operations.  Grammars over ⊗₊ are generating functions; grammars over
  ⊗× are Dirichlet series.  They are the same connective former at two
  operations of one theory -- which is exactly what
  `TheoryGrammar.Base`'s "one ⊗[o] per OPERATION" buys.

  ------------------------------------------------------------------
  SPLITTINGS.

  Additive splittings are an INDUCTIVE FAMILY, in the style of `Split3`
  in `Instances/Strings/Base` -- `SplitAdd i j n` is "n counts down from
  i while j stays put".  This keeps `parts` a projection, so `⊗-UP-β`
  and `⊗-UP-η` remain `refl` and no green slime appears.

  Multiplicative splittings carry an `Eq`-proof, `i · j Eq.≡ n`.  This
  is the one place the file departs from CLAUDE.md's third trap ("do not
  carry proofs in a `Split`"), and the departure is deliberate and
  harmless: `parts` never INSPECTS the proof (it is `fst`/`fst ∘ snd`),
  so both universal properties stay definitional.  What is lost is only
  that `Split mulOp` does not itself compute -- an inductive family for
  "i divides n with cofactor j" would recover that, at the cost of an
  encoding of multiplication as repeated addition, which buys nothing
  for the results in `Grading` and `Distributivity`.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Ring.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib

-- ==================================================================
-- The signature of a semiring: one sort, four operations.
-- ==================================================================

data RingOp : Type₀ where
  zeroOp addOp oneOp mulOp : RingOp

RingAr : RingOp → Type₀
RingAr zeroOp = ⊥
RingAr addOp  = Bool
RingAr oneOp  = ⊥
RingAr mulOp  = Bool

ringSig : SortedSig Unit ℓ-zero ℓ-zero
ringSig .ops          = RingOp
ringSig .arities      = RingAr
ringSig .sortOf _ _   = tt
ringSig .resultSort _ = tt

-- ==================================================================
-- Splittings.
-- ==================================================================

-- `SplitAdd i j n` : n is i followed by j.  Compare `Split3` for
-- strings -- this is its image under `length`.
data SplitAdd : ℕ → ℕ → ℕ → Type₀ where
  zl : ∀ {n} → SplitAdd 0 n n
  sl : ∀ {i j n} → SplitAdd i j n → SplitAdd (suc i) j (suc n)

splitAllAdd : (i j : ℕ) → SplitAdd i j (i + j)
splitAllAdd zero    j = zl
splitAllAdd (suc i) j = sl (splitAllAdd i j)

-- the sum a splitting witnesses
splitAdd≡ : ∀ {i j n} → SplitAdd i j n → i + j ≡ n
splitAdd≡ zl     = refl
splitAdd≡ (sl s) = cong suc (splitAdd≡ s)

-- Unit predicates as RECURSIVE families (as `IsNil` for strings), so
-- that every case split happens on the number itself.
IsZero : ℕ → Type₀
IsZero zero    = Unit
IsZero (suc _) = ⊥

IsUnit : ℕ → Type₀
IsUnit zero          = ⊥
IsUnit (suc zero)    = Unit
IsUnit (suc (suc _)) = ⊥

RingSplit : (o : RingOp) → ℕ → Type₀
RingSplit zeroOp n = IsZero n
RingSplit addOp  n = Σ[ i ∈ ℕ ] Σ[ j ∈ ℕ ] SplitAdd i j n
RingSplit oneOp  n = IsUnit n
RingSplit mulOp  n = Σ[ i ∈ ℕ ] Σ[ j ∈ ℕ ] (i · j Eq.≡ n)

RingParts : (o : RingOp) (n : ℕ) → RingSplit o n → RingAr o → ℕ
RingParts zeroOp n sp ()
RingParts addOp  n (i , j , _) b = if b then i else j
RingParts oneOp  n sp ()
RingParts mulOp  n (i , j , _) b = if b then i else j

natFib : Fibered ringSig ℓ-zero ℓ-zero
natFib .carrier _   = ℕ
natFib .Split       = RingSplit
natFib .parts       = RingParts

-- The total point, separately: (ℕ,0,+,1,·) is a total algebra, so the
-- split loses nothing here.  What it buys is that `RulesF natFib` and
-- the two convolutions below never consult it.
natPoint : LaxPoint natFib
natPoint .op zeroOp _ = 0
natPoint .op addOp f  = f true + f false
natPoint .op oneOp _  = 1
natPoint .op mulOp f  = f true · f false
natPoint .split zeroOp f = tt
natPoint .split addOp f  = f true , f false , splitAllAdd (f true) (f false)
natPoint .split oneOp f  = tt
natPoint .split mulOp f  = f true , f false , Eq.refl
natPoint .parts-split zeroOp f = funExt λ ()
natPoint .parts-split addOp f  = funExt λ { true → refl ; false → refl }
natPoint .parts-split oneOp f  = funExt λ ()
natPoint .parts-split mulOp f  = funExt λ { true → refl ; false → refl }

open RulesF natFib public

Gr : Type₁
Gr = TheoryTy ℓ-zero tt

-- ==================================================================
-- The two convolutions, and their units.
-- ==================================================================

-- CAUCHY product: coefficientwise, (A⊗₊B)_n = Σ_{i+j=n} A_i B_j
_⊗₊_ : Gr → Gr → Gr
A ⊗₊ B = ⊗ˢ addOp (λ b → if b then A else B)

-- DIRICHLET product: (A⊗×B)_n = Σ_{i·j=n} A_i B_j
_⊗×_ : Gr → Gr → Gr
A ⊗× B = ⊗ˢ mulOp (λ b → if b then A else B)

infixr 20 _⊗×_
infixr 19 _⊗₊_

ε₊ : Gr
ε₊ = ⊗ˢ zeroOp (λ ())

ε× : Gr
ε× = ⊗ˢ oneOp (λ ())

-- ==================================================================
-- Intro and elim (phase-1 primitives: they name the splitting).
-- ==================================================================

⊗₊-mk : {A B : Gr} {i j n : ℕ} → SplitAdd i j n → A i → B j → (A ⊗₊ B) n
⊗₊-mk {i = i} {j} s a b = (i , j , s) , λ { true → a ; false → b }

⊗×-mk : {A B : Gr} {i j n : ℕ} → i · j Eq.≡ n → A i → B j → (A ⊗× B) n
⊗×-mk {i = i} {j} e a b = (i , j , e) , λ { true → a ; false → b }

⊗₊-elim : {A B C : Gr}
        → (∀ {i j n} → SplitAdd i j n → A i → B j → C n)
        → (A ⊗₊ B) ⊢ C
⊗₊-elim f n ((i , j , s) , h) = f s (h true) (h false)

⊗×-elim : {A B C : Gr}
        → (∀ {i j n} → i · j Eq.≡ n → A i → B j → C n)
        → (A ⊗× B) ⊢ C
⊗×-elim f n ((i , j , e) , h) = f e (h true) (h false)

ε₊-mk : ε₊ 0
ε₊-mk = tt , λ ()

ε×-mk : ε× 1
ε×-mk = tt , λ ()
