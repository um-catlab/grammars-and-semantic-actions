{- ℤ UNDER ADDITION: A SUBSTRATE WHOSE EVERY GRADING IS DEGENERATE. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Group.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Unit
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order using (_≤_; _<_)
open import Cubical.Data.Empty as E using (⊥)
open import Cubical.Data.Int
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded
open import TheoryGrammar.RulesFib

open import TheoryGrammar.Instances.Group.NoGrading

-- The signature: one sort, a constant and a binary operation.

data GrpOp : Type₀ where
  zeroOp addOp : GrpOp

GrpAr : GrpOp → Type₀
GrpAr zeroOp = ⊥
GrpAr addOp  = Bool

grpSig : SortedSig Unit ℓ-zero ℓ-zero
grpSig .ops          = GrpOp
grpSig .arities      = GrpAr
grpSig .sortOf _ _   = tt
grpSig .resultSort _ = tt

-- The `Fibered`. THE WHOLE CONTENT IS IN `GrpSplit addOp`.

GrpSplit : (o : GrpOp) → ℤ → Type₀
GrpSplit zeroOp n = pos 0 Eq.≡ n
GrpSplit addOp  n = ℤ

GrpParts : (o : GrpOp) (n : ℤ) → GrpSplit o n → GrpAr o → ℤ
GrpParts zeroOp n sp ()
GrpParts addOp  n i b = if b then i else (n - i)

private
  -- (a + b) - a ≡ b : the group law, as the `Fibered`'s `parts-split`.
  +-cancelˡ : (a b : ℤ) → (a + b) - a ≡ b
  +-cancelˡ a b = cong (_- a) (+Comm a b) ∙ plusMinus a b

ℤFib : Fibered grpSig ℓ-zero ℓ-zero
ℤFib .carrier _     = ℤ
ℤFib .Split         = GrpSplit
ℤFib .parts         = GrpParts

-- The total point, separately: ℤ is total under addition, so the split
-- costs this instance nothing.
ℤPoint : LaxPoint ℤFib
ℤPoint .op zeroOp _   = pos 0
ℤPoint .op addOp f    = f true + f false
ℤPoint .split zeroOp f = Eq.refl
ℤPoint .split addOp f  = f true
ℤPoint .parts-split zeroOp f = funExt λ ()
ℤPoint .parts-split addOp f  =
  funExt λ { true → refl ; false → +-cancelˡ (f true) (f false) }

open RulesF ℤFib public

Gr : Type₁
Gr = TheoryTy ℓ-zero tt

-- the additive convolution over ℤ: (A ⊗' B) n = Σ i. A i × B (n - i)
_⊗'_ : Gr → Gr → Gr
A ⊗' B = ⊗ˢ addOp (λ b → if b then A else B)

infixr 20 _⊗'_

-- ℤ IS GROUP-LIKE AT THE LEFT SLOT.  This is the whole input to the
-- obstruction, and it is `refl`: the splitting IS the left summand.

ℤGroupLike : GroupLike ℤFib addOp true
ℤGroupLike n h = h , refl

-- THE THEOREM, over an arbitrary grading of `ℤFib`.

module AnyGrading (G : Grading ℤFib) where

  ℤGraded : GradedFib grpSig ℓ-zero ℓ-zero
  ℤGraded = graded ℤFib G

  open GroupObstruction ℤGraded addOp true ℤGroupLike public

  -- THEOREM 1.  ℤ carries no information: the degree cannot see it.
  ℤ-deg-const : (m n : ℤ) → G .deg tt m ≡ G .deg tt n
  ℤ-deg-const = deg-const

  -- THEOREM 2.  No slot of any splitting is proper.  So the ONLY legal
  -- choice of `Proper` is the empty one -- the grading is degenerate.
  ℤ-no-proper : (o : GrpOp) (n : ℤ) (sp : GrpSplit o n) (a : GrpAr o)
              → G .Proper o n sp a → ⊥
  ℤ-no-proper = no-proper

  -- THEOREM 3.  No description over ℤ is guarded once it has a single
  -- recursive position.  Instantiated at one nonterminal for
  -- readability; `AtFunctors` states it at any set of nonterminals.
  module OneNonterminal where
    open AtFunctors ℓ-zero ℓ-zero Unit (λ _ → tt) public

    ℤ-no-inductive : (F : Functor tt) (n : ℤ) (sh : Sh F n)
                   → Guarded F → Pos F n sh → ⊥
    ℤ-no-inductive = no-guarded

    -- and the sharp form: a guarded description over ℤ is not recursive
    -- at all -- its least fixed point is its own shape functor.
    ℤ-μ-noRec = μ-noRec
