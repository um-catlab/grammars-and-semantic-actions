{-
  ℤ UNDER ADDITION: A SUBSTRATE WHOSE EVERY GRADING IS DEGENERATE.

  The signature is that of a monoid -- `zeroOp` (arity ⊥) and `addOp`
  (arity Bool), one sort.  Inverses are deliberately NOT in the
  signature: the obstruction of `NoGrading` needs only that the
  operation is solvable in a slot, and stating it that way keeps the
  theorem about the SHAPE of the splittings rather than about extra
  operations.  What makes ℤ a group shows up instead in the splittings:

      Split addOp n  =  ℤ,        parts addOp n i = (i , n - i)

  -- writing `n` as a sum is the same thing as choosing its left
  summand, freely.  Compare strings, where `Split appop w` is the
  (finite, `length w + 1`-element) set of cut points.  The splitting
  type of a group does not shrink as the element shrinks, because
  nothing shrinks.

  Consequently `GroupLike ℤSub addOp true` is witnessed by `refl`:
  slot `true` of the splitting `i` IS `i`, so it ranges over all of ℤ.
  `NoGrading.GroupObstruction` then gives, for EVERY grading of `ℤSub`:

      deg is constant,
      no splitting has a proper slot,
      no description with a recursive position is `Guarded`,
      hence no `hyloC`, no `löb`, no inductive grammar, no parser.

  This is stated below as `ℤ-deg-const` / `ℤ-no-proper` /
  `ℤ-no-inductive`, quantified over an ARBITRARY grading supplied as
  its four components (`deg`, `Proper`, `deg≤`, `deg<`) -- i.e. over an
  arbitrary `GradedSubstrate` whose `sub` is `ℤSub`.  Note again that
  the degenerate grading (`deg = const 0`, `Proper = ⊥`) does exist; the
  theorem is that it is the only one.

  Why this is not a defect.  The same degeneration is familiar from
  phase semantics of linear logic: over a group the phase space is
  homogeneous and every fact is provable at every point.  The criterion
  it points at:

      inductive grammars exist  ⟺  the divisibility preorder
                                     m ≼ n  =  "m is a slot of some
                                                splitting of n"
                                   is well-founded.

  Strings, bags, heaps, (ℕ,+), (ℕ₊,×): well-founded, and their instances
  in this library all carry gradings with nonempty `Proper`.  Groups,
  (ℚ₊,×), ℤ: the preorder is the total relation, hence not well-founded,
  hence no induction.  ℤ is the smallest interesting witness.
-}
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
open import TheoryGrammar.Substrate
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded
open import TheoryGrammar.RulesSub

open import TheoryGrammar.Instances.Group.NoGrading

-- ==================================================================
-- The signature: one sort, a constant and a binary operation.
-- ==================================================================

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

-- ==================================================================
-- The substrate.  THE WHOLE CONTENT IS IN `GrpSplit addOp`.
--
-- For a monoid the splittings of `n` are the ways of writing n = i + j.
-- For a GROUP that is a free choice of `i`, with `j = n - i` forced --
-- so `Split addOp n ≃ ℤ`, uniformly in n.  No proof component is
-- carried (CLAUDE.md's third trap), and both β and η for ⊗ˢ stay refl.
-- ==================================================================

GrpSplit : (o : GrpOp) → ℤ → Type₀
GrpSplit zeroOp n = pos 0 Eq.≡ n
GrpSplit addOp  n = ℤ

GrpParts : (o : GrpOp) (n : ℤ) → GrpSplit o n → GrpAr o → ℤ
GrpParts zeroOp n sp ()
GrpParts addOp  n i b = if b then i else (n - i)

private
  -- (a + b) - a ≡ b : the group law, as the substrate's `parts-split`.
  +-cancelˡ : (a b : ℤ) → (a + b) - a ≡ b
  +-cancelˡ a b = cong (_- a) (+Comm a b) ∙ plusMinus a b

ℤSub : Substrate grpSig ℓ-zero ℓ-zero
ℤSub .carrier _     = ℤ
ℤSub .op zeroOp _   = pos 0
ℤSub .op addOp f    = f true + f false
ℤSub .Split         = GrpSplit
ℤSub .parts         = GrpParts
ℤSub .split zeroOp f = Eq.refl
ℤSub .split addOp f  = f true
ℤSub .parts-split zeroOp f = funExt λ ()
ℤSub .parts-split addOp f  =
  funExt λ { true → refl ; false → +-cancelˡ (f true) (f false) }

open RulesS ℤSub public

Gr : Type₁
Gr = TheoryTy ℓ-zero tt

-- the additive convolution over ℤ: (A ⊗' B) n = Σ i. A i × B (n - i)
_⊗'_ : Gr → Gr → Gr
A ⊗' B = ⊗ˢ addOp (λ b → if b then A else B)

infixr 20 _⊗'_

-- ==================================================================
-- ℤ IS GROUP-LIKE AT THE LEFT SLOT.  This is the whole input to the
-- obstruction, and it is `refl`: the splitting IS the left summand.
-- ==================================================================

ℤGroupLike : GroupLike ℤSub addOp true
ℤGroupLike n h = h , refl

-- ==================================================================
-- THE THEOREM, over an arbitrary grading of `ℤSub`.
--
-- The four module parameters are exactly the fields of
-- `GradedSubstrate` other than `sub`; `ℤGraded` below reassembles them,
-- so this really does quantify over every graded substrate whose
-- underlying substrate is `ℤSub`.
-- ==================================================================

module AnyGrading
  (deg    : ℤ → ℕ)
  (Proper : (o : GrpOp) (n : ℤ) → GrpSplit o n → GrpAr o → Type₀)
  (deg≤   : (o : GrpOp) (n : ℤ) (sp : GrpSplit o n) (a : GrpAr o)
          → deg (GrpParts o n sp a) ≤ deg n)
  (deg<   : (o : GrpOp) (n : ℤ) (sp : GrpSplit o n) (a : GrpAr o)
          → Proper o n sp a → deg (GrpParts o n sp a) < deg n)
  where

  ℤGraded : GradedSubstrate grpSig ℓ-zero ℓ-zero
  ℤGraded .GradedSubstrate.sub    = ℤSub
  ℤGraded .GradedSubstrate.deg _  = deg
  ℤGraded .GradedSubstrate.Proper = Proper
  ℤGraded .GradedSubstrate.deg≤   = deg≤
  ℤGraded .GradedSubstrate.deg<   = deg<

  open GroupObstruction ℤGraded addOp true ℤGroupLike public

  -- THEOREM 1.  ℤ carries no information: the degree cannot see it.
  ℤ-deg-const : (m n : ℤ) → deg m ≡ deg n
  ℤ-deg-const = deg-const

  -- THEOREM 2.  No slot of any splitting is proper.  So the ONLY legal
  -- choice of `Proper` is the empty one -- the grading is degenerate.
  ℤ-no-proper : (o : GrpOp) (n : ℤ) (sp : GrpSplit o n) (a : GrpAr o)
              → Proper o n sp a → ⊥
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
