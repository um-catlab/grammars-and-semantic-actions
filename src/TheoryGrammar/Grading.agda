{-
  CHECK 3: local contractivity, and the hylomorphism.

  Checks 1 and 2 (algebras and coalgebras internal to families over `Ix`)
  are in TheoryGrammar.Inductive: `⟦_⟧`, `Fmap`, `Alg`, `Coalg`.  This
  file supplies the third, and with it the recursive-coalgebra story.

  The point of the file is that for a CONTAINER functor, local
  contractivity is not an extra structure you must supply -- it is
  DERIVABLE from a single lemma:

      Guarded F  =  every position's next index is STRICTLY smaller.

  Because `Fmap h (sh , f) = (sh , h ∘ f)` does not touch shapes, the
  strength `Hδ : ▷(A ⇒ B) → (H A ⇒ H B)` -- ccl's `▷HomActionFam` -- is
  forced, and `Guarded` is precisely the side condition that lets you
  apply the later-function at each position.  That is `mapGuarded` below,
  and it IS the strength.

  Guardedness itself decomposes: `Guarded≤` ("no growth") holds for every
  description former including `Var`, and the single STRICT step comes
  from `⊗e` at a proper splitting.  So the shape of the argument is

      Var contributes equality,  ⊗e contributes the strict decrease,

  which is the generic form of "the recursive call is on a proper part".
  `Var` at the top of a description is exactly what fails to be guarded --
  that is left recursion, correctly rejected.

  The degree is ℕ.  Every instance in ccl and gsa grades to ℕ via
  `pullbackWFOrder ℕWFOrder`, so this loses nothing today; the order can
  be made abstract later if a lexicographic instance needs it.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Grading where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Unit
open import Cubical.Induction.WellFounded

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
open import TheoryGrammar.Later

private variable ℓS ℓ ℓ' ℓX ℓP ℓA ℓM ℓN ℓV : Level

-- ==================================================================
-- A promodel with a grading.
-- ==================================================================

record GradedFib {S : Type ℓS} (σ : SortedSig S ℓ ℓ') ℓX ℓP
  : Type (ℓ-max ℓS (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max (ℓ-suc ℓX) (ℓ-suc ℓP))))) where
  field
    fib : Fibered σ ℓX ℓP
    deg : (s : S) → fib .carrier s → ℕ

    -- Properness is DATA ON THE SPLITTING.  Phrasing it this way dodges
    -- "some slot other than a", and hence dodges needing
    -- `Discrete (arities o)` -- the same problem `Focus` was introduced
    -- to avoid.  For strings, `Proper appop w sp false` says the left
    -- part is nonempty.
    Proper : (o : σ .ops) (m : fib .carrier (σ .resultSort o))
           → fib .Split o m → σ .arities o → Type ℓP

    -- slots never grow ...
    deg≤ : (o : σ .ops) (m : fib .carrier (σ .resultSort o))
           (sp : fib .Split o m) (a : σ .arities o)
         → deg _ (fib .parts o m sp a) ≤ deg _ m

    -- ... and a proper slot strictly shrinks
    deg< : (o : σ .ops) (m : fib .carrier (σ .resultSort o))
           (sp : fib .Split o m) (a : σ .arities o)
         → Proper o m sp a
         → deg _ (fib .parts o m sp a) < deg _ m

open GradedFib public

-- ==================================================================
-- THE GRADING, UNBUNDLED -- a structure OVER a promodel, exactly as
-- `Focus` is, and for the same reason.
--
-- `GradedFib` bundles the promodel, which makes one thing UNSTATABLE:
-- "for every grading of THIS promodel".  That quantification is what the
-- obstruction theorems need -- `Instances/Group/NoGrading` wants to say
-- ℤ admits only the degenerate grading, and with the bundled record it
-- had to unbundle into four module parameters and rebuild `GradedFib` by
-- hand at every use.  Both the group and the ring instance did exactly
-- that, independently, which is the signal that the record is shaped
-- wrong.
--
-- Note this does NOT say "ℤ has no grading": the trivial grading
-- (`deg = const 0`, `Proper = ⊥`) always exists, so the honest theorem is
-- RIGIDITY -- that it is the only one.  Stating rigidity is precisely
-- what needs the quantifier this record provides.
-- ==================================================================

record Grading {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (Fib : Fibered σ ℓX ℓP)
  : Type (ℓ-max ℓS (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓX (ℓ-suc ℓP))))) where
  field
    deg    : (s : S) → Fib .carrier s → ℕ
    Proper : (o : σ .ops) (m : Fib .carrier (σ .resultSort o))
           → Fib .Split o m → σ .arities o → Type ℓP
    deg≤   : (o : σ .ops) (m : Fib .carrier (σ .resultSort o))
             (sp : Fib .Split o m) (a : σ .arities o)
           → deg _ (Fib .parts o m sp a) ≤ deg _ m
    deg<   : (o : σ .ops) (m : Fib .carrier (σ .resultSort o))
             (sp : Fib .Split o m) (a : σ .arities o)
           → Proper o m sp a
           → deg _ (Fib .parts o m sp a) < deg _ m

open Grading public

-- The two presentations are the same data, and both directions are
-- definitional -- there is no content here, only shape.
gradingOf : {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
            (GS : GradedFib σ ℓX ℓP) → Grading (GS .fib)
gradingOf GS .deg    = GS .deg
gradingOf GS .Proper = GS .Proper
gradingOf GS .deg≤   = GS .deg≤
gradingOf GS .deg<   = GS .deg<

graded : {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
         (Fib : Fibered σ ℓX ℓP) → Grading Fib → GradedFib σ ℓX ℓP
graded Fib G .fib    = Fib
graded Fib G .deg    = G .deg
graded Fib G .Proper = G .Proper
graded Fib G .deg≤   = G .deg≤
graded Fib G .deg<   = G .deg<

-- ==================================================================
-- ▷, next, löb -- first-order, exactly as Grammar/Later/Ordered.agda
-- hand-collapses ccl's presheaf ▷.
-- ==================================================================

module Grade {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
             (GS : GradedFib σ ℓX ℓP) (ℓA : Level)
             (X : Type ℓV) (xs : X → S) where

  open Ind (GS .fib) ℓA X xs public

  degIx : Ix → ℕ
  degIx (x , m) = GS .deg (xs x) m

  _≺_ : Ix → Ix → Type
  i ≺ j = degIx i < degIx j

  private
    ≺-wf : WellFounded _≺_
    ≺-wf i = go (degIx i) (<-wellfounded (degIx i)) i refl
      where
        go : (n : ℕ) → Acc _<_ n → (j : Ix) → degIx j ≡ n → Acc _≺_ j
        go n (acc h) j p =
          acc λ k q → go (degIx k) (h (degIx k) (subst (degIx k <_) p q)) k refl

  -- the graded order is one instance of `WFLater`; ▷/next/löb come
  -- from there rather than being re-defined here
  open WFLater _≺_ ≺-wf public

  -- ================================================================
  -- Guardedness.
  -- ================================================================

  Guarded≤ : {s : S} → Functor s → Type (ℓ-max ℓX (ℓ-max ℓSh ℓPos))
  Guarded≤ {s} F = (m : GS .fib .carrier s) (sh : Sh F m) (p : Pos F m sh)
                 → degIx (nx F m sh p) ≤ GS .deg s m

  Guarded : {s : S} → Functor s → Type (ℓ-max ℓX (ℓ-max ℓSh ℓPos))
  Guarded {s} F = (m : GS .fib .carrier s) (sh : Sh F m) (p : Pos F m sh)
                → degIx (nx F m sh p) < GS .deg s m

  Guarded→≤ : {s : S} {F : Functor s} → Guarded F → Guarded≤ F
  Guarded→≤ g m sh p = <-weaken (g m sh p)

  -- every former is non-increasing ...
  ≤⌜⌝ : {s : S} (A : FibNotation.TheoryTy (GS .fib) ℓA s) → Guarded≤ ⌜ A ⌝
  ≤⌜⌝ A m sh ()

  ≤Var : (x : X) → Guarded≤ (Var x)
  ≤Var x m sh p = ≤-refl

  ≤⊕e : {s : S} (Y : Type ℓA) (G : Y → Functor s)
      → ((y : Y) → Guarded≤ (G y)) → Guarded≤ (⊕e Y G)
  ≤⊕e Y G g m (y , sh) p = g y m sh p

  ≤&e : {s : S} (Y : Type ℓA) (G : Y → Functor s)
      → ((y : Y) → Guarded≤ (G y)) → Guarded≤ (&e Y G)
  ≤&e Y G g m sh (y , p) = g y m (sh y) p

  ≤⊗e : (o : σ .ops) (G : (a : σ .arities o) → Functor (σ .sortOf o a))
      → ((a : σ .arities o) → Guarded≤ (G a)) → Guarded≤ (⊗e o G)
  ≤⊗e o G g m (sp , sh) (a , p) =
    ≤-trans (g a _ (sh a) p) (GS .deg≤ o m sp a)

  -- ... and ⊗e at a proper splitting is the one STRICT step.
  <⊗e : (o : σ .ops) (G : (a : σ .arities o) → Functor (σ .sortOf o a))
      → ((a : σ .arities o) → Guarded≤ (G a))
      → ((m : GS .fib .carrier (σ .resultSort o)) (sp : GS .fib .Split o m)
         (sh : (a : σ .arities o) → Sh (G a) (GS .fib .parts o m sp a))
         (a : σ .arities o) → Pos (G a) _ (sh a) → Proper GS o m sp a)
      → Guarded (⊗e o G)
  <⊗e o G g pr m (sp , sh) (a , p) =
    ≤<-trans (g a _ (sh a) p) (GS .deg< o m sp a (pr m sp sh a p))

