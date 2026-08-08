{- CHECK 3: local contractivity, and the hylomorphism. -}
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

-- A `Fibered` with a grading.

record GradedFib {S : Type ℓS} (σ : SortedSig S ℓ ℓ') ℓX ℓP
  : Type (ℓ-max ℓS (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max (ℓ-suc ℓX) (ℓ-suc ℓP))))) where
  field
    fib : Fibered σ ℓX ℓP
    deg : (s : S) → fib .carrier s → ℕ

    -- Properness is DATA ON THE SPLITTING. Phrasing it this way dodges
    -- "some slot other than a", and hence dodges needing `Discrete
    -- (arities o)` -- the same problem `Focus` was introduced to avoid.
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

-- THE GRADING, UNBUNDLED -- a structure OVER a `Fibered`, exactly as
-- `Focus` is, and for the same reason.

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

-- ▷, next, löb -- first-order, exactly as Grammar/Later/Ordered.agda
-- hand-collapses ccl's presheaf ▷.

module Grade {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
             (GS : GradedFib σ ℓX ℓP) (ℓA : Level)
             (X : Type ℓV) (xs : X → S) where

  -- `Ind` at an ℓA WIDE ENOUGH TO ABSORB ℓV and ℓX.
  ℓA⁺ : Level
  ℓA⁺ = ℓ-max ℓA (ℓ-max ℓV ℓX)

  open Ind (GS .fib) ℓA⁺ X xs public

  -- THE FIXED POINT IN CONNECTIVE FORM -- generic at last, AND A TERM.

  open FibNotation (GS .fib) using (_⊢_)

  module _ (F : (x : X) → Functor (xs x)) where

    unrollg : (x : X) → (λ m → μ F (x , m)) ⊢ ⟦ F x ⟧c (μ F)
    unrollg x m t = toC (F x) m (unroll t)

    rollg : (x : X) → ⟦ F x ⟧c (μ F) ⊢ (λ m → μ F (x , m))
    rollg x m t = roll (fromC (F x) m t)

    -- NOTE: the round trip `rollg ∘ unrollg ≡ id` is NOT stated here.

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

  -- Guardedness.

  Guarded≤ : {s : S} → Functor s → Type (ℓ-max ℓX (ℓ-max ℓSh ℓPos))
  Guarded≤ {s} F = (m : GS .fib .carrier s) (sh : Sh F m) (p : Pos F m sh)
                 → degIx (nx F m sh p) ≤ GS .deg s m

  Guarded : {s : S} → Functor s → Type (ℓ-max ℓX (ℓ-max ℓSh ℓPos))
  Guarded {s} F = (m : GS .fib .carrier s) (sh : Sh F m) (p : Pos F m sh)
                → degIx (nx F m sh p) < GS .deg s m

  Guarded→≤ : {s : S} {F : Functor s} → Guarded F → Guarded≤ F
  Guarded→≤ g m sh p = <-weaken (g m sh p)

  -- every former is non-increasing ...
  ≤⌜⌝ : {s : S} (A : FibNotation.TheoryTy (GS .fib) ℓA⁺ s) → Guarded≤ ⌜ A ⌝
  ≤⌜⌝ A m sh ()

  ≤Var : (x : X) → Guarded≤ (Var x)
  ≤Var x m sh p = ≤-refl

  ≤⊕e : {s : S} (Y : Type ℓA⁺) (G : Y → Functor s)
      → ((y : Y) → Guarded≤ (G y)) → Guarded≤ (⊕e Y G)
  ≤⊕e Y G g m (y , sh) p = g y m sh p

  ≤&e : {s : S} (Y : Type ℓA⁺) (G : Y → Functor s)
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

