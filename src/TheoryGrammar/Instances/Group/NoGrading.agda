{- A NONTRIVIAL GROUP ADMITS NO USEFUL GRADING. This is a boundary marker:
   the framework should be able to say which algebraic structures give good
   grammar theories, and this file says which ones do NOT. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Group.NoGrading where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded

private variable ℓ ℓ' ℓX ℓP ℓA ℓM ℓV ℓQ : Level

private
  -- two functions out of an empty domain agree
  ⊥ext : {P : Type ℓQ} {B : P → Type ℓM}
         (np : P → ⊥) (f g : (p : P) → B p) → f ≡ g
  ⊥ext np f g = funExt λ p → E.rec (np p)

-- PART A. A grading whose degree is constant is unusable.

module Degenerate {σ : SortedSig Unit ℓ ℓ'}
                  (GS : GradedFib σ ℓX ℓP)
                  (deg-const : (m m' : GS .fib .carrier tt)
                             → GS .deg tt m ≡ GS .deg tt m')
  where

  -- THEOREM.  No splitting has a proper slot, at any operation.
  no-proper : (o : σ .ops) (m : GS .fib .carrier (σ .resultSort o))
              (sp : GS .fib .Split o m) (a : σ .arities o)
            → Proper GS o m sp a → ⊥
  no-proper o m sp a pr =
    ¬m<m (subst (λ n → n < GS .deg tt m)
                (deg-const (GS .fib .parts o m sp a) m)
                (GS .deg< o m sp a pr))

  -- The consequence for descriptions.

  module AtFunctors (ℓA ℓV : Level) (V : Type ℓV) (vs : V → Unit) where

    open Guard GS ℓA V vs public

    -- THEOREM. A guarded description has NO recursive positions.
    no-guarded : {s : Unit} (F : Functor s) (m : GS .fib .carrier s)
                 (sh : Sh F m) → Guarded F → Pos F m sh → ⊥
    no-guarded F m sh gF p =
      ¬m<m (subst (λ n → n < GS .deg tt m)
                  (deg-const (nx F m sh p .snd) m)
                  (gF m sh p))

    -- `Var` -- i.e. ANY recursive reference -- is never guarded.
    no-guarded-Var : (x : V) (m : GS .fib .carrier (vs x))
                   → Guarded (Var x) → ⊥
    no-guarded-Var x m g = no-guarded (Var x) m tt* g tt*

    -- ... and neither is a convolution with a recursive slot.  This is
    -- exactly the premise `<⊗e` / `⊗-guard` demand, refuted.
    no-guarded-⊗e : (o : σ .ops)
                    (G : (a : σ .arities o) → Functor (σ .sortOf o a))
                    (m : GS .fib .carrier (σ .resultSort o))
                    (sp : GS .fib .Split o m)
                    (sh : (a : σ .arities o) → Sh (G a) (GS .fib .parts o m sp a))
                    (a : σ .arities o) → Pos (G a) _ (sh a)
                  → Guarded (⊗e o G) → ⊥
    no-guarded-⊗e o G m sp sh a p g = no-guarded (⊗e o G) m (sp , sh) g (a , p)

    -- `slotProper` (Graded.agda, "Way 2") is unusable: its `Proper`
    -- premise is uninhabited.
    no-slotProper : (o : σ .ops) (m : GS .fib .carrier (σ .resultSort o))
                    (sp : GS .fib .Split o m) (a : σ .arities o)
                  → Proper GS o m sp a → ⊥
    no-slotProper = no-proper

    -- So a guarded description is not a description of anything
    -- recursive: its interpretation does not depend on the motive.

    guarded→const : {s : Unit} (F : Functor s) (gF : Guarded F)
                    {A : Ix → Type ℓM} (m : GS .fib .carrier s)
                  → Iso (⟦ F ⟧ A m) (Sh F m)
    guarded→const F gF m .Iso.fun = fst
    guarded→const F gF m .Iso.inv sh = sh , λ p → E.rec (no-guarded F m sh gF p)
    guarded→const F gF m .Iso.sec sh = refl
    guarded→const F gF m .Iso.ret (sh , f) =
      cong (sh ,_) (⊥ext (no-guarded F m sh gF) _ f)

    -- ... and its least fixed point has depth one.  "There are no
    -- well-founded inductive types over a group-like `Fibered`" in its
    -- sharpest form: `μ` degenerates to its own shape functor.
    μ-noRec : (F : (x : V) → Functor (vs x)) (gF : (x : V) → Guarded (F x))
              (x : V) (m : GS .fib .carrier (vs x))
            → Iso (μ F (x , m)) (Sh (F x) m)
    μ-noRec F gF x m .Iso.fun (sup sh f) = sh
    μ-noRec F gF x m .Iso.inv sh = sup sh λ p → E.rec (no-guarded (F x) m sh (gF x) p)
    μ-noRec F gF x m .Iso.sec sh = refl
    μ-noRec F gF x m .Iso.ret (sup sh f) =
      cong (sup sh) (⊥ext (no-guarded (F x) m sh (gF x)) _ f)

-- PART B.  Group-likeness, and the rigidity theorem.

-- "Every element occurs in slot `a` of some splitting of every `m`." For a
-- group under `·` at the left slot this is witnessed by `m = h · (h⁻¹ m)`.
GroupLike : {σ : SortedSig Unit ℓ ℓ'} (Fib : Fibered σ ℓX ℓP)
            (o : σ .ops) (a : σ .arities o) → Type (ℓ-max ℓX ℓP)
GroupLike {σ = σ} Fib o a =
  (m : Fib .carrier (σ .resultSort o)) (h : Fib .carrier (σ .sortOf o a))
  → Σ[ sp ∈ Fib .Split o m ] (Fib .parts o m sp a ≡ h)

module GroupObstruction {σ : SortedSig Unit ℓ ℓ'}
                        (GS : GradedFib σ ℓX ℓP)
                        (o : σ .ops) (a : σ .arities o)
                        (gl : GroupLike (GS .fib) o a)
  where

  private
    -- `deg≤` at a group-like slot says: deg x ≤ deg y for ARBITRARY
    -- x and y, because x is a slot of some splitting of y.
    bound : (x y : GS .fib .carrier tt) → GS .deg tt x ≤ GS .deg tt y
    bound x y =
      subst (λ z → GS .deg tt z ≤ GS .deg tt y)
            (gl y x .snd)
            (GS .deg≤ o y (gl y x .fst) a)

  -- THEOREM.  The degree is constant.  (Antisymmetry of ≤ on ℕ.)
  deg-const : (m m' : GS .fib .carrier tt) → GS .deg tt m ≡ GS .deg tt m'
  deg-const m m' = ≤-antisym (bound m m') (bound m' m)

  -- ... hence everything in Part A.
  open Degenerate GS deg-const public
