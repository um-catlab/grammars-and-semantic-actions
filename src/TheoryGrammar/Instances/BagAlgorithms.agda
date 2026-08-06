{-
  MERGESORT and QUICKSELECT over bags, on the same machinery as
  quicksort.  The point is that they exercise DIFFERENT parts of it.

  MERGESORT splits into two halves, both of which are recursive.  Both
  slots are proper parts, so guardedness is discharged by the UNIFORM
  rule `<⊗e` -- the one that was too weak for quicksort.  The price is
  that the description must carry the nonemptiness of each half
  (`Var & NonEmpty`), because a splitting alone does not force it: a
  singleton has no two-nonempty-part split, which is exactly why
  mergesort needs a `length ≤ 1` base case and quicksort does not.

  QUICKSELECT recurses into ONE side, so its description branches on
  which.  Its guardedness is uniform too, because in both branches the
  pivot sits in the non-recursive factor.  It also shows the motive
  carrying data downwards: the coalgebra passes a RANK to the recursive
  position, so `A` is `λ _ → ℕ` rather than `λ _ → Unit`.

  Together with quicksort:
      quicksort   two recursive slots, discharged two different ways
      mergesort   two recursive slots, both by properness
      quickselect one recursive slot, chosen by the coalgebra
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.BagAlgorithms where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.List
open import Cubical.Data.Maybe
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Substrate
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded
open import TheoryGrammar.Instances.Bags

module Sorts (A : Type₀) (le : A → A → Bool) where

  open Bags A public

  -- ================================================================
  -- MERGESORT.
  -- ================================================================

  NonEmpty : Gr
  NonEmpty m = 0 < length m

  Small : Gr
  Small m = length m ≤ 1

  -- each half is a recursive occurrence TOGETHER WITH a proof it is
  -- nonempty; the proof is what makes the splitting proper
  MSlot : Bool → Functor tt
  MSlot true  = Var tt
  MSlot false = ⌜ NonEmpty ⌝

  MHalf : Functor tt
  MHalf = &e Bool MSlot

  MAlt : Bool → Functor tt
  MAlt true  = ⌜ Small ⌝
  MAlt false = ⊗e appop (λ _ → MHalf)

  MF : Unit → Functor tt
  MF _ = ⊕e Bool MAlt

  ≤MSlot : (b : Bool) → Guarded≤ (MSlot b)
  ≤MSlot true  = ≤Var tt
  ≤MSlot false = ≤⌜⌝ NonEmpty

  mfGuarded : (x : Unit) → Guarded (MF x)
  mfGuarded tt = <⊕e Bool MAlt alt
    where
      pr : (m : Bag) (sp : MonSplit appop m)
           (sh : (a : Bool) → Sh MHalf (MonParts appop m sp a))
           (a : Bool) → Pos MHalf _ (sh a) → Proper' appop m sp a
      pr m (u , v , s) sh true  p = lower (sh false false)
      pr m (u , v , s) sh false p = lower (sh true false)

      alt : (b : Bool) → Guarded (MAlt b)
      alt true  = <⌜⌝ Small
      alt false = <⊗e appop (λ _ → MHalf)
                      (λ _ → ≤&e Bool MSlot ≤MSlot) pr

  -- alternating deal; used only to build the splitting
  dealt : (m : Bag) → Σ[ u ∈ Bag ] Σ[ v ∈ Bag ] Ilv u v m
  dealt []      = [] , [] , nil
  dealt (x ∷ m) = let (u , v , s) = dealt m in (x ∷ v) , u , left (ilvSwap s)

  0<suc : {n : ℕ} → 0 < suc n
  0<suc = suc-≤-suc zero-≤

  mcoalg : CoalgC MF (λ _ → Unit)
  mcoalg tt []          _ = true , lift zero-≤
  mcoalg tt (x ∷ [])    _ = true , lift ≤-refl
  mcoalg tt (x ∷ y ∷ r) _ = false , mkSplit
    where
      d = dealt r
      mkSplit : ⟦ MAlt false ⟧c (λ _ → Unit) (x ∷ y ∷ r)
      mkSplit = ⊗I {P = λ _ → ⟦ MHalf ⟧c (λ _ → Unit)}
                 (left (right (d .snd .snd)))
                 (λ { true → tt ; false → lift 0<suc })
                 (λ { true → tt ; false → lift 0<suc })

  merge : Bag → Bag → Bag
  merge []      b       = b
  merge (x ∷ a) []      = x ∷ a
  merge (x ∷ a) (y ∷ b) =
    if le x y then x ∷ merge a (y ∷ b) else y ∷ merge (x ∷ a) b

  malg : AlgC MF (λ _ → Bag)
  malg tt =
    ⊕ᴰ-elim λ { true  → λ w _ → w
              ; false → λ w t →
                  ⊗E {P = λ _ → ⟦ MHalf ⟧c (λ _ → Bag)} {w = w}
                     (λ _ _ _ l r → merge (l true) (r true)) t }

  mergesort : Bag → Bag
  mergesort m = hyloC mfGuarded mcoalg malg (tt , m) tt


module MTest where
  leℕ : ℕ → ℕ → Bool
  leℕ zero    _       = true
  leℕ (suc m) zero    = false
  leℕ (suc m) (suc n) = leℕ m n

  open Sorts ℕ leℕ

  _ : mergesort (5 ∷ 3 ∷ 4 ∷ 1 ∷ 2 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
  _ = refl

  _ : mergesort (2 ∷ 2 ∷ 1 ∷ []) ≡ (1 ∷ 2 ∷ 2 ∷ [])
  _ = refl
