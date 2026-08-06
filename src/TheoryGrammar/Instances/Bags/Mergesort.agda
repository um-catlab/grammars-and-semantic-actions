{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Mergesort: both halves recurse, so guardedness is the uniform rule
   `<⊗e` -- unlike quicksort, whose two slots need different certificates.
   The price is that the description must carry each half's nonemptiness,
   which is why mergesort needs a `length ≤ 1` base case and quicksort
   does not. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Bags.Mergesort (A : Type₀) where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.List

open import TheoryGrammar.Base
open import TheoryGrammar.Substrate
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded

open import TheoryGrammar.Instances.Bags.Quicksort A public

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

module MSort (le : A → A → Bool) where

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
