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
import Cubical.Data.Equality as Eq
open import Cubical.Data.Sum using (_⊎_; inl; inr)

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded

open import TheoryGrammar.Instances.Bags.Quicksort A public

-- `NonTrivial` comes from Graded.  `Small` is its internal complement:
-- empty, or a single atom -- no length anywhere.
Small : Gr
Small = ⌈ [] ⌉ ⊕ ⊕ᴰ A (λ x → ⌈ x ∷ [] ⌉)

-- a non-trivial bag, from its first element
ntCons : (x : A) (u : Bag) → NonTrivial (x ∷ u)
ntCons x u = x , ⊗-mk (left (ilvApp [] u)) Eq.refl tt

-- each half is a recursive occurrence TOGETHER WITH a proof it is
-- nonempty; the proof is what makes the splitting proper
MSlot : Bool → Functor tt
MSlot true  = Var tt
MSlot false = ⌜ NonTrivial ⌝

MHalf : Functor tt
MHalf = &e Bool MSlot

MAlt : Bool → Functor tt
MAlt true  = ⌜ Small ⌝
MAlt false = ⊗e appop (λ _ → MHalf)

MF : Unit → Functor tt
MF _ = ⊕e Bool MAlt

≤MSlot : (b : Bool) → Guarded≤ (MSlot b)
≤MSlot true  = ≤Var tt
≤MSlot false = ≤⌜⌝ NonTrivial

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

mcoalg : CoalgC MF (λ _ → Unit)
mcoalg tt []          _ = true , lift (inl Eq.refl)
mcoalg tt (x ∷ [])    _ = true , lift (inr (x , Eq.refl))
mcoalg tt (x ∷ y ∷ r) _ = false , mkSplit
  where
    d = dealt r
    mkSplit : ⟦ MAlt false ⟧c (λ _ → Unit) (x ∷ y ∷ r)
    mkSplit = ⊗I {P = λ _ → ⟦ MHalf ⟧c (λ _ → Unit)}
               (left (right (d .snd .snd)))
               (λ { true → tt ; false → lift (ntCons x (d .fst)) })
               (λ { true → tt ; false → lift (ntCons y (d .snd .fst)) })

module MSort (le : A → A → Bool) where

  merge : Bag → Bag → Bag
  merge []      b       = b
  merge (x ∷ a) []      = x ∷ a
  merge (x ∷ a) (y ∷ b) =
    if le x y then x ∷ merge a (y ∷ b) else y ∷ merge (x ∷ a) b

  malg : AlgC MF (λ _ → Bag)
  malg tt =
    ⊕ᴰ-E λ { true  → λ w _ → w
              ; false → λ w t →
                  ⊗E {P = λ _ → ⟦ MHalf ⟧c (λ _ → Bag)} {w = w}
                     (λ _ _ _ l r → merge (l true) (r true)) t }

  mergesort : Bag → Bag
  mergesort m = hyloC mfGuarded mcoalg malg (tt , m) tt

-- ==================================================================
-- MERGE AS AN INTERNAL TERM, and mergesort as a Cover.
--
-- `Bagged m` is "a listing of the bag `m`".  Since `_⊢_` preserves the
-- index and `⊗ˢ` splits it, a term
--
--     mergeG : (Bagged ⊗ Bagged) ⊢ Bagged
--
-- cannot invent or drop elements: permutation-correctness is carried by
-- the type rather than proved afterwards.  What it costs is the three
-- lemmas in `Permutation` -- `permRefl`, `permInsert`, `permTrans` --
-- because `merge a b` REORDERS `a ++ b` rather than being it.
-- ==================================================================

Bagged : Gr
Bagged m = Σ[ out ∈ Bag ] Perm out m

BaggedIx : Ix → Type₀
BaggedIx i = Bagged (i .snd)

module MSortV (le : A → A → Bool) where

  open MSort le

  -- `merge` only reorders
  mergePerm : (a b : Bag) → Perm (merge a b) (a ++ b)
  mergePerm []      b  = permRefl b
  mergePerm (x ∷ a) [] =
    subst (Perm (x ∷ a)) (sym (++-unit-r (x ∷ a))) (permRefl (x ∷ a))
  -- the branch is an ARGUMENT, not a `with`: `with` hides the
  -- lexicographic descent from the termination checker
  mergePerm (x ∷ a) (y ∷ b) =
    go (le x y) (mergePerm a (y ∷ b)) (mergePerm (x ∷ a) b)
    where
      -- both recursive results are ARGUMENTS, exactly as `merge`'s own
      -- `if` makes them; a `with` or a nullary `where` hides the
      -- lexicographic descent from the termination checker
      go : (bl : Bool)
         → Perm (merge a (y ∷ b)) (a ++ (y ∷ b))
         → Perm (merge (x ∷ a) b) ((x ∷ a) ++ b)
         → Perm (if bl then x ∷ merge a (y ∷ b) else y ∷ merge (x ∷ a) b)
                ((x ∷ a) ++ (y ∷ b))
      go true  p q = cons p (left (ilvApp [] (a ++ (y ∷ b))))
      go false p q = cons q (ilvAfter (x ∷ a) b y)

  mergeAt : ∀ {u v w} → Ilv u v w → Bagged u → Bagged v → Bagged w
  mergeAt s (a , pa) (b , pb) =
    merge a b , permTrans (mergePerm a b) (permMerge pa pb s)

  -- the internal term
  mergeG : (Bagged ⊗' Bagged) ⊢ Bagged
  mergeG w ((u , v , s) , h) = mergeAt s (h true) (h false)

  malgV : AlgC MF BaggedIx
  malgV tt =
    ⊕ᴰ-E λ { true  → λ w _ → w , permRefl w
           ; false → λ w t →
               ⊗E {P = λ _ → ⟦ MHalf ⟧c BaggedIx} {w = w}
                  (λ u v s l r → mergeAt s (l true) (r true)) t }

  -- MERGESORT, as a term of the calculus, permutation-correct by type
  mergesortV : ⊤G ⊢ Bagged
  mergesortV m _ = hyloC mfGuarded mcoalg malgV (tt , m) tt
