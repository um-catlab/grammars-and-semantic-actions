{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Mergesort: both halves recurse, so guardedness is the uniform rule `<⊗e`
   -- unlike quicksort, whose two slots need different certificates. -}
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

-- `Small`, `NonTrivial` and `ntCons` are theory facts, from `Graded`.

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

-- PRIMITIVE (phase 1): mergesort's `outQ`.  Generic in the motive, so
-- all three algebras below share it.
outM : (B : Fam)
     → ⟦ MAlt false ⟧ᴳ B
     ⊢ ((B tt & Liftg NonTrivial) ⊗' (B tt & Liftg NonTrivial))
outM B w ((u , v , s) , h) =
  ⊗-mk s (h true true , h true false) (h false true , h false false)

-- the nonemptiness witnesses are there for `mfGuarded` and nothing
-- else; `&-E₁` is the discard
dropNT : (B : Fam)
       → ((B tt & Liftg NonTrivial) ⊗' (B tt & Liftg NonTrivial))
       ⊢ (B tt ⊗' B tt)
dropNT B = ⊗-map &-E₁ &-E₁

-- alternating deal; used only to build the splitting
dealt : (m : Bag) → Σ[ u ∈ Bag ] Σ[ v ∈ Bag ] Ilv u v m
dealt []      = [] , [] , nil
dealt (x ∷ m) = let (u , v , s) = dealt m in (x ∷ v) , u , left (ilvSwap s)

-- PRIMITIVE (phase 1).  Decomposition: a bag is small, or it deals
-- into two nonempty halves.  Not a `Cover`, because the nonemptiness
-- witnesses that make the splitting proper travel in the shape.
mcoalg : Coalgᴳ MF (λ _ → ⊤G)
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

  -- the base case, at the two representables `Small` is built from
  smallBag : Small ⊢ CBag
  smallBag = ⊕-E (⌈⌉-E []) (⊕ᴰ-E λ x → ⌈⌉-E (x ∷ []))

  -- SEMANTIC ACTION: the carrier is constant, so `mergePerm` becomes a
  -- separate obligation.  `mergeG` below is what makes it unnecessary.
  mergeBag : (CBag ⊗' CBag) ⊢ CBag
  mergeBag w =
    ⊗E {P = λ b → if b then CBag else CBag} {w = w} λ _ _ _ a b → merge a b

  malg : AlgC MF (λ _ → Bag)
  malg tt =
    ⊕ᴰ-E λ { true  → smallBag ∘g lowerg
           ; false → mergeBag ∘g dropNT (λ _ → CBag) ∘g outM (λ _ → CBag) }

  -- The plain sort, still a term: `Δ Bag` carries the answer and `run` is
  -- the single exit, in a test.
  msortP : ⊤G ⊢ Δ Bag
  msortP = intoΔ Bag ∘g hyloᴳ mfGuarded mcoalg malg tt

-- MERGE AS AN INTERNAL TERM. `Bagged m` is "a listing of `m`", and it is
-- quicksort's `SpecG` on the nose -- the two sorters share a specification
-- and its monoid, and differ only in the join.
Bagged : Gr
Bagged = SpecG

BaggedIx : Ix → Type₀
BaggedIx i = Bagged (i .snd)

module MSortV (le : A → A → Bool) where

  open MSort le

  -- `merge` only reorders
  mergePerm : (a b : Bag) → Perm (merge a b) (a ++ b)
  mergePerm []      b  = permRefl b
  mergePerm (x ∷ a) [] =
    subst (Perm (x ∷ a)) (sym (++-unit-r (x ∷ a))) (permRefl (x ∷ a))
  mergePerm (x ∷ a) (y ∷ b) =
    go (le x y) (mergePerm a (y ∷ b)) (mergePerm (x ∷ a) b)
    where
      -- both recursive results are ARGUMENTS: a `with` would hide the
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

  -- PRIMITIVE (phase 1): it matches the splitting, which is what a
  -- primitive is; every use downstream composes it.
  mergeG : (Bagged ⊗' Bagged) ⊢ Bagged
  mergeG w ((u , v , s) , h) = mergeAt s (h true) (h false)

  -- the unit and singleton of quicksort's monoid; nothing new to prove
  smallBagged : Small ⊢ Bagged
  smallBagged = ⊕-E nilSpec (⊕ᴰ-E unitSpec)

  malgV : Algᴳ MF (λ _ → Bagged)
  malgV tt =
    ⊕ᴰ-E λ { true  → smallBagged ∘g lowerg
           ; false → mergeG ∘g dropNT (λ _ → Bagged) ∘g outM (λ _ → Bagged) }

  -- MERGESORT, as a term of the calculus, permutation-correct by type
  mergesortV : ⊤G ⊢ Bagged
  mergesortV = hyloᴳ mfGuarded mcoalg malgV tt
