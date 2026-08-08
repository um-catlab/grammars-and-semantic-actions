{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Permutation, built from the `Fibered`'s own insertion relation. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Bags.Permutation (A : Type₀) where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.List
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded

open import TheoryGrammar.Instances.Bags.Graded A public

data Perm : Bag → Bag → Type₀ where
  nil  : Perm [] []
  cons : ∀ {x u v w} → Perm u v → Ilv (x ∷ []) v w → Perm (x ∷ u) w

ilvNilL : ∀ {v w} → Ilv [] v w → v Eq.≡ w
ilvNilL nil = Eq.refl
ilvNilL (right s) with ilvNilL s
... | Eq.refl = Eq.refl

-- Permutations merge along an interleaving.  The only lemma the
-- intrinsic proof needs, and it is discharged by `ilvAssoc` + `ilvSwap`
-- -- i.e. entirely by the `Fibered`'s own structure.
permMerge : ∀ {a u b v w} → Perm a u → Perm b v → Ilv u v w → Perm (a ++ b) w
permMerge nil q s with ilvNilL s
... | Eq.refl = q
permMerge (cons p ins) q s =
  let (y , e1 , e2) = ilvAssoc (ilvSwap s) ins
  in cons (permMerge p q (ilvSwap e2)) e1

-- THE TWO PRIMITIVES.

-- (1) DECOMPOSITION.  Every bag is empty or has a distinguished

-- The permutation theory `merge` needs.  `permMerge` above handles
-- CONCATENATION; making `merge` internal additionally needs that
-- permutations compose and that an insertion survives one.

permRefl : (m : Bag) → Perm m m
permRefl []      = nil
permRefl (x ∷ m) = cons (permRefl m) (left (ilvApp [] m))

-- inserting `y` after a prefix
ilvAfter : (u v : Bag) (y : A) → Ilv (y ∷ []) (u ++ v) (u ++ (y ∷ v))
ilvAfter []      v y = left (ilvApp [] v)
ilvAfter (c ∷ u) v y = right (ilvAfter u v y)

-- an insertion survives a permutation of the whole
permInsert : ∀ {x v w c} → Ilv (x ∷ []) v w → Perm w c
           → Σ[ v' ∈ Bag ] (Perm v v' × Ilv (x ∷ []) v' c)
permInsert ins        nil          = E.rec (noIlv ins)
  where noIlv : ∀ {x v} → Ilv (x ∷ []) v [] → ⊥
        noIlv ()
permInsert (left ins) (cons p i')  = _ , subst (λ z → Perm z _) (Eq.eqToPath (Eq.sym (ilvNilL ins))) p , i'
permInsert (right ins) (cons p i') =
  let (v₁ , pv , iv) = permInsert ins p
      (v'' , ic , iy) = ilvAssoc i' iv
  in v'' , cons pv iy , ic

permTrans : ∀ {a b c} → Perm a b → Perm b c → Perm a c
permTrans nil        nil = nil
permTrans (cons p i) q   =
  let (v' , pv , iv) = permInsert i q
  in cons (permTrans p pv) iv

-- LISTINGS, AND THEIR MONOID. `SpecG m` is "a listing of the bag `m`" --
-- the specification both sorters are written against.

SpecG : Gr
SpecG m = Σ[ out ∈ Bag ] Perm out m

Spec : Ix → Type₀
Spec (_ , m) = SpecG m

-- the multiplication is `permMerge`; the two units are `⌈⌉-E`
appendSpec : (SpecG ⊗' SpecG) ⊢ SpecG
appendSpec w ((u , v , s) , h) =
  (h true .fst ++ h false .fst) , permMerge (h true .snd) (h false .snd) s

nilSpec : ⌈ [] ⌉ ⊢ SpecG
nilSpec = ⌈⌉-E ([] , nil)

unitSpec : (a : A) → ⌈ a ∷ [] ⌉ ⊢ SpecG
unitSpec a = ⌈⌉-E ((a ∷ []) , permRefl (a ∷ []))

-- the constant carrier, for contrast: nothing indexes it, so a term
-- into it may return any bag at all
CBag : Gr
CBag _ = Bag
