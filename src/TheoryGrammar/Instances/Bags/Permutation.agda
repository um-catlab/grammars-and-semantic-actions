{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Permutation, built from the promodel's own insertion relation. -}
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

ilvAssoc : ∀ {p q r u w} → Ilv p u w → Ilv q r u
         → Σ[ y ∈ Bag ] (Ilv q y w × Ilv p r y)
ilvAssoc nil       nil        = [] , nil , nil
ilvAssoc (left s)  t          =
  let (y , e1 , e2) = ilvAssoc s t in _ , right e1 , left e2
ilvAssoc (right s) (left t)   =
  let (y , e1 , e2) = ilvAssoc s t in _ , left e1 , e2
ilvAssoc (right s) (right t)  =
  let (y , e1 , e2) = ilvAssoc s t in _ , right e1 , right e2

-- Permutations merge along an interleaving.  The only lemma the
-- intrinsic proof needs, and it is discharged by `ilvAssoc` + `ilvSwap`
-- -- i.e. entirely by the promodel's own structure.
permMerge : ∀ {a u b v w} → Perm a u → Perm b v → Ilv u v w → Perm (a ++ b) w
permMerge nil q s with ilvNilL s
... | Eq.refl = q
permMerge (cons p ins) q s =
  let (y , e1 , e2) = ilvAssoc (ilvSwap s) ins
  in cons (permMerge p q (ilvSwap e2)) e1

-- THE TWO PRIMITIVES.

-- (1) DECOMPOSITION.  Every bag is empty or has a distinguished
