{- `emp` IS THE REPRESENTABLE AT THE EMPTY HEAP. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Heap.Emp where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Unit
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Precision using (coeEq)

open import TheoryGrammar.Instances.Heap.Connectives public

-- The two spellings of `emp`.

-- `empR` DENOTES "I own nothing": the representable at the empty heap.
empR : Gr
empR = ⌈ [] ⌉

-- reads the PRIMITIVE `IsNil`, which is `⊥` at a cons
emp⊢empR : emp ⊢ empR
emp⊢empR []      _        = Eq.refl
emp⊢empR (_ ∷ _) (sp , _) = E.rec sp

empR⊢emp : empR ⊢ emp
empR⊢emp = ⌈⌉-E {a = []} {B = emp} (tt , λ ())

-- `l ↦ x` DENOTES "I own exactly the cell at l, and it holds x" -- the
-- representable at the one-cell heap.  Exclusive ownership is not an
-- extra clause: a representable pins the WHOLE heap it holds at.
infix 9 _↦_

_↦_ : Loc → Val → Gr
l ↦ x = ⌈ single l x ⌉

-- `emp` IS A UNIT FOR `∗`. Four lemmas, not two: each side is an identity
-- law and each law has a direction.

-- PRIMITIVE (phase 1): an INVERSION of the substrate's splitting relation,
-- moved along a strict equality.
emp-∗ : (P : Gr) → (empR ∗ P) ⊢ P
emp-∗ P h ((u , v , ilv , apt) , k) =
  coeEq P (ilv-nilL-inv (coeEq (λ z → Ilv z v h) (k true) ilv)) (k false)

emp-∗-I : (P : Gr) → P ⊢ (empR ∗ P)
emp-∗-I P h p = ([] , h , ilv-nilL h , tt) , boolΠ Eq.refl p

∗-emp : (P : Gr) → (P ∗ empR) ⊢ P
∗-emp P h ((u , v , ilv , apt) , k) =
  coeEq P (ilv-nilR-inv (coeEq (λ z → Ilv u z h) (k false) ilv)) (k true)

∗-emp-I : (P : Gr) → P ⊢ (P ∗ empR)
∗-emp-I P h p = (h , [] , ilv-nilR h , #-nil h) , boolΠ p Eq.refl

-- Commutativity.  `Ilv` swaps by exchanging two constructors; `_#_` is
-- symmetric because `Diff` is.  Both are structural recursions on the
-- representation, hence PRIMITIVE.

diff-sym : (l k : Loc) → Diff l k → Diff k l          -- PRIMITIVE
diff-sym zero    zero    d = d
diff-sym zero    (suc _) d = tt
diff-sym (suc _) zero    d = tt
diff-sym (suc l) (suc k) d = diff-sym l k d

#-tail : (u v : Heap) (c : Cell) → u # (c ∷ v) → u # v   -- PRIMITIVE
#-tail []            v c       d       = tt
#-tail ((l , _) ∷ u) v (k , y) (f , d) = f .snd , #-tail u v (k , y) d

#-head : (u v : Heap) (k : Loc) (y : Val)                -- PRIMITIVE
       → u # ((k , y) ∷ v) → Fresh k u
#-head []            v k y d       = tt
#-head ((l , _) ∷ u) v k y (f , d) = diff-sym l k (f .fst) , #-head u v k y d

#-sym : (u v : Heap) → u # v → v # u
#-sym u []            d = tt
#-sym u ((k , y) ∷ v) d = #-head u v k y d , #-sym u v (#-tail u v (k , y) d)

ilv-sym : {u v h : Heap} → Ilv u v h → Ilv v u h          -- PRIMITIVE
ilv-sym nil       = nil
ilv-sym (left p)  = right (ilv-sym p)
ilv-sym (right p) = left  (ilv-sym p)

∗-comm : (P Q : Gr) → (P ∗ Q) ⊢ (Q ∗ P)
∗-comm P Q h ((u , v , ilv , apt) , k) =
  (v , u , ilv-sym ilv , #-sym u v apt) , boolΠ (k false) (k true)
