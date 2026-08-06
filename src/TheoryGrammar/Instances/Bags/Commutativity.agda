{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Commutativity of ⊗, discharged by swapping an interleaving. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Bags.Commutativity (A : Type₀) where

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
open import TheoryGrammar.Substrate
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded
open import Cubical.Foundations.Isomorphism

open import TheoryGrammar.Instances.Bags.Connectives A public

ilvSwap : ∀ {u v w} → Ilv u v w → Ilv v u w
ilvSwap nil       = nil
ilvSwap (left s)  = right (ilvSwap s)
ilvSwap (right s) = left (ilvSwap s)


⊗-comm : {P Q : Gr} → (P ⊗' Q) ⊢ (Q ⊗' P)
⊗-comm w ((u , v , s) , h) = (v , u , ilvSwap s) , λ { true → h false ; false → h true }

ilvSwap-inv : ∀ {u v w} (s : Ilv u v w) → ilvSwap (ilvSwap s) ≡ s
ilvSwap-inv nil       = refl
ilvSwap-inv (left s)  = cong left  (ilvSwap-inv s)
ilvSwap-inv (right s) = cong right (ilvSwap-inv s)

⊗-comm-invol : {P Q : Gr} (w : Bag) (t : (P ⊗' Q) w)
             → ⊗-comm {P = Q} {Q = P} w (⊗-comm {P = P} {Q = Q} w t) ≡ t
⊗-comm-invol w ((u , v , s) , h) =
  ΣPathP ( (λ i → u , v , ilvSwap-inv s i)
         , funExt λ { true → refl ; false → refl } )

-- The grading.  Properness of a slot = its COMPLEMENT is nonempty.
