{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Unit and associativity for ⊗. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Strings.Laws (Char : Type₀) where

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

open import TheoryGrammar.Instances.Strings.Connectives Char public

⊗-unit-l : {A : Gr} → (ε' ⊗' A) ⊢ A
⊗-unit-l w (([]    , v , nil) , h) = h false
⊗-unit-l w ((c ∷ u , v , s)   , h) = E.rec (h true .fst)

-- right unit: needs the induction that `++-unit-r` needs in LambekD.
splitNilR : ∀ {u w} → Split3 u [] w → u Eq.≡ w
splitNilR nil      = Eq.refl
splitNilR (cons s) with splitNilR s
... | Eq.refl = Eq.refl

⊗-unit-r : {A : Gr} → (A ⊗' ε') ⊢ A
⊗-unit-r {A} w ((u , []    , s) , h) = coeA (splitNilR s) (h true)
  where coeA : ∀ {u' w'} → u' Eq.≡ w' → A u' → A w'
        coeA Eq.refl a = a
⊗-unit-r {A} w ((u , c ∷ v , s) , h) = E.rec (h false .fst)

⊗-unit-l⁻ : {A : Gr} → A ⊢ (ε' ⊗' A)
⊗-unit-l⁻ w a = ⊗-mk nil ε-mk a

-- the round trip LambekD proves with a chain of Eq.transports
⊗-unit-ll⁻ : {A : Gr} → ∀ w (a : A w) → ⊗-unit-l w (⊗-unit-l⁻ {A = A} w a) ≡ a
⊗-unit-ll⁻ w a = refl

-- associativity, by induction on the outer splitting
splitAssoc : ∀ {u v v' x w} → Split3 u x w → Split3 v v' x
           → Σ[ y ∈ String ] (Split3 u v y × Split3 y v' w)
splitAssoc nil      t = _ , nil , t
splitAssoc (cons s) t =
  let (y , s1 , s2) = splitAssoc s t in _ , cons s1 , cons s2

⊗-assoc : {A B C : Gr} → (A ⊗' (B ⊗' C)) ⊢ ((A ⊗' B) ⊗' C)
⊗-assoc = ⊗-elim λ { a ((v , v' , t) , k) s →
  let (y , s1 , s2) = splitAssoc s t
  in ⊗-mk s2 (⊗-mk s1 a (k true)) (k false) }
