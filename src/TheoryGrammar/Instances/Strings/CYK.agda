{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- CYK parsing: a CNF grammar, by löb over the proper splittings. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Strings.CYK (Char : Type₀) where

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

open import TheoryGrammar.Instances.Strings.Enumeration Char public

module CYK (V : Type₀) (allV : List V)
           (unitRule : V → Char → Bool)
           (binRule  : V → V → V → Bool) where

  anyL : {X : Type₀} → (X → Bool) → List X → Bool
  anyL p []       = false
  anyL p (x ∷ xs) = if p x then true else anyL p xs

  filterL : {X : Type₀} → (X → Bool) → List X → List X
  filterL p []       = []
  filterL p (x ∷ xs) = if p x then x ∷ filterL p xs else filterL p xs

  concatMapL : {X Y : Type₀} → (X → List Y) → List X → List Y
  concatMapL f []       = []
  concatMapL f (x ∷ xs) = f x ++ concatMapL f xs

  0<suc : {n : ℕ} → 0 < suc n
  0<suc = suc-≤-suc zero-≤

  Res : Ix → Type₀
  Res _ = List V

  -- one decomposition: recurse on both parts, keep the P with a rule
  -- P → Q T witnessed there.  Improper cuts contribute nothing.
  atCut : (w : String) → ((j : Ix) → j ≺ (tt , w) → List V)
        → MonSplit appop w → List V
  atCut w rec (u , v , s) = go u v s
    where
      go : (u' v' : String) → Split3 u' v' w → List V
      go []      v'       s' = []
      go (_ ∷ _) []       s' = []
      go (c ∷ u') (d ∷ v') s' =
        filterL (λ P → anyL (λ Q → anyL (λ T → binRule P Q T) ts) qs) allV
        where qs = rec (tt , c ∷ u') (split3LenL< s' 0<suc)
              ts = rec (tt , d ∷ v') (split3LenR< s' 0<suc)

  unitPart : String → List V
  unitPart (c ∷ []) = filterL (λ P → unitRule P c) allV
  unitPart _        = []

  cyk : String → List V
  cyk w = löb {A = Res} step (tt , w)
    where
      step : (i : Ix) → ▷ Res i → Res i
      step (tt , w') rec = unitPart w' ++ concatMapL (atCut w' rec) (cuts w')

-- A concrete parse that computes.
