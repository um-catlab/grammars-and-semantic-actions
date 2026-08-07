{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- SCRATCH: the timing sweep for the span CYK.  `HALF` and the span in
   the test line are what the sweep script rewrites; the grammar is
   `Bench`'s aⁿbⁿ and the word is a^HALF b^HALF, so the root span
   (0 , 2*HALF) succeeds and forces the chart to full depth. -}
module TheoryGrammar.Instances.Spans.Sweep where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Enumerable
open import TheoryGrammar.SemanticAction using (passes; _↦_; _at_)
open import TheoryGrammar.Instances.Spans.CYK

HALF : ℕ
HALF = 15

ltb : ℕ → ℕ → Bool
ltb zero    (suc _) = true
ltb _       zero    = false
ltb (suc m) (suc n) = ltb m n

charAt : ℕ → Bool
charAt j = ltb j HALF

data NT : Type₀ where ntS ntA ntB ntC : NT

unitR : NT → ℕ → Type₀
unitR ntS j = ⊥
unitR ntC j = ⊥
unitR ntA j = charAt j Eq.≡ true
unitR ntB j = charAt j Eq.≡ false

binR : NT → NT → NT → Type₀
binR ntS ntA ntB = Unit
binR ntS ntA ntC = Unit
binR ntC ntS ntB = Unit
binR _   _   _   = ⊥

open CYK NT unitR binR

allRules : (P : NT) → List (Rule P)
allRules ntS = inl tt ∷ inr (ntA , ntB , tt) ∷ inr (ntA , ntC , tt) ∷ []
allRules ntC = inl tt ∷ inr (ntS , ntB , tt) ∷ []
allRules ntA = inl tt ∷ []
allRules ntB = inl tt ∷ []

allComplete : (P : NT) (r : Rule P) → r ∈L allRules P
allComplete ntS (inl tt)               = here
allComplete ntS (inr (ntS , _   , ()))
allComplete ntS (inr (ntB , _   , ()))
allComplete ntS (inr (ntC , _   , ()))
allComplete ntS (inr (ntA , ntS , ()))
allComplete ntS (inr (ntA , ntA , ()))
allComplete ntS (inr (ntA , ntB , tt)) = there here
allComplete ntS (inr (ntA , ntC , tt)) = there (there here)
allComplete ntC (inl tt)               = here
allComplete ntC (inr (ntA , _   , ()))
allComplete ntC (inr (ntB , _   , ()))
allComplete ntC (inr (ntC , _   , ()))
allComplete ntC (inr (ntS , ntS , ()))
allComplete ntC (inr (ntS , ntA , ()))
allComplete ntC (inr (ntS , ntB , tt)) = there here
allComplete ntC (inr (ntS , ntC , ()))
allComplete ntA (inl tt)               = here
allComplete ntA (inr (_ , _ , ()))
allComplete ntB (inl tt)               = here
allComplete ntB (inr (_ , _ , ()))

decEqB : (a b : Bool) → (a Eq.≡ b) ⊎ No (a Eq.≡ b)
decEqB true  true  = inl Eq.refl
decEqB false false = inl Eq.refl
decEqB true  false = inr λ ()
decEqB false true  = inr λ ()

decUnit : (P : NT) (j : ℕ) → unitR P j ⊎ No (unitR P j)
decUnit ntS j = inr λ ()
decUnit ntC j = inr λ ()
decUnit ntA j = decEqB (charAt j) true
decUnit ntB j = decEqB (charAt j) false

termProbe : (P : NT) → Probe (UnitG P)
termProbe P (i , zero)        _ = dec-no (UnitG P) _ λ { (j , () , _) }
termProbe P (i , suc (suc n)) _ = dec-no (UnitG P) _ λ { (j , () , _) }
termProbe P (i , suc zero)    _ = pick (decUnit P i)
  where
    pick : unitR P i ⊎ No (unitR P i) → Dec⟨ UnitG P ⟩ (i , 1)
    pick (inl u) = dec-yes (UnitG P) _ (i , Eq.refl , u)
    pick (inr k) = dec-no  (UnitG P) _ λ { (j , Eq.refl , u) → k u }

open Decide allRules allComplete termProbe

-- TABULATED (`löbᵀ` + `Spans.Schedule`)
derives! : (P : NT) → ⊤G ⊢ Δ Bool
derives! P = okA (Deriv P) (¬G Deriv P) ∘g derives? P

-- UNTABULATED (`löbᵍ`), the same step term -- the measurement baseline
derivesLob! : (P : NT) → ⊤G ⊢ Δ Bool
derivesLob! P =
  okA (Deriv P) (¬G Deriv P) ∘g (chartAt P ∘g chartLöb)

_ : passes (run (derives! ntS) at ( (0 , 30) ↦ true ∷ [] ))
_ = refl
