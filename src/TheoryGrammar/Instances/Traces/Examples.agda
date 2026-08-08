{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Three letters, ONE independent pair, and the interpolation measured. -}
module TheoryGrammar.Instances.Traces.Examples where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty as E using (⊥)

open import TheoryGrammar.Enumerable using (No)

import TheoryGrammar.Instances.Traces.Ordered     as TrOrd
import TheoryGrammar.Instances.Traces.Commutative as TrCom
import TheoryGrammar.Instances.Traces.Decidable   as TrDec

data L3 : Type₀ where
  a b c : L3

-- ONE independent pair: `a` and `b` commute; `c` commutes with nothing,
-- and no letter commutes with itself (independence is irreflexive).
Ind : L3 → L3 → Type₀
Ind a b = Unit
Ind b a = Unit
Ind _ _ = ⊥

decInd : (x y : L3) → Ind x y ⊎ No (Ind x y)
decInd a a = inr λ ()
decInd a b = inl tt
decInd a c = inr λ ()
decInd b a = inl tt
decInd b b = inr λ ()
decInd b c = inr λ ()
decInd c a = inr λ ()
decInd c b = inr λ ()
decInd c c = inr λ ()

isPropInd : (x y : L3) → isProp (Ind x y)
isPropInd a a = E.isProp⊥
isPropInd a b = isPropUnit
isPropInd a c = E.isProp⊥
isPropInd b a = isPropUnit
isPropInd b b = E.isProp⊥
isPropInd b c = E.isProp⊥
isPropInd c a = E.isProp⊥
isPropInd c b = E.isProp⊥
isPropInd c c = E.isProp⊥

-- the two endpoints, with their isos
module OrdI = TrOrd L3
module ComI = TrCom L3

dec⊥ : (x y : L3) → OrdI.⊥I x y ⊎ No (OrdI.⊥I x y)
dec⊥ x y = inr λ ()

isProp⊥I : (x y : L3) → isProp (OrdI.⊥I x y)
isProp⊥I x y = E.isProp⊥

dec⊤ : (x y : L3) → ComI.⊤I x y ⊎ No (ComI.⊤I x y)
dec⊤ x y = inl tt

isProp⊤I : (x y : L3) → isProp (ComI.⊤I x y)
isProp⊤I x y = isPropUnit

-- one family, three members
module Ord  = TrDec L3 OrdI.⊥I dec⊥   isProp⊥I
module Part = TrDec L3 Ind     decInd isPropInd
module Full = TrDec L3 ComI.⊤I dec⊤   isProp⊤I

w3 : List L3
w3 = a ∷ b ∷ c ∷ []

-- THE INTERPOLATION, COUNTED. `abc` has 4 concatenations (the |w|+1 cuts)
-- 5 I-shuffles (`b` may cross `a`, nothing may cross `c`) 8 interleavings
-- (2^|w|)

_ : length (Ord.shuffles w3) ≡ 4
_ = refl

_ : length (Part.shuffles w3) ≡ 5
_ = refl

_ : length (Full.shuffles w3) ≡ 8
_ = refl

-- the two-letter words show where the extra factorisation comes from:
-- `ab` is already fully commutative, `ac` is still purely ordered
_ : length (Part.shuffles (a ∷ b ∷ [])) ≡ 4
_ = refl

_ : length (Part.shuffles (a ∷ c ∷ [])) ≡ 3
_ = refl

-- THE POINT IS ONLY LAX, STRICTLY SO.  `ba` splits as `a` and `b`
-- although `a ++ b = ab`; and the same swap is REFUTED at the pair
-- that is not independent.

-- `ba` IS a shuffle of `a` and `b` ...
swap-ab : Part.ITr Ind (a ∷ []) (b ∷ []) (b ∷ a ∷ [])
swap-ab = Part.right (tt , tt) (Part.left Part.nil)

-- ... while the point's answer at the same pair is `ab`, so the
-- containment `u ++ v` ⊆ shuffles is strict.
_ : (a ∷ []) ++ (b ∷ []) ≡ a ∷ b ∷ []
_ = refl

-- ... and the same swap is REFUTED at the dependent pair.
no-swap-ac : Part.ITr Ind (a ∷ []) (c ∷ []) (c ∷ a ∷ []) → ⊥
no-swap-ac (Part.right (() , _) t)

-- The endpoint isos compute.

ex⊥ : OrdI.ITr OrdI.⊥I (a ∷ []) (b ∷ []) (a ∷ b ∷ [])
ex⊥ = OrdI.left (OrdI.right tt OrdI.nil)

_ : OrdI.toSplit3 ex⊥ ≡ OrdI.Str.cons OrdI.Str.nil
_ = refl

_ : OrdI.fromSplit3 (OrdI.Str.cons OrdI.Str.nil) ≡ ex⊥
_ = refl

ex⊤ : ComI.ITr ComI.⊤I (a ∷ []) (b ∷ []) (b ∷ a ∷ [])
ex⊤ = ComI.right (tt , tt) (ComI.left ComI.nil)

_ : ComI.toIlv ex⊤ ≡ ComI.Bg.right (ComI.Bg.left ComI.Bg.nil)
_ = refl

_ : ComI.fromIlv (ComI.Bg.right (ComI.Bg.left ComI.Bg.nil)) ≡ ex⊤
_ = refl
