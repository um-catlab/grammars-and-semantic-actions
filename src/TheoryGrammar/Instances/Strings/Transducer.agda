{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{- A GRAMMAR OVER THE GLUE, and what it costs. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Strings.Transducer
  (In Out : Type₀) (f : In → Out) where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit
open import Cubical.Data.List
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Theories.Monoid
open import TheoryGrammar.Fibered

import TheoryGrammar.Instances.Strings.Base as StB
import TheoryGrammar.Instances.Strings.Aligned as Al
open Al In Out public

-- the two recomposition facts, at each alphabet
import TheoryGrammar.Instances.Strings.Recompose as Rc
module RI = Rc In
module RO = Rc Out

-- PRIMITIVE.  THE LETTERWISE PROPERTY, and the only mention of `f` in
-- the whole file outside `Trans` itself.
mapApp : (u v : I.String) → map f (u ++ v) Eq.≡ (map f u ++ map f v)
mapApp []      v = Eq.refl
mapApp (c ∷ u) v = Eq.ap (λ z → f c ∷ z) (mapApp u v)

-- THE GRAMMAR.

Trans : G.TheoryTy ℓ-zero tt
Trans g = map f (g .fst) Eq.≡ g .snd .fst

-- named, not an extended lambda: a slot family written `λ { … }` is not
-- convertible with itself, and `⊗ˢ-E` could not be stated at it
transSlots : (a : MonAr appop) → G.TheoryTy ℓ-zero tt
transSlots _ = Trans

nilSlots : (a : MonAr nilop) → G.TheoryTy ℓ-zero tt
nilSlots ()

-- ... AND ITS MULTIPLICATIVE STRUCTURE.

transTensor : G.⊗ˢ appop transSlots G.⊢ Trans
transTensor = G.⊗ˢ-E appop {A = transSlots} {B = Trans} body
  where
  body : G.MultiHomˢ appop transSlots Trans
  body g ((u₁ , u₂ , p) , (v₁ , v₂ , q) , _) h =
    Eq.ap (map f) (RI.recompose p)
      Eq.∙ (mapApp u₁ u₂
      Eq.∙ (Eq.ap (λ z → z ++ map f u₂) (h true)
      Eq.∙ (Eq.ap (λ z → v₁ ++ z) (h false)
      Eq.∙ Eq.sym (RO.recompose q))))

transNil : G.⊗ˢ nilop nilSlots G.⊢ Trans
transNil = G.⊗ˢ-E nilop {A = nilSlots} {B = Trans} body
  where
  body : G.MultiHomˢ nilop nilSlots Trans
  body g (nw , nv , _) _ =
    Eq.ap (map f) (RI.isNilEq (g .fst) nw)
      Eq.∙ Eq.sym (RO.isNilEq (g .snd .fst) nv)

-- THE TESTS.  `f` is abstract, so nothing here can be computing by
-- accident on the letters.

module _ (x y : In) where

  private
    w2 : I.String
    w2 = x ∷ y ∷ []

    v2 : O.String
    v2 = f x ∷ f y ∷ []

    g2 : Aligned
    g2 = w2 , v2 , Eq.refl

    cut1 : I.strFib .Split appop w2
    cut1 = (x ∷ []) , (y ∷ []) , I.cons I.nil

    -- the output tape's cut is not chosen -- `Determined` produces it
    glued : glue .Split appop g2
    glued = cut1 , alignedDetermined appop g2 cut1

    pay : (a : MonAr appop) → Trans (glue .parts appop g2 glued a)
    pay true  = Eq.refl
    pay false = Eq.refl

  -- the whole `Eq` chain collapses on closed data
  _ : transTensor g2 (glued , pay) ≡ Eq.refl
  _ = refl

  -- and the transduced pair really is one
  witness : Trans g2
  witness = transTensor g2 (glued , pay)

  _ : witness ≡ Eq.refl
  _ = refl
