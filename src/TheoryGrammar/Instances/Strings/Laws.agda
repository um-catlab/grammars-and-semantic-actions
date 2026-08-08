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

-- ==================================================================
-- The four laws are `Theories.MonoidStructure`'s, at the string
-- splitting.  What is string-specific is the three facts below about
-- `Split3` -- everything else is derived generically.  Strings have no
-- `Sym`: `Split3` cannot be swapped, and that absence is the whole
-- difference from `Bags`.
-- ==================================================================

open import TheoryGrammar.Theories.MonoidStructure
module MS = MonStr strFib

-- PRIMITIVE (phase 1): reassociation of `Split3`, i.e. Levi's lemma.
splitAssoc : ∀ {u v v' x w} → Split3 u x w → Split3 v v' x
           → Σ[ y ∈ String ] (Split3 u v y × Split3 y v' w)
splitAssoc nil      t = _ , nil , t
splitAssoc (cons s) t =
  let (y , s1 , s2) = splitAssoc s t in _ , cons s1 , cons s2

strAssoc : MS.Assoc
strAssoc .MS.reOut w (u , x , s) (v , v' , t) =
  splitAssoc s t .fst , v' , splitAssoc s t .snd .snd
strAssoc .MS.reIn  w (u , x , s) (v , v' , t) = u , v , splitAssoc s t .snd .fst
strAssoc .MS.reP w (u , x , s) (v , v' , t) = Eq.refl
strAssoc .MS.reQ w (u , x , s) (v , v' , t) = Eq.refl
strAssoc .MS.reR w (u , x , s) (v , v' , t) = Eq.refl

strUnitL : MS.UnitL
strUnitL .MS.nilL w ([] , v , nil) tt = Eq.refl
strUnitL .MS.mkL  w = [] , w , nil
strUnitL .MS.mkLε w = tt
strUnitL .MS.mkLR w = Eq.refl

strUnitR : MS.UnitR
strUnitR .MS.nilR w (u , [] , s) tt = split3-nilʳ s
strUnitR .MS.mkR  w = w , [] , split3-idʳ w
strUnitR .MS.mkRε w = tt
strUnitR .MS.mkRL w = Eq.refl

-- the arity-η coercion between `⊗'` (an `if`) and `⊗ᵐ` (a `boolΠ`)
into : {P Q : Gr} → (P ⊗' Q) ⊢ (P MS.⊗ᵐ Q)
into {P} {Q} = MS.⊗ˢ-recast {A = λ b → if b then P else Q}
                            {B = boolΠ {M = λ _ → Gr} P Q} idg idg

outof : {P Q : Gr} → (P MS.⊗ᵐ Q) ⊢ (P ⊗' Q)
outof {P} {Q} = MS.⊗ˢ-recast {A = boolΠ {M = λ _ → Gr} P Q}
                             {B = λ b → if b then P else Q} idg idg

⊗-unit-l : {A : Gr} → (ε' ⊗' A) ⊢ A
⊗-unit-l {A} = MS.⊗ᵐ-unit-l strUnitL {P = A} ∘g into {ε'} {A}

⊗-unit-r : {A : Gr} → (A ⊗' ε') ⊢ A
⊗-unit-r {A} = MS.⊗ᵐ-unit-r strUnitR {P = A} ∘g into {A} {ε'}

⊗-unit-l⁻ : {A : Gr} → A ⊢ (ε' ⊗' A)
⊗-unit-l⁻ {A} = outof {ε'} {A} ∘g MS.⊗ᵐ-unit-l⁻ strUnitL {P = A}

⊗-unit-r⁻ : {A : Gr} → A ⊢ (A ⊗' ε')
⊗-unit-r⁻ {A} = outof {A} {ε'} ∘g MS.⊗ᵐ-unit-r⁻ strUnitR {P = A}

-- the round trip, still `refl`
⊗-unit-ll⁻ : {A : Gr} → ∀ w (a : A w) → ⊗-unit-l w (⊗-unit-l⁻ {A = A} w a) ≡ a
⊗-unit-ll⁻ w a = refl

⊗-assoc : {A B C : Gr} → (A ⊗' (B ⊗' C)) ⊢ ((A ⊗' B) ⊗' C)
⊗-assoc {A} {B} {C} =
    outof {A ⊗' B} {C}
  ∘g MS.⊗ᵐ-map (outof {A} {B}) idg
  ∘g MS.⊗ᵐ-assoc strAssoc {P = A} {Q = B} {S = C}
  ∘g MS.⊗ᵐ-map idg (into {B} {C})
  ∘g into {A} {B ⊗' C}
