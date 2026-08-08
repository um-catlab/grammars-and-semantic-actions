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
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded
open import Cubical.Foundations.Isomorphism

open import TheoryGrammar.Instances.Bags.Connectives A public

ilvSwap : ∀ {u v w} → Ilv u v w → Ilv v u w
ilvSwap nil       = nil
ilvSwap (left s)  = right (ilvSwap s)
ilvSwap (right s) = left (ilvSwap s)

-- THE THREE STRUCTURAL FACTS, and they are facts about `Ilv` alone.
-- `MonoidStructure` turns them into the monoidal laws of `⊗'`, so
-- nothing below matches a splitting.
open import TheoryGrammar.Theories.MonoidStructure
module MS = MonStr bagFib

bagSym : MS.Sym
bagSym .MS.swapSp w (u , v , s) = v , u , ilvSwap s
bagSym .MS.swapL  w (u , v , s) = Eq.refl
bagSym .MS.swapR  w (u , v , s) = Eq.refl

bagAssoc : MS.Assoc
bagAssoc .MS.reOut w (p , qr , s) (q , r , t) =
  ilvAssoc s (ilvSwap t) .fst , r , ilvSwap (ilvAssoc s (ilvSwap t) .snd .fst)
bagAssoc .MS.reIn  w (p , qr , s) (q , r , t) =
  p , q , ilvAssoc s (ilvSwap t) .snd .snd
bagAssoc .MS.reP w (p , qr , s) (q , r , t) = Eq.refl
bagAssoc .MS.reQ w (p , qr , s) (q , r , t) = Eq.refl
bagAssoc .MS.reR w (p , qr , s) (q , r , t) = Eq.refl

-- `⊗'` spells its arity family with `if`, `⊗ᵐ` with `boolΠ`; the two are
-- pointwise equal and not definitionally so, which is what `⊗ˢ-recast`
-- is for.  Both its arguments are `idg`: no content crosses.
into : {P Q : Gr} → (P ⊗' Q) ⊢ (P MS.⊗ᵐ Q)
into {P} {Q} = MS.⊗ˢ-recast {A = λ b → if b then P else Q}
                            {B = boolΠ {M = λ _ → Gr} P Q} idg idg

outof : {P Q : Gr} → (P MS.⊗ᵐ Q) ⊢ (P ⊗' Q)
outof {P} {Q} = MS.⊗ˢ-recast {A = boolΠ {M = λ _ → Gr} P Q}
                             {B = λ b → if b then P else Q} idg idg

bagUnitL : MS.UnitL
bagUnitL .MS.nilL w ([]    , v , s) tt = ilv-nilL-inv s
bagUnitL .MS.mkL  w = [] , w , ilv-nilL w
bagUnitL .MS.mkLε w = tt
bagUnitL .MS.mkLR w = Eq.refl

bagUnitR : MS.UnitR
bagUnitR .MS.nilR w (u , []    , s) tt = ilv-nilR-inv s
bagUnitR .MS.mkR  w = w , [] , ilv-nilR w
bagUnitR .MS.mkRε w = tt
bagUnitR .MS.mkRL w = Eq.refl

-- DERIVED, not primitive: `⊗ˢ`'s symmetry at the bag splitting.
⊗-comm : {P Q : Gr} → (P ⊗' Q) ⊢ (Q ⊗' P)
⊗-comm {P} {Q} = outof {Q} {P} ∘g MS.⊗ᵐ-comm bagSym {P = P} {Q = Q} ∘g into {P} {Q}

-- ... and associativity, which no bag file had at all.
⊗-assoc : {P Q S : Gr} → (P ⊗' (Q ⊗' S)) ⊢ ((P ⊗' Q) ⊗' S)
⊗-assoc {P} {Q} {S} =
    outof {P ⊗' Q} {S}
  ∘g MS.⊗ᵐ-map (outof {P} {Q}) idg
  ∘g MS.⊗ᵐ-assoc bagAssoc {P = P} {Q = Q} {S = S}
  ∘g MS.⊗ᵐ-map idg (into {Q} {S})
  ∘g into {P} {Q ⊗' S}

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

-- ... and the unit laws, which no bag file had either.
⊗-unit-l : {P : Gr} → (ε' ⊗' P) ⊢ P
⊗-unit-l {P} = MS.⊗ᵐ-unit-l bagUnitL {P = P} ∘g into {ε'} {P}

⊗-unit-l⁻ : {P : Gr} → P ⊢ (ε' ⊗' P)
⊗-unit-l⁻ {P} = outof {ε'} {P} ∘g MS.⊗ᵐ-unit-l⁻ bagUnitL {P = P}

⊗-unit-r : {P : Gr} → (P ⊗' ε') ⊢ P
⊗-unit-r {P} = MS.⊗ᵐ-unit-r bagUnitR {P = P} ∘g into {P} {ε'}

⊗-unit-r⁻ : {P : Gr} → P ⊢ (P ⊗' ε')
⊗-unit-r⁻ {P} = outof {P} {ε'} ∘g MS.⊗ᵐ-unit-r⁻ bagUnitR {P = P}
