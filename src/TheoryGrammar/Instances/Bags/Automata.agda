{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Automata over a COMMUTATIVE theory: the same three per-theory pieces the
   string instance supplies (description, guardedness, ⊤'s coalgebra), over
   bags, with the generic runner from `Graded`. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Bags.Automata (A : Type₀) where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.List
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded
open import TheoryGrammar.Theories.MonoidStar

open import TheoryGrammar.Instances.Bags.Sorted A public

-- (1) the description: "take out one element, or stop"

bagAtom : Gr
bagAtom = ⊕ᴰ A (λ x → ⌈ x ∷ [] ⌉)

-- generic monoid star at this atom, not bag-specific.  `MonStar` is
-- opened selectively so its `Guard` re-export does not collide.
open MonStar bagGraded using (starSlot; starF; starGuarded; ProperBody)

ScanSlot : Bool → Functor tt
ScanSlot = starSlot bagAtom

ScanF : Unit → Functor tt
ScanF = starF bagAtom

-- (2) guardedness -- the ONE bag-specific line: an atom is a proper
-- resource.  Everything else comes from the generic layer.

atomNN : bagAtom ⊢ NonTrivial
atomNN = ⊕ᴰ-E λ x → ⌈⌉-E (x , ⊗-mk (left nil) Eq.refl tt)

atomProper : ProperBody bagAtom
atomProper m sp a = atomNN _ a

scanGuarded : (x : Unit) → Guarded (ScanF x)
scanGuarded = starGuarded bagAtom atomProper

-- (3) ⊤'s coalgebra -- `bagCase`, which already existed, in the
-- description's shape.  This is the decomposition axiom for bags.

scanCoalg : Scanner ScanF
scanCoalg tt m _ = go (bagCase m tt)
  where
    go : (⌈ [] ⌉ ⊕ NonTrivial) m → ⟦ ScanF tt ⟧ᴳ (λ _ → ⊤ᴳ) m
    go (inl e) = true , lift (nilOf e)
      where nilOf : m Eq.≡ [] → ε' m
            nilOf Eq.refl = tt , λ ()
    go (inr (x , sp , h)) =
      false , sp , λ { true → lift (x , h true) ; false → tt* }

scanLC : LocallyContractive ScanF
scanLC = guarded→LC scanGuarded

-- What `ScanF` does to a grammar:  ⟦ ScanF ⟧ A ≅ ε ⊕ (atom ⊗ A).
-- Both directions are the generic star functor's iso at
-- `ScanF = starF bagAtom`.
scanOut : (A : Gr) → ⟦ ScanF tt ⟧ᴳ (λ _ → A) ⊢ (ε' ⊕ (bagAtom ⊗' A))
scanOut = MonStar.starOut bagGraded {A = bagAtom}

scanIn : (A : Gr) → (ε' ⊕ (bagAtom ⊗' A)) ⊢ ⟦ ScanF tt ⟧ᴳ (λ _ → A)
scanIn = MonStar.starIn bagGraded {A = bagAtom}

-- An automaton over bags: fold with a combining function.  Well-defined
-- exactly when `_·_` is commutative, per the header.

module Fold (B : Type₀) (nil· : B) (cons· : A → B → B) where

  Carrier : Fam
  Carrier _ _ = B

  foldAut : Algᴳ ScanF Carrier
  foldAut tt =
    ⊕ᴰ-E λ { true  → λ _ _ → nil·
           ; false → ⊗ˢ-E appop {A = λ a → ⟦ ScanSlot a ⟧c ⌞ Carrier ⌟}
                                {B = λ _ → B}
                                (λ _ _ h → cons· (lower (h true) .fst) (h false)) }

  -- A term out of ⊤, so its codomain must be a grammar: `Δ B`, not the
  -- constant family, with the externalisation deferred to `run`.  The
  -- `A` suffix is the semantic-action convention (`okA`, `tagA`).
  foldA : ⊤G ⊢ Δ B
  foldA = intoΔ B ∘g runAut scanLC scanCoalg foldAut tt
