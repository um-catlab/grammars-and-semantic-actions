{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Automata over a COMMUTATIVE theory.

   `Automaton`, `Scanner` and `runAut` are theory-generic and live in
   `TheoryGrammar.Graded`.  This file is the check that they really are:
   it supplies the same three per-theory pieces the string instance
   does -- a description, its guardedness, and ⊤'s coalgebra -- over
   bags instead of strings, and gets the same runner.

   ONE THING IS GENUINELY DIFFERENT, and it is a property of the theory
   rather than of the interface.  Over a commutative theory the scanner
   CHOOSES a decomposition, and different choices visit the elements in
   different orders.  So `runAut` computes an answer, but that answer is
   canonical only when the algebra is invariant under the theory's
   equations.  `foldAut` below is well-defined for a commutative
   combining function (sum, product, max, size) and NOT for an
   order-sensitive one (building a list) -- the type does not stop you
   writing the latter, it just stops meaning what you wanted.  For
   strings the question does not arise, since `charCase` has only one
   decomposition to choose. -}
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

-- ==================================================================
-- (1) the description: "take out one element, or stop"
-- ==================================================================

bagAtom : Gr
bagAtom = ⊕ᴰ A (λ x → ⌈ x ∷ [] ⌉)

-- The description and its guardedness are NOT bag-specific: they are
-- the generic monoid star at this atom.  `MonStar` is opened
-- selectively so its `Guard` re-export does not collide with the one
-- the Bags chain already applied.
open MonStar bagGraded using (starSlot; starF; starGuarded; ProperBody)

ScanSlot : Bool → Functor tt
ScanSlot = starSlot bagAtom

ScanF : Unit → Functor tt
ScanF = starF bagAtom

-- ==================================================================
-- (2) guardedness -- the ONE bag-specific line: an atom is a proper
-- resource.  Everything else comes from the generic layer.
-- ==================================================================

atomNN : bagAtom ⊢ NonTrivial
atomNN = ⊕ᴰ-E λ x → ⌈⌉-E (x , ⊗-mk (left nil) Eq.refl tt)

atomProper : ProperBody bagAtom
atomProper m sp a = atomNN _ a

scanGuarded : (x : Unit) → Guarded (ScanF x)
scanGuarded = starGuarded bagAtom atomProper

-- ==================================================================
-- (3) ⊤'s coalgebra -- `bagCase`, which already existed, in the
-- description's shape.  This is the decomposition axiom for bags.
-- ==================================================================

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

-- ==================================================================
-- THE FUNCTOR, spelled out.  A description is not self-evident, so
-- here is what `ScanF` actually does to a grammar:
--
--     ⟦ ScanF ⟧ A  ≅  ε  ⊕  (atom ⊗ A)
--
-- Both directions are terms.  The only content is `⊕e`/`⊗e` versus
-- `⊕`/`⊗'` and the `Lift`s on the constant slots.
-- ==================================================================

scanOut : (A : Gr) → ⟦ ScanF tt ⟧ᴳ (λ _ → A) ⊢ (ε' ⊕ (bagAtom ⊗' A))
scanOut A m (true  , e)       = inl (lower e)
scanOut A m (false , sp , h)  =
  inr (sp , λ { true → lower (h true) ; false → h false })

scanIn : (A : Gr) → (ε' ⊕ (bagAtom ⊗' A)) ⊢ ⟦ ScanF tt ⟧ᴳ (λ _ → A)
scanIn A m (inl e)        = true , lift e
scanIn A m (inr (sp , h)) =
  false , sp , λ { true → lift (h true) ; false → h false }

-- ==================================================================
-- An automaton over bags: fold with a combining function.  Well-defined
-- exactly when `_·_` is commutative, per the header.
-- ==================================================================

module Fold (B : Type₀) (nil· : B) (cons· : A → B → B) where

  Carrier : Fam
  Carrier _ _ = B

  foldAut : Algᴳ ScanF Carrier
  foldAut tt =
    ⊕ᴰ-E λ { true  → λ _ _ → nil·
           ; false → ⊗ˢ-E appop {A = λ a → ⟦ ScanSlot a ⟧c ⌞ Carrier ⌟}
                                {B = λ _ → B}
                                (λ _ _ h → cons· (lower (h true) .fst) (h false)) }

  -- An INTERNAL term out of ⊤ -- which means its codomain has to be a
  -- GRAMMAR.  `λ _ → B` is not one in the sense that matters: it is the
  -- constant family, and a name whose type mentions it has already left
  -- the calculus.  `Δ B` is the grammar that carries a `B`, so this is
  -- the same computation with the externalisation deferred to `run`.
  -- The `A` suffix is the semantic-action convention (`okA`, `tagA`,
  -- `mapA`); a `run`-prefixed name would advertise the wrong thing.
  foldA : ⊤G ⊢ Δ B
  foldA m x = runAut scanLC scanCoalg foldAut tt m x , x
