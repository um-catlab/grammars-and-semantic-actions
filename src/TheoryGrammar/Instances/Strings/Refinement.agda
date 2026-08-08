{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- SEQUENTIAL UNAMBIGUITY AS AN INSTANCE OF THE GENERIC THEOREM. -}
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sum using (_⊎_; inl; inr)
import Cubical.Data.Equality as Eq
open import TheoryGrammar.Enumerable using (No)

module TheoryGrammar.Instances.Strings.Refinement
  (Char : Type₀)
  (decChar : (a b : Char) → (a Eq.≡ b) ⊎ No (a Eq.≡ b))
  where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Unit
open import Cubical.Data.List

open import TheoryGrammar.Refinement
open import TheoryGrammar.Instances.Strings.SeqUnambig Char decChar public
-- Levi and refinability, decidability-free (see that file).
open import TheoryGrammar.Instances.Strings.Levi Char public

open Refine strFib

-- `SeqUnambig.sameParts`, AS AN INSTANCE OF THE GENERIC THEOREM.

noMiddle : {A B : Gr} → A ⊛ B
         → ∀ {u₁ v₁ u₂ v₂ t} → A u₁ → B v₁ → A u₂ → B v₂
         → Split3 u₁ t u₂ → Split3 t v₂ v₁ → IsNil t
noMiddle su a₁ b₁ a₂ b₂ P nil                = tt
noMiddle su a₁ b₁ a₂ b₂ P (cons {c = c'} q') = clash (su c')
  where clash : _ → _
        clash (inl nf)  = lower (nf a₁ P a₂)
        clash (inr nfi) = lower (nfi _ b₁)

strNonOverlap : (A B : Gr) → A ⊛ B
              → NonOverlap appHom strRefinable (λ i → if i then A else B)
strNonOverlap A B su w (u₁ , v₁ , s₁) (u₂ , v₂ , s₂) x y = go (levi s₁ s₂)
  where
  go : (d : Refines u₁ v₁ u₂ v₂ ⊎ Refines u₂ v₂ u₁ v₁)
     → Diagonal (refinesOr→refinement {s₁ = s₁} {s₂ = s₂} d)
  go (inl (t , P , Q)) =
    refines→diagonal (t , P , Q) (noMiddle su (x true) (x false) (y true) (y false) P Q)
  go (inr (t , P , Q)) =
    diagTranspose (refines→refinement (t , P , Q))
      (refines→diagonal (t , P , Q) (noMiddle su (y true) (y false) (x true) (x false) P Q))

-- the generic conclusion ...
strSameParts : (A B : Gr) → A ⊛ B
             → (w : String) (p q : SplitH appHom w)
             → ((i : Bool) → (if i then A else B) (partsH appHom w p i))
             → ((i : Bool) → (if i then A else B) (partsH appHom w q i))
             → (i : Bool) → partsH appHom w p i Eq.≡ partsH appHom w q i
strSameParts A B su =
  nonOverlap→sameParts appHom strRefinable (λ i → if i then A else B)
                       (strNonOverlap A B su)

-- ... AT EACH SLOT.
sameSlot : (A B : Gr) → A ⊛ B
         → ∀ {u₁ v₁ u₂ v₂ w} (s₁ : Split3 u₁ v₁ w) (s₂ : Split3 u₂ v₂ w)
         → A u₁ → B v₁ → A u₂ → B v₂
         → (i : Bool) → partsH appHom _ (u₁ , v₁ , s₁) i
                        Eq.≡ partsH appHom _ (u₂ , v₂ , s₂) i
sameSlot A B su {u₁} {v₁} {u₂} {v₂} {w} s₁ s₂ a₁ b₁ a₂ b₂ =
  strSameParts A B su w (u₁ , v₁ , s₁) (u₂ , v₂ , s₂)
    (λ { true → a₁ ; false → b₁ }) (λ { true → a₂ ; false → b₂ })

-- the two halves of `SeqUnambig.sameParts`, each on its own
recoversˡ : {A B : Gr} → A ⊛ B
          → ∀ {u₁ v₁ u₂ v₂ w} → Split3 u₁ v₁ w → Split3 u₂ v₂ w
          → A u₁ → B v₁ → A u₂ → B v₂ → u₁ Eq.≡ u₂
recoversˡ {A} {B} su s₁ s₂ a₁ b₁ a₂ b₂ =
  sameSlot A B su s₁ s₂ a₁ b₁ a₂ b₂ true

recoversʳ : {A B : Gr} → A ⊛ B
          → ∀ {u₁ v₁ u₂ v₂ w} → Split3 u₁ v₁ w → Split3 u₂ v₂ w
          → A u₁ → B v₁ → A u₂ → B v₂ → v₁ Eq.≡ v₂
recoversʳ {A} {B} su s₁ s₂ a₁ b₁ a₂ b₂ =
  sameSlot A B su s₁ s₂ a₁ b₁ a₂ b₂ false

-- ... and their pairing IS `SeqUnambig.sameParts`, whose statement is
-- the conjunction.  Kept only to witness that coincidence: prefer
-- `recoversˡ`/`recoversʳ`.
recovers : {A B : Gr} → A ⊛ B
         → ∀ {u₁ v₁ u₂ v₂ w} → Split3 u₁ v₁ w → Split3 u₂ v₂ w
         → A u₁ → B v₁ → A u₂ → B v₂ → (u₁ Eq.≡ u₂) × (v₁ Eq.≡ v₂)
recovers su s₁ s₂ a₁ b₁ a₂ b₂ =
    recoversˡ su s₁ s₂ a₁ b₁ a₂ b₂
  , recoversʳ su s₁ s₂ a₁ b₁ a₂ b₂
