{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The later modality over an arbitrary well-founded order.

   Nothing here mentions a signature, a promodel, or a grading -- only a
   relation and its well-foundedness.  That is the whole point of the
   file: `Graded` supplies ONE such order (pull back ℕ's `<` along a
   degree), `Grammar/Later/Ordered.agda` supplies others (the suffix and
   infix orders), and a lexicographic instance would be a third. -}
module TheoryGrammar.Later where

open import Cubical.Foundations.Prelude
open import Cubical.Induction.WellFounded

-- ==================================================================
-- THE LATER MODALITY, GENERIC IN THE ORDER.
--
-- The header above says "the order can be made abstract later if a
-- lexicographic instance needs it".  Doing it now costs nothing: ▷,
-- `next` and `löb` never mention the degree, only the relation and its
-- well-foundedness.  The graded order below is then one instance, and
-- `Grammar/Later/Ordered.agda` -- which is generic in a `WFOrder` and
-- instantiated at the suffix and infix orders -- is another.
-- ==================================================================
module WFLater {ℓI ℓR : Level} {I : Type ℓI} (_≺_ : I → I → Type ℓR)
               (≺-wf : WellFounded _≺_) where

  ▷ : {ℓM : Level} → (I → Type ℓM) → I → Type (ℓ-max ℓI (ℓ-max ℓR ℓM))
  ▷ A i = (j : I) → j ≺ i → A j

  next : {ℓM : Level} {A : I → Type ℓM} → ((i : I) → A i) → (i : I) → ▷ A i
  next f i j _ = f j

  löb : {ℓM : Level} {A : I → Type ℓM}
      → ((i : I) → ▷ A i → A i) → (i : I) → A i
  löb {A = A} step = WFI.induction ≺-wf λ i rec → step i (λ j q → rec j q)

-- A FINER order gives a WEAKER modality: fewer `j ≺ i` means fewer
-- assumptions available in the löb step.  So `Later/Infix`'s `▷ⁱ` --
-- the proper-substring order -- is IMPLIED by the graded `▷`, since a
-- proper infix is strictly shorter but not conversely.  That is why
-- `Instances/Strings/CYK.agda` needs no infix modality: the CYK
-- recursion is available already, with a stronger hypothesis.
▷-mono : {ℓI ℓR ℓR' ℓM : Level} {I : Type ℓI}
         {_≺_ : I → I → Type ℓR} {_≺'_ : I → I → Type ℓR'}
       → ({i j : I} → i ≺' j → i ≺ j)
       → {A : I → Type ℓM} {i : I}
       → ((j : I) → j ≺ i → A j) → ((j : I) → j ≺' i → A j)
▷-mono sub r j q = r j (sub q)

