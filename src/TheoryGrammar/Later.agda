{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The later modality over an arbitrary well-founded order. -}
module TheoryGrammar.Later where

open import Cubical.Foundations.Prelude
open import Cubical.Induction.WellFounded

open import TheoryGrammar.BaseChange

-- THE LATER MODALITY, GENERIC IN THE ORDER. The header above says "the
-- order can be made abstract later if a lexicographic instance needs it".
module WFLater {ℓI ℓR : Level} {I : Type ℓI} (_≺_ : I → I → Type ℓR)
               (≺-wf : WellFounded _≺_) where

  ▷ : {ℓM : Level} → (I → Type ℓM) → I → Type (ℓ-max ℓI (ℓ-max ℓR ℓM))
  ▷ A i = (j : I) → j ≺ i → A j

  next : {ℓM : Level} {A : I → Type ℓM} → ((i : I) → A i) → (i : I) → ▷ A i
  next f i j _ = f j

  löb : {ℓM : Level} {A : I → Type ℓM}
      → ((i : I) → ▷ A i → A i) → (i : I) → A i
  löb {A = A} step = WFI.induction ≺-wf λ i rec → step i (λ j q → rec j q)

  -- `▷` IS base change: `Πᴿ` at the relation "j is smaller than i".
  -- Not an analogy -- `refl`.
  ▷≡Πᴿ : {ℓM : Level} {A : I → Type ℓM}
       → ▷ A ≡ Rel.Πᴿ (λ i j → j ≺ i) A
  ▷≡Πᴿ = refl

  -- löb IS THE UNIQUE FIXED POINT. `löb step` solves `f i = step i (λ j _
  -- → f j)`, and it is the ONLY solution.

  löb-unfold : {ℓM : Level} {A : I → Type ℓM} (step : (i : I) → ▷ A i → A i)
             → (i : I) → löb step i ≡ step i (λ j _ → löb step j)
  löb-unfold step = WFI.induction-compute ≺-wf (λ i rec → step i (λ j q → rec j q))

  löb-unique : {ℓM : Level} {A : I → Type ℓM} (step : (i : I) → ▷ A i → A i)
               (f : (i : I) → A i)
             → ((i : I) → f i ≡ step i (λ j _ → f j))
             → (i : I) → f i ≡ löb step i
  löb-unique step f hf = WFI.induction ≺-wf go
    where
      go : (i : I) → ((j : I) → j ≺ i → f j ≡ löb step j) → f i ≡ löb step i
      go i ih = hf i
              ∙ cong (step i) (funExt λ j → funExt λ q → ih j q)
              ∙ sym (löb-unfold step i)

  -- CHANGING THE CARRIER CANNOT CHANGE THE ANSWER. A recurrence is often
  -- solved in a DIFFERENT representation from the one it is stated in --
  -- `A` re-tabulated as `B` so that a memo table can share more of it
  -- (`Enumerable.tabulate'` is the case that motivates this).

  löb-conj : {ℓM ℓN : Level} {A : I → Type ℓM} {B : I → Type ℓN}
             (stA : (i : I) → ▷ A i → A i)
             (stB : (i : I) → ▷ B i → B i)
             (to  : (i : I) → A i → B i)
           → ((i : I) (r : ▷ A i) → stB i (λ j q → to j (r j q)) ≡ to i (stA i r))
           → (i : I) → löb stB i ≡ to i (löb stA i)
  löb-conj stA stB to conj i =
    sym (löb-unique stB (λ k → to k (löb stA k)) hf i)
    where
      hf : (k : I) → to k (löb stA k) ≡ stB k (λ j _ → to j (löb stA j))
      hf k = cong (to k) (löb-unfold stA k)
           ∙ sym (conj k (λ j _ → löb stA j))

  -- THE CASE THAT ACTUALLY ARISES. One does not usually write the second
  -- step by hand: one CONJUGATES the first, `to ∘ st ∘ ▷ from`, and then
  -- the intertwining hypothesis is not something to prove but something
  -- that follows from `from ∘ to ≡ id`.
  löb-retract : {ℓM ℓN : Level} {A : I → Type ℓM} {B : I → Type ℓN}
                (stA : (i : I) → ▷ A i → A i)
                (to  : (i : I) → A i → B i)
                (from : (i : I) → B i → A i)
              → ((i : I) (a : A i) → from i (to i a) ≡ a)
              → (i : I)
              → löb (λ k s → to k (stA k (λ j q → from j (s j q)))) i
                ≡ to i (löb stA i)
  löb-retract {A = A} stA to from retr =
    löb-conj stA (λ k s → to k (stA k (λ j q → from j (s j q)))) to conj
    where
      conj : (i : I) (r : ▷ A i)
           → to i (stA i (λ j q → from j (to j (r j q)))) ≡ to i (stA i r)
      conj i r = cong (λ z → to i (stA i z))
                      (funExt λ j → funExt λ q → retr j (r j q))

-- A FINER order gives a WEAKER modality: fewer `j ≺ i` means fewer
-- assumptions available in the löb step.
▷-mono : {ℓI ℓR ℓR' ℓM : Level} {I : Type ℓI}
         {_≺_ : I → I → Type ℓR} {_≺'_ : I → I → Type ℓR'}
       → ({i j : I} → i ≺' j → i ≺ j)
       → {A : I → Type ℓM} {i : I}
       → ((j : I) → j ≺ i → A j) → ((j : I) → j ≺' i → A j)
▷-mono sub r j q = r j (sub q)

