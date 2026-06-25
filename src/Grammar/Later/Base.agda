open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Later.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure

open import Cubical.Data.List
open import Cubical.Data.List.Properties
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open import Cubical.Induction.WellFounded

open import Grammar.Base Alphabet
open import Grammar.Function Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.Product Alphabet
open import Grammar.String Alphabet
open import Grammar.Top Alphabet
open import Grammar.Derivative.String Alphabet
open import Term.Base Alphabet

private
  variable
    ℓA : Level
    A : Grammar ℓA

▷ : Grammar ℓA → Grammar ℓA
▷ A = &[ w ∈ NonEmptyString ] √l-string (w .fst) A

▷r : Grammar ℓA → Grammar ℓA
▷r A = &[ w ∈ NonEmptyString ] √r-string (w .fst) A

-- TODO move these to a List file
private
  length-pos : ∀ {ℓ} {X : Type ℓ} (xs : List X)
             → (xs ≡ [] → Empty.⊥) → 0 < length xs
  length-pos [] ne = Empty.rec (ne refl)
  length-pos (x ∷ xs) _ = length xs , +-comm (length xs) 1

  length++Eq : (xs ys : List ⟨ Alphabet ⟩)
            → length (xs ++ ys) Eq.≡ length xs + length ys
  length++Eq [] ys = Eq.refl
  length++Eq (x ∷ xs) ys = Eq.ap suc (length++Eq xs ys)

  -- Eq-world commutativity for ℕ addition. Local to keep Löb in Eq world.
  +-zero-Eq : ∀ n → n + 0 Eq.≡ n
  +-zero-Eq zero = Eq.refl
  +-zero-Eq (suc n) = Eq.ap suc (+-zero-Eq n)

  +-suc-Eq : ∀ m n → m + suc n Eq.≡ suc (m + n)
  +-suc-Eq zero n = Eq.refl
  +-suc-Eq (suc m) n = Eq.ap suc (+-suc-Eq m n)

  +-commEq : ∀ m n → m + n Eq.≡ n + m
  +-commEq zero n = Eq.sym (+-zero-Eq n)
  +-commEq (suc m) n =
    Eq.ap suc (+-commEq m n) Eq.∙ Eq.sym (+-suc-Eq n m)

-- the Löb motive: an `A`-value at every string of a given length
Plob : ∀ {ℓA} → Grammar ℓA → ℕ → Type ℓA
Plob A n = (w'' : String) → length w'' Eq.≡ n → A w''

opaque
  unfolding _⇒_ _⊗_ ⊤

  -- Löb induction, with the recursion machinery exposed (rather than buried in
  -- a `where`) so we can state its fixed-point unfolding.  `lob-build` packages
  -- the "build a `▷ A w''` from `A` at strictly shorter strings" step (it is the
  -- only piece that pattern-matches the √/⊗ structure, so it lives directly in
  -- the opaque block); `lob` is the well-founded recursion; `lob-next` is `lob`'s
  -- canonical delay; `lob-unfold` is the fixed-point equation (induction-compute).

  lob-build : ∀ {ℓA} {A : Grammar ℓA} (w'' : String)
    → (∀ v₂ → length v₂ < length w'' → A v₂) → ▷ A w''
  lob-build w'' rec (v , vne) (((v₁ , v₂) , w''≡v₁v₂) , (cv , _)) =
    ((v₁ , v₂) , w''≡v₁v₂) , (cv , rec v₂ lv₂<lw'')
    where
      v≡v₁ : v ≡ v₁
      v≡v₁ = uniquely-supported-⌈⌉ v v₁ cv

      v₁ne : v₁ ≡ [] → Empty.⊥
      v₁ne v₁≡[] = vne (v≡v₁ ∙ v₁≡[])

      0<lv₁ : 0 < length v₁
      0<lv₁ = length-pos v₁ v₁ne

      lv₂<lw'' : length v₂ < length w''
      lv₂<lw'' =
        Eq.transport (length v₂ <_)
          (Eq.sym (Eq.ap length w''≡v₁v₂ Eq.∙ length++Eq v₁ v₂))
          (<-+k 0<lv₁)

  module _ {ℓA} {A : Grammar ℓA} (f : ▷ A ⊢ A) where
    open WFI <-wellfounded

    private
      lob-step : ∀ n → (∀ m → m < n → Plob A m) → Plob A n
      lob-step n IH w'' lw''≡n =
        f w'' (lob-build w'' (λ v₂ lv₂<lw'' →
          IH (length v₂) (Eq.transport (length v₂ <_) lw''≡n lv₂<lw'') v₂ Eq.refl))

      lob-rec : ∀ n → Plob A n
      lob-rec = induction lob-step

    lob : ⊤ ⊢ A
    lob w' _ = lob-rec (length w') w' Eq.refl

    -- the canonical delay of `lob`: a `▷ A` assembled from `lob` at shorter strings
    lob-next : ⊤ ⊢ ▷ A
    lob-next w' _ = lob-build w' (λ v₂ _ → lob-rec (length v₂) v₂ Eq.refl)

    -- the guarded fixed-point equation: `lob` unfolds to `f` applied to its delay
    lob-unfold : lob ≡ f ∘g lob-next
    lob-unfold = funExt λ w' → funExt λ x →
      cong (λ z → z w' Eq.refl) (induction-compute lob-step (length w'))

  lob-r : ∀ {ℓA} {A : Grammar ℓA} → (▷r A ⊢ A) → ⊤ ⊢ A
  lob-r {ℓA = ℓA} {A = A} f w' _ = lob-len (length w') w' Eq.refl
    where
      open WFI <-wellfounded

      P : ℕ → Type ℓA
      P n = (w'' : String) → length w'' Eq.≡ n → A w''

      step : ∀ n → (∀ m → m < n → P m) → P n
      step n IH w'' lw''≡n = f w'' build-▷r
        where
          build-▷r : ▷r A w''
          build-▷r (v , vne) (((v₁ , v₂) , w''≡v₁v₂) , (_ , cv)) =
            ((v₁ , v₂) , w''≡v₁v₂) , (A-v₁ , cv)
            where
              v≡v₂ : v ≡ v₂
              v≡v₂ = uniquely-supported-⌈⌉ v v₂ cv

              v₂ne : v₂ ≡ [] → Empty.⊥
              v₂ne v₂≡[] = vne (v≡v₂ ∙ v₂≡[])

              0<lv₂ : 0 < length v₂
              0<lv₂ = length-pos v₂ v₂ne

              lv₁<lw'' : length v₁ < length w''
              lv₁<lw'' =
                Eq.transport (length v₁ <_)
                  (Eq.sym (Eq.ap length w''≡v₁v₂ Eq.∙ length++Eq v₁ v₂))
                  (Eq.transport (length v₁ <_)
                    (+-commEq (length v₂) (length v₁))
                    (<-+k 0<lv₂))

              A-v₁ : A v₁
              A-v₁ =
                IH (length v₁)
                   (Eq.transport (length v₁ <_) lw''≡n lv₁<lw'')
                   v₁ Eq.refl

      lob-len : ∀ n → P n
      lob-len = induction step
