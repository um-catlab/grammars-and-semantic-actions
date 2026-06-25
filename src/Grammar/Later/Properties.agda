open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Later.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure

open import Cubical.Data.List

open import Grammar.Base Alphabet
open import Grammar.Bottom Alphabet
open import Grammar.Distributivity Alphabet
open import Grammar.Function Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.Product Alphabet
open import Grammar.Product.Binary.AsPrimitive Alphabet
open import Grammar.String Alphabet
open import Grammar.Sum Alphabet
open import Grammar.Top Alphabet
open import Grammar.Later.Base Alphabet
open import Grammar.External.String.Tiny Alphabet
open import Grammar.SequentialUnambiguity.Nullable Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Term.Base Alphabet

open import Cubical.Data.List using (rev ; rev-rev)
open import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open import Grammar.Later.SuffixOrder Alphabet using (_<ˢ_)

open StrongEquivalence

private
  variable
    ℓA ℓB ℓC : Level
    A : Grammar ℓA
    B : Grammar ℓB

opaque
  unfolding _⊗_ _&_ ⊤
  -- Peel a known nonempty prefix w: the residual is a strict suffix, so
  -- ▷ A delivers A there.  Factors through ▷-elim-at (the `α (right split) …`).
  ▷-app-⌈⌉ : ∀ (w : NonEmptyString) →
    (⌈ w .fst ⌉ ⊗ ⊤) & ▷ A ⊢ ⌈ w .fst ⌉ ⊗ A
  ▷-app-⌈⌉ {A = A} w s ((split , cv , _) , α) =
    split , cv , α r residual<ˢs
    where
      l r : String
      l = split .fst .fst
      r = split .fst .snd
      w≡l : w .fst Eq.≡ l
      w≡l = uniquely-supported-⌈⌉Eq (w .fst) l cv
      lne : l Eq.≡ [] → Empty.⊥
      lne e = w .snd (Eq.eqToPath (w≡l Eq.∙ e))
      residual<ˢs : r <ˢ s
      residual<ˢs = l , lne , Eq.sym (split .snd)

  -- Symmetric: peel a known nonempty suffix w; the residual prefix is strict.
  ▷r-app-⌈⌉ : ∀ (w : NonEmptyString) →
    (⊤ ⊗ ⌈ w .fst ⌉) & ▷r A ⊢ A ⊗ ⌈ w .fst ⌉
  ▷r-app-⌈⌉ {A = A} w s ((split , _ , cv) , α) =
    split , α l residual<ᵖs , cv
    where
      l r : String
      l = split .fst .fst
      r = split .fst .snd
      w≡r : w .fst Eq.≡ r
      w≡r = uniquely-supported-⌈⌉Eq (w .fst) r cv
      rne : rev r Eq.≡ [] → Empty.⊥
      rne e = w .snd (Eq.eqToPath w≡r ∙ sym (rev-rev r) ∙ cong rev (Eq.eqToPath e))
      residual<ᵖs : rev l <ˢ rev s
      residual<ᵖs =
        rev r , rne ,
        ( Eq.sym (++-rev-Eq l r) Eq.∙ Eq.ap rev (Eq.sym (split .snd)) )

▷-app-NE-keep-⌈⌉ : ∀ {ℓC} {C : Grammar ℓC} (w : NonEmptyString) →
  (⌈ w .fst ⌉ ⊗ C) & ▷ A ⊢ ⌈ w .fst ⌉ ⊗ (C & A)
▷-app-NE-keep-⌈⌉ w =
  ⌈⌉-⊗&-distL⁻Eq {w = w .fst}
  ∘g π₁ ,& (▷-app-⌈⌉ w ∘g (id ,⊗ ⊤-intro) ,&p id)

▷r-app-NE-keep-⌈⌉ : ∀ {ℓC} {C : Grammar ℓC} (w : NonEmptyString) →
  (C ⊗ ⌈ w .fst ⌉) & ▷r A ⊢ (C & A) ⊗ ⌈ w .fst ⌉
▷r-app-NE-keep-⌈⌉ w =
  ⌈⌉-⊗&-distR⁻Eq {w = w .fst}
  ∘g π₁ ,& (▷r-app-⌈⌉ w ∘g (⊤-intro ,⊗ id) ,&p id)

▷-app-NE : ⟨ ¬Nullable B ⟩ → (B ⊗ ⊤) & ▷ A ⊢ B ⊗ A
▷-app-NE {B = B} {A = A} ¬nullB =
  ⊕ᴰ-elim per-w
  ∘g &⊕ᴰ-distL≅ .fun
  ∘g (⊕ᴰ-distL .fun
      ∘g (&⊕ᴰ-distR≅ .fun
          ∘g id ,&p ⊤→⊕⌈⌉
          ∘g id ,& ⊤-intro) ,⊗ id) ,&p id
  where
    per-w : ∀ (w : String) →
      ((B & ⌈ w ⌉) ⊗ ⊤) & ▷ A ⊢ B ⊗ A
    per-w [] =
      ⊥-elim
      ∘g ⊥⊗
      ∘g (¬nullB ∘g &-swap) ,⊗ id
      ∘g π₁
    per-w (c ∷ rest) =
      π₁ ,⊗ π₂
      ∘g ⌈⌉-⊗&-keep-distL⁻Eq {w = c ∷ rest}
      ∘g π₁
         ,& (▷-app-⌈⌉ ((c ∷ rest) , ¬cons≡nil)
             ∘g (π₂ ,⊗ id) ,&p id)
