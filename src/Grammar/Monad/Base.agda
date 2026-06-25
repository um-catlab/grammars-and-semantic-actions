{- Monads on the category of grammars, given *semantically* — the exact dual
   of Grammar.Comonad.Base. A monad is an endofunctor (F₀ , F₁) with a unit η
   and a multiplication μ satisfying the monad laws, and an algebra is a
   structure map F₀ A ⊢ A compatible with η and μ.

   As with the comonad, we fix a single level ℓ and do not route through the
   `SPFunctor` syntactic codes. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Monad.Base (Alphabet : hSet ℓ-zero) where

open import Grammar.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓ : Level

record Monad (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    -- underlying endofunctor
    F₀ : Grammar ℓ → Grammar ℓ
    F₁ : {A B : Grammar ℓ} → A ⊢ B → F₀ A ⊢ F₀ B
    F-id  : {A : Grammar ℓ} → F₁ (id {A = A}) ≡ id
    F-seq : {A B C : Grammar ℓ} (f : A ⊢ B) (g : B ⊢ C)
          → F₁ (g ∘g f) ≡ F₁ g ∘g F₁ f
    -- monad structure
    η : {A : Grammar ℓ} → A ⊢ F₀ A
    μ : {A : Grammar ℓ} → F₀ (F₀ A) ⊢ F₀ A
    -- naturality of the structure maps
    η-nat : {A B : Grammar ℓ} (f : A ⊢ B) → η ∘g f ≡ F₁ f ∘g η
    μ-nat : {A B : Grammar ℓ} (f : A ⊢ B) → μ ∘g F₁ (F₁ f) ≡ F₁ f ∘g μ
    -- monad laws
    unit-l : {A : Grammar ℓ} → μ ∘g η {A = F₀ A} ≡ id {A = F₀ A}
    unit-r : {A : Grammar ℓ} → μ ∘g F₁ η ≡ id {A = F₀ A}
    assoc  : {A : Grammar ℓ} → μ ∘g μ {A = F₀ A} ≡ μ ∘g F₁ μ

module _ {ℓ} (T : Monad ℓ) where
  open Monad T

  -- An algebra for the monad T: a structure map α compatible with η and μ.
  record Algebra : Type (ℓ-suc ℓ) where
    field
      car : Grammar ℓ
      α : F₀ car ⊢ car
      unit-coh  : α ∘g η ≡ id
      assoc-coh : α ∘g μ ≡ α ∘g F₁ α
  open Algebra public

  record AlgebraHom (X Y : Algebra) : Type ℓ where
    field
      hom  : X .car ⊢ Y .car
      comm : hom ∘g X .α ≡ Y .α ∘g F₁ hom
  open AlgebraHom public

  idAlgebraHom : (X : Algebra) → AlgebraHom X X
  idAlgebraHom X .hom = id
  idAlgebraHom X .comm = cong (X .α ∘g_) (sym F-id)

  compAlgebraHom : {X Y Z : Algebra}
    → AlgebraHom Y Z → AlgebraHom X Y → AlgebraHom X Z
  compAlgebraHom {X}{Y}{Z} g f .hom = g .hom ∘g f .hom
  compAlgebraHom {X}{Y}{Z} g f .comm =
    cong (g .hom ∘g_) (f .comm)
    ∙ cong (_∘g F₁ (f .hom)) (g .comm)
    ∙ cong (Z .α ∘g_) (sym (F-seq (f .hom) (g .hom)))

  -- The free algebra on a grammar A is (F₀ A , μ). The algebra laws are
  -- exactly the monad laws.
  free : Grammar ℓ → Algebra
  free A .car = F₀ A
  free A .α = μ
  free A .unit-coh = unit-l
  free A .assoc-coh = assoc

  -- The forgetful functor is right adjoint to `free`:
  --     AlgebraHom (free A) X  ≅  (A ⊢ X .car).
  free-transpose : {X : Algebra} {A : Grammar ℓ}
    → (A ⊢ X .car) → AlgebraHom (free A) X
  free-transpose {X} g .hom = X .α ∘g F₁ g
  free-transpose {X} g .comm =
    -- (X.α ∘g F₁ g) ∘g μ ≡ X.α ∘g F₁ (X.α ∘g F₁ g)
    cong (X .α ∘g_) (sym (μ-nat g))
    ∙ cong (_∘g F₁ (F₁ g)) (X .assoc-coh)
    ∙ cong (X .α ∘g_) (sym (F-seq (F₁ g) (X .α)))

  free-transpose⁻ : {X : Algebra} {A : Grammar ℓ}
    → AlgebraHom (free A) X → (A ⊢ X .car)
  free-transpose⁻ h = h .hom ∘g η

  free-β : {X : Algebra} {A : Grammar ℓ} (g : A ⊢ X .car)
    → free-transpose⁻ {X} (free-transpose {X} g) ≡ g
  free-β {X} g =
    cong (X .α ∘g_) (sym (η-nat g))
    ∙ cong (_∘g g) (X .unit-coh)
