{- Comonads on the category of grammars, given *semantically*.

   A comonad here is a bona-fide endofunctor on grammars (an F₀ on objects
   together with a functorial action F₁) equipped with a counit ε and a
   comultiplication δ satisfying the comonad laws. This deliberately does NOT
   go through the `SPFunctor` syntactic codes of Grammar.Inductive.Functor:
   those codes only describe strictly-positive polynomial functors and cannot
   name something like □ (which is built from the cartesian arrow ⇒).

   We fix a single universe level ℓ: the endofunctor preserves levels and all
   carriers live in `Grammar ℓ`. This is enough for □ (which is
   level-preserving) and keeps everything in `Type (ℓ-suc ℓ)` rather than
   Typeω. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Comonad.Base (Alphabet : hSet ℓ-zero) where

open import Grammar.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓ : Level

record Comonad (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    -- underlying endofunctor
    F₀ : Grammar ℓ → Grammar ℓ
    F₁ : {A B : Grammar ℓ} → A ⊢ B → F₀ A ⊢ F₀ B
    F-id  : {A : Grammar ℓ} → F₁ (id {A = A}) ≡ id
    F-seq : {A B C : Grammar ℓ} (f : A ⊢ B) (g : B ⊢ C)
          → F₁ (g ∘g f) ≡ F₁ g ∘g F₁ f
    -- comonad structure
    ε : {A : Grammar ℓ} → F₀ A ⊢ A
    δ : {A : Grammar ℓ} → F₀ A ⊢ F₀ (F₀ A)
    -- naturality of the structure maps
    ε-nat : {A B : Grammar ℓ} (f : A ⊢ B) → f ∘g ε ≡ ε ∘g F₁ f
    δ-nat : {A B : Grammar ℓ} (f : A ⊢ B) → δ ∘g F₁ f ≡ F₁ (F₁ f) ∘g δ
    -- comonad laws
    counit-l : {A : Grammar ℓ} → ε ∘g δ ≡ id {A = F₀ A}
    counit-r : {A : Grammar ℓ} → F₁ ε ∘g δ ≡ id {A = F₀ A}
    coassoc  : {A : Grammar ℓ} → δ {A = F₀ A} ∘g δ ≡ F₁ δ ∘g δ

module _ {ℓ} (D : Comonad ℓ) where
  open Comonad D

  -- A coalgebra for the comonad D: a coaction γ compatible with ε and δ.
  record Coalgebra : Type (ℓ-suc ℓ) where
    field
      car : Grammar ℓ
      γ : car ⊢ F₀ car
      counit-coh  : ε ∘g γ ≡ id
      coassoc-coh : δ ∘g γ ≡ F₁ γ ∘g γ
  open Coalgebra public

  record CoalgebraHom (X Y : Coalgebra) : Type ℓ where
    field
      hom  : X .car ⊢ Y .car
      comm : F₁ hom ∘g X .γ ≡ Y .γ ∘g hom
  open CoalgebraHom public

  idCoalgebraHom : (X : Coalgebra) → CoalgebraHom X X
  idCoalgebraHom X .hom = id
  idCoalgebraHom X .comm = cong (_∘g X .γ) F-id

  compCoalgebraHom : {X Y Z : Coalgebra}
    → CoalgebraHom Y Z → CoalgebraHom X Y → CoalgebraHom X Z
  compCoalgebraHom {X} g f .hom = g .hom ∘g f .hom
  compCoalgebraHom {X} g f .comm =
    cong (_∘g X .γ) (F-seq (f .hom) (g .hom))
    ∙ cong (F₁ (g .hom) ∘g_) (f .comm)
    ∙ cong (_∘g f .hom) (g .comm)

  -- The cofree coalgebra on a grammar A is (F₀ A , δ). The coalgebra laws
  -- are exactly the comonad laws.
  cofree : Grammar ℓ → Coalgebra
  cofree A .car = F₀ A
  cofree A .γ = δ
  cofree A .counit-coh = counit-l
  cofree A .coassoc-coh = coassoc

  -- The forgetful functor (X ↦ X .car) is left adjoint to `cofree`:
  --     (X .car ⊢ A)  ≅  CoalgebraHom X (cofree A).
  -- This adjunction is the universal property characterising coalgebras
  -- built from the comonad.
  cofree-transpose : {X : Coalgebra} {A : Grammar ℓ}
    → (X .car ⊢ A) → CoalgebraHom X (cofree A)
  cofree-transpose {X} g .hom = F₁ g ∘g X .γ
  cofree-transpose {X} g .comm =
    -- F₁ (F₁ g ∘g γ) ∘g γ ≡ δ ∘g (F₁ g ∘g γ)
    cong (_∘g X .γ) (F-seq (X .γ) (F₁ g))
    ∙ cong (F₁ (F₁ g) ∘g_) (sym (X .coassoc-coh))
    ∙ cong (_∘g X .γ) (sym (δ-nat g))

  cofree-transpose⁻ : {X : Coalgebra} {A : Grammar ℓ}
    → CoalgebraHom X (cofree A) → (X .car ⊢ A)
  cofree-transpose⁻ h = ε ∘g h .hom

  -- One triangle of the adjunction holds on the nose:
  cofree-β : {X : Coalgebra} {A : Grammar ℓ} (g : X .car ⊢ A)
    → cofree-transpose⁻ {X} (cofree-transpose {X} g) ≡ g
  cofree-β {X} g =
    cong (_∘g X .γ) (sym (ε-nat g))
    ∙ cong (g ∘g_) (X .counit-coh)

  -- The other triangle (equality of coalgebra homomorphisms, compared on
  -- their underlying maps) uses counit-r.
  cofree-η : {X : Coalgebra} {A : Grammar ℓ} (h : CoalgebraHom X (cofree A))
    → cofree-transpose {X} (cofree-transpose⁻ {X} h) .hom ≡ h .hom
  cofree-η {X} h =
    -- F₁ (ε ∘g h.hom) ∘g γ ≡ h.hom
    cong (_∘g X .γ) (F-seq (h .hom) ε)
    ∙ cong (F₁ ε ∘g_) (h .comm)
    ∙ cong (_∘g h .hom) counit-r
