{- CHANGE OF THEORY: reinterpreting a derivation at another theory. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.ChangeOfTheory where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base

private variable ℓS ℓS' ℓ ℓ' ℓ2 ℓ2' ℓX ℓY ℓA ℓB ℓV : Level

-- (1) CHANGE OF MODEL.

record ModelHom {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
                (M : Model σ ℓX) (N : Model σ ℓY)
  : Type (ℓ-max ℓS (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓX ℓY)))) where
  field
    hom   : (s : S) → M .carrier s → N .carrier s
    homOp : (o : σ .ops) (m⃗ : (a : σ .arities o) → M .carrier (σ .sortOf o a))
          → hom _ (M .op o m⃗) Eq.≡ N .op o (λ a → hom _ (m⃗ a))

open ModelHom public

module Reinterpret {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
                   {M : Model σ ℓX} {N : Model σ ℓY} (h : ModelHom M N) where

  private
    module 𝕄 = Notation M
    module ℕ = Notation N

  -- the reinterpretation of types
  pull : {s : S} → ℕ.TheoryTy ℓA s → 𝕄.TheoryTy ℓA s
  pull {s = s} B m = B (h .hom s m)

  -- and of derivations: EVERY term reinterprets, with no cost
  pullTerm : {s : S} {A B : ℕ.TheoryTy ℓA s}
           → A ℕ.⊢ B → pull A 𝕄.⊢ pull B
  pullTerm f m x = f _ x

  -- The additive fragment is preserved ON THE NOSE.

  pull-⊤ : {s : S} → pull (ℕ.⊤G {s}) ≡ 𝕄.⊤G
  pull-⊤ = refl

  pull-⊥ : {s : S} → pull (ℕ.⊥G {s}) ≡ 𝕄.⊥G
  pull-⊥ = refl

  pull-& : {s : S} (A : ℕ.TheoryTy ℓA s) (B : ℕ.TheoryTy ℓB s)
         → pull (A ℕ.& B) ≡ (pull A 𝕄.& pull B)
  pull-& _ _ = refl

  pull-⊕ : {s : S} (A : ℕ.TheoryTy ℓA s) (B : ℕ.TheoryTy ℓB s)
         → pull (A ℕ.⊕ B) ≡ (pull A 𝕄.⊕ pull B)
  pull-⊕ _ _ = refl

  pull-⇒ : {s : S} (A : ℕ.TheoryTy ℓA s) (B : ℕ.TheoryTy ℓB s)
         → pull (A ℕ.⇒ B) ≡ (pull A 𝕄.⇒ pull B)
  pull-⇒ _ _ = refl

  pull-⊕ᴰ : {s : S} (Y : Type ℓV) (A : Y → ℕ.TheoryTy ℓA s)
          → pull (ℕ.⊕ᴰ Y A) ≡ 𝕄.⊕ᴰ Y (λ y → pull (A y))
  pull-⊕ᴰ _ _ = refl

  pull-&ᴰ : {s : S} (Y : Type ℓV) (A : Y → ℕ.TheoryTy ℓA s)
          → pull (ℕ.&ᴰ Y A) ≡ 𝕄.&ᴰ Y (λ y → pull (A y))
  pull-&ᴰ _ _ = refl

  -- The multiplicative fragment is only LAX.

  module _ (o : σ .ops) {B : (a : σ .arities o) → ℕ.TheoryTy ℓA (σ .sortOf o a)} where

    -- the canonical direction always exists, and is transport-free
    -- PRIMITIVE (phase 1): the construction of the change of model.
    pull⊗ : 𝕄.⊗[ o ] (λ a → pull (B a)) 𝕄.⊢ pull (ℕ.⊗[ o ] B)
    pull⊗ .(M .op o m⃗) (m⃗ , Eq.refl , g) =
      (λ a → h .hom _ (m⃗ a)) , Eq.sym (h .homOp o m⃗) , g

  -- ... and is invertible exactly when h REFLECTS SPLITTINGS.
  -- This is the discrete Conduché condition.

  ReflectsSplit : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓX ℓY)))
  ReflectsSplit =
    (o : σ .ops) (m : M .carrier (σ .resultSort o))
    (n⃗ : (a : σ .arities o) → N .carrier (σ .sortOf o a))
    → N .op o n⃗ Eq.≡ h .hom _ m
    → Σ[ m⃗ ∈ ((a : σ .arities o) → M .carrier (σ .sortOf o a)) ]
        ((M .op o m⃗ Eq.≡ m) × ((a : σ .arities o) → h .hom _ (m⃗ a) Eq.≡ n⃗ a))

  module _ (rs : ReflectsSplit) (o : σ .ops)
           {B : (a : σ .arities o) → ℕ.TheoryTy ℓA (σ .sortOf o a)} where

    private
      coeB : {a : σ .arities o} {x y : N .carrier (σ .sortOf o a)}
           → x Eq.≡ y → B a y → B a x
      coeB Eq.refl b = b

    -- PRIMITIVE (phase 1): the construction of the change of model.
    pull⊗⁻ : pull (ℕ.⊗[ o ] B) 𝕄.⊢ 𝕄.⊗[ o ] (λ a → pull (B a))
    pull⊗⁻ m (n⃗ , e , g) =
      let (m⃗ , em , ea) = rs o m n⃗ e
      in m⃗ , em , λ a → coeB (ea a) (g a)

-- (2) CHANGE OF SIGNATURE.

record SigMor {S : Type ℓS} {S' : Type ℓS'}
              (σ : SortedSig S ℓ ℓ') (τ : SortedSig S' ℓ2 ℓ2')
  : Type (ℓ-max ℓS (ℓ-max ℓS' (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓ2 ℓ2'))))) where
  field
    onSort : S → S'
    onOp   : σ .ops → τ .ops
    -- CONTRAVARIANT on arities: to build a τ-tuple from a σ-tuple.
    onAr   : (o : σ .ops) → τ .arities (onOp o) → σ .arities o
    resEq  : (o : σ .ops) → τ .resultSort (onOp o) Eq.≡ onSort (σ .resultSort o)
    sortEq : (o : σ .ops) (b : τ .arities (onOp o))
           → τ .sortOf (onOp o) b Eq.≡ onSort (σ .sortOf o (onAr o b))

open SigMor public

module _ {S : Type ℓS} {S' : Type ℓS'}
         {σ : SortedSig S ℓ ℓ'} {τ : SortedSig S' ℓ2 ℓ2'}
         (φ : SigMor σ τ) (N : Model τ ℓX) where

  private
    coeN : {s t : S'} → s Eq.≡ t → N .carrier s → N .carrier t
    coeN Eq.refl x = x

  restrict : Model σ ℓX
  restrict .carrier s = N .carrier (φ .onSort s)
  restrict .op o m⃗ =
    coeN (φ .resEq o)
      (N .op (φ .onOp o) (λ b → coeN (Eq.sym (φ .sortEq o b)) (m⃗ (φ .onAr o b))))

  -- THE POINT. σ-types over the restricted model are DEFINITIONALLY
  -- τ-types over N at the translated sort -- so a derivation written in
  -- the σ-calculus already IS a derivation in the τ-calculus.
  reinterpretTy : (s : S)
                → Notation.TheoryTy restrict ℓA s
                ≡ Notation.TheoryTy N ℓA (φ .onSort s)
  reinterpretTy s = refl

  reinterpretTerm : {s : S}
                    (A B : Notation.TheoryTy restrict ℓA s)
                  → Notation._⊢_ restrict A B ≡ Notation._⊢_ N A B
  reinterpretTerm A B = refl
