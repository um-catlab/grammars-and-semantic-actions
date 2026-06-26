{- Distributivity of `_⊗_` over the binary coproduct `_⊕_`, DERIVED from the
   Lambek adjunction.

   The tensor `(– ⊗ C)` is a left adjoint — its right adjoint is the internal
   hom `(C ⊸ –)`, witnessed by the currying iso `⊸-intro`/`⊸-intro⁻` (see
   `Grammar.LinearFunction.Base`, packaged categorically in
   `Grammar.LinearFunction.Adjoint`).  A left adjoint preserves coproducts, so

       (A ⊕ B) ⊗ C  ≅  (A ⊗ C) ⊕ (B ⊗ C).

   This module spells out that general argument — transpose along the
   adjunction, use the coproduct universal property (`⊕-elim`/`⊕≡`), transpose
   back — for the binary coproduct.  It REDERIVES `⊗⊕-distR`; the bespoke,
   definitionally-computing iso in `Grammar.Sum.Binary.AsPrimitive.Base` is left
   in place (the refl-tests depend on its computation), so this is an additive
   demonstration of the categorical structure, not a replacement.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Sum.Binary.AsPrimitive.Distributivity (Alphabet : hSet ℓ-zero) where

open import Grammar.Base Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.LinearFunction.Base Alphabet
open import Grammar.Sum.Binary.AsPrimitive.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓA ℓB ℓC ℓD : Level

open StrongEquivalence

-- Naturality of `⊸-intro` in its domain: precomposing the transpose is the
-- transpose of the precomposition (tensored with the identity on the right).
-- This is the only "adjoint" coherence used below beyond β/η and mapCod.
⊸-intro-precompDom :
  ∀ {X : Grammar ℓA}{Z : Grammar ℓB}{W : Grammar ℓC}{Y : Grammar ℓD}
  (m : X ⊗ Z ⊢ W) (g : Y ⊢ X)
  → ⊸-intro m ∘g g ≡ ⊸-intro (m ∘g (g ,⊗ id))
⊸-intro-precompDom m g =
  sym (⊸-η (⊸-intro m ∘g g))
  ∙ cong ⊸-intro
      ( cong (⊸-app ∘g_)
          (sym (⊗-intro⊗-intro {f = ⊸-intro m}{f' = id}{f'' = g}{f''' = id}))
      ∙ cong (_∘g (g ,⊗ id)) (⊸-β m) )

module _ {A : Grammar ℓA} {B : Grammar ℓB} {C : Grammar ℓC} where

  private
    -- the coproduct injections of the codomain
    inlD : A ⊗ C ⊢ (A ⊗ C) ⊕ (B ⊗ C)
    inlD = inl
    inrD : B ⊗ C ⊢ (A ⊗ C) ⊕ (B ⊗ C)
    inrD = inr

    -- E : (A ⊕ B) ⊢ C ⊸ ((A⊗C) ⊕ (B⊗C)), the transposed cotuple
    E : (A ⊕ B) ⊢ C ⊸ ((A ⊗ C) ⊕ (B ⊗ C))
    E = ⊕-elim (⊸-intro inlD) (⊸-intro inrD)

    -- forward = transpose⁻¹ of E  : (A⊕B)⊗C ⊢ (A⊗C)⊕(B⊗C)
    fwd : (A ⊕ B) ⊗ C ⊢ (A ⊗ C) ⊕ (B ⊗ C)
    fwd = ⊸-intro⁻ E

    -- inverse = the functorial action of (–⊗C) on inl/inr, cotupled
    bwd : (A ⊗ C) ⊕ (B ⊗ C) ⊢ (A ⊕ B) ⊗ C
    bwd = ⊕-elim (inl ,⊗ id) (inr ,⊗ id)

    the-sec : fwd ∘g bwd ≡ id
    the-sec = ⊕≡ _ _
      ( cong (fwd ∘g_) (⊕-βl (inl ,⊗ id) (inr ,⊗ id))
      ∙ cong (⊸-app ∘g_) (⊗-intro⊗-intro {f = E}{f' = id}{f'' = inl}{f''' = id})
      ∙ cong (λ z → ⊸-app ∘g ⊗-intro z id) (⊕-βl (⊸-intro inlD) (⊸-intro inrD))
      ∙ ⊸-β inlD )
      ( cong (fwd ∘g_) (⊕-βr (inl ,⊗ id) (inr ,⊗ id))
      ∙ cong (⊸-app ∘g_) (⊗-intro⊗-intro {f = E}{f' = id}{f'' = inr}{f''' = id})
      ∙ cong (λ z → ⊸-app ∘g ⊗-intro z id) (⊕-βr (⊸-intro inlD) (⊸-intro inrD))
      ∙ ⊸-β inrD )

    -- the key step: ⊸-mapCod bwd ∘g E ≡ ⊸-intro id  (used to invert fwd)
    mapCod-E : ⊸-mapCod bwd ∘g E ≡ ⊸-intro id
    mapCod-E = ⊕≡ _ _
      ( cong (⊸-mapCod bwd ∘g_) (⊕-βl (⊸-intro inlD) (⊸-intro inrD))
      ∙ ⊸-mapCod-precomp bwd inlD
      ∙ cong ⊸-intro (⊕-βl (inl ,⊗ id) (inr ,⊗ id))
      ∙ sym (⊸-intro-precompDom id inl) )
      ( cong (⊸-mapCod bwd ∘g_) (⊕-βr (⊸-intro inlD) (⊸-intro inrD))
      ∙ ⊸-mapCod-precomp bwd inrD
      ∙ cong ⊸-intro (⊕-βr (inl ,⊗ id) (inr ,⊗ id))
      ∙ sym (⊸-intro-precompDom id inr) )

    the-ret : bwd ∘g fwd ≡ id
    the-ret =
      sym (⊸-β (bwd ∘g fwd))
      ∙ cong ⊸-intro⁻
          ( sym (⊸-mapCod-precomp bwd (⊸-intro⁻ E))
          ∙ cong (⊸-mapCod bwd ∘g_) (⊸-η E)
          ∙ mapCod-E )
      ∙ ⊸-β id

  ⊗⊕-distR-cat≅ : (A ⊕ B) ⊗ C ≅ (A ⊗ C) ⊕ (B ⊗ C)
  ⊗⊕-distR-cat≅ = mkStrEq fwd bwd the-sec the-ret

------------------------------------------------------------------------
-- The other tensor side, via the MIRROR adjunction `(A ⊗ –) ⊣ (– ⟜ A)`.
-- (Lambek `⊗` is non-commutative, so this is a genuinely separate fact —
-- there is no `⊗`-swap to reduce it to the `– ⊗ C` case.)
------------------------------------------------------------------------

-- The `⟜` mirror of `⊸-mapCod-precomp` (absent upstream; refl after unfolding,
-- exactly like the `⊸` version in `Grammar.LinearFunction.Base`).
opaque
  unfolding ⟜-intro
  ⟜-mapCod-precomp : ∀ {A : Grammar ℓA}{B : Grammar ℓB}{C : Grammar ℓC}{D : Grammar ℓD}
    (e : A ⊢ B)(f : C ⊗ D ⊢ A)
    → ⟜-mapCod e ∘g ⟜-intro f ≡ ⟜-intro (e ∘g f)
  ⟜-mapCod-precomp e f = refl

-- The `⟜` mirror of `⊸-intro-precompDom`; here the variable factor is on the
-- right (`A ⊗ –`), so we tensor with the identity on the left.
⟜-intro-precompDom :
  ∀ {X : Grammar ℓA}{Z : Grammar ℓB}{W : Grammar ℓC}{Y : Grammar ℓD}
  (m : Z ⊗ X ⊢ W) (g : Y ⊢ X)
  → ⟜-intro m ∘g g ≡ ⟜-intro (m ∘g (id ,⊗ g))
⟜-intro-precompDom m g =
  ⟜-η (⟜-intro m ∘g g)
  ∙ cong ⟜-intro
      ( cong (⟜-app ∘g_)
          (sym (⊗-intro⊗-intro {f = id}{f' = ⟜-intro m}{f'' = id}{f''' = g}))
      ∙ cong (_∘g (id ,⊗ g)) (⟜-β m) )

module _ {A : Grammar ℓA} {B : Grammar ℓB} {C : Grammar ℓC} where

  private
    inlD : A ⊗ B ⊢ (A ⊗ B) ⊕ (A ⊗ C)
    inlD = inl
    inrD : A ⊗ C ⊢ (A ⊗ B) ⊕ (A ⊗ C)
    inrD = inr

    E : (B ⊕ C) ⊢ ((A ⊗ B) ⊕ (A ⊗ C)) ⟜ A
    E = ⊕-elim (⟜-intro inlD) (⟜-intro inrD)

    fwd : A ⊗ (B ⊕ C) ⊢ (A ⊗ B) ⊕ (A ⊗ C)
    fwd = ⟜-intro⁻ E

    bwd : (A ⊗ B) ⊕ (A ⊗ C) ⊢ A ⊗ (B ⊕ C)
    bwd = ⊕-elim (id ,⊗ inl) (id ,⊗ inr)

    the-sec : fwd ∘g bwd ≡ id
    the-sec = ⊕≡ _ _
      ( cong (fwd ∘g_) (⊕-βl (id ,⊗ inl) (id ,⊗ inr))
      ∙ cong (⟜-app ∘g_) (⊗-intro⊗-intro {f = id}{f' = E}{f'' = id}{f''' = inl})
      ∙ cong (λ z → ⟜-app ∘g ⊗-intro id z) (⊕-βl (⟜-intro inlD) (⟜-intro inrD))
      ∙ ⟜-β inlD )
      ( cong (fwd ∘g_) (⊕-βr (id ,⊗ inl) (id ,⊗ inr))
      ∙ cong (⟜-app ∘g_) (⊗-intro⊗-intro {f = id}{f' = E}{f'' = id}{f''' = inr})
      ∙ cong (λ z → ⟜-app ∘g ⊗-intro id z) (⊕-βr (⟜-intro inlD) (⟜-intro inrD))
      ∙ ⟜-β inrD )

    mapCod-E : ⟜-mapCod bwd ∘g E ≡ ⟜-intro id
    mapCod-E = ⊕≡ _ _
      ( cong (⟜-mapCod bwd ∘g_) (⊕-βl (⟜-intro inlD) (⟜-intro inrD))
      ∙ ⟜-mapCod-precomp bwd inlD
      ∙ cong ⟜-intro (⊕-βl (id ,⊗ inl) (id ,⊗ inr))
      ∙ sym (⟜-intro-precompDom id inl) )
      ( cong (⟜-mapCod bwd ∘g_) (⊕-βr (⟜-intro inlD) (⟜-intro inrD))
      ∙ ⟜-mapCod-precomp bwd inrD
      ∙ cong ⟜-intro (⊕-βr (id ,⊗ inl) (id ,⊗ inr))
      ∙ sym (⟜-intro-precompDom id inr) )

    the-ret : bwd ∘g fwd ≡ id
    the-ret =
      sym (⟜-β (bwd ∘g fwd))
      ∙ cong ⟜-intro⁻
          ( sym (⟜-mapCod-precomp bwd (⟜-intro⁻ E))
          ∙ cong (⟜-mapCod bwd ∘g_) (sym (⟜-η E))
          ∙ mapCod-E )
      ∙ ⟜-β id

  ⊗⊕-distL-cat≅ : A ⊗ (B ⊕ C) ≅ (A ⊗ B) ⊕ (A ⊗ C)
  ⊗⊕-distL-cat≅ = mkStrEq fwd bwd the-sec the-ret
