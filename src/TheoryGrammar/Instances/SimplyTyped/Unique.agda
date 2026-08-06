{-
  THE SUBSINGLETON THEOREM.

      synUnique : (Infer Γ A & Infer Γ B) ⊢ Kty A B

  "two synthesis derivations of the same term give equal types", stated
  with the calculus' own equality of types (`Kty A B = ⌈ B ⌉ A`) and
  proved with the calculus' own rules.  It says exactly that

      Syn Γ = ⊕ᴰ Ty (λ A → Infer Γ A)

  is a SUBSINGLETON in its index: the sum has at most one summand
  inhabited.  That is the same shape of fact `Split-isProp` states for
  the promodel -- at most one splitting -- and it plays the same role:
  it is what turns a positive answer somewhere else into a REFUTATION
  here.  See `Check.agda`, where `dec-at` takes it as a hypothesis.

  The proof is the generic `fold`, with the motive

      UM (syn , Γ , A , t) = (B : Ty) → Infer Γ B t → TyEq A B
      UM (chk , Γ , C , t) = ⊤

  so the induction hypothesis arrives already at the right index, and
  only the `app` rule uses it.  The nine cases are eliminated by
  `dist&₂` and `⊕-E`; six are refuted because two derivations of the
  same term cannot use different head operations, and `ann/ann` needs no
  induction at all -- the type is read straight off the `ty` slot.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.SimplyTyped.Unique where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Relation.Nullary.Base using (Discrete)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Inductive
open import TheoryGrammar.Instances.SimplyTyped.Signature
open import TheoryGrammar.Instances.SimplyTyped.Fibered
open import TheoryGrammar.Instances.SimplyTyped.Base
open import TheoryGrammar.Instances.SimplyTyped.Readable
open import TheoryGrammar.Instances.SimplyTyped.Types
open import TheoryGrammar.Instances.SimplyTyped.Context
open import TheoryGrammar.Instances.SimplyTyped.Judgments

module StUnique (Name : Type₀) (_≟_ : Discrete Name) where

  open StBase Name
  open StReadable Name
  open StTypes Name
  open StContext Name _≟_
  open Judgments Name _≟_

  -- the erased checking slot: the motive says nothing at `chk`
  KU : TmG
  KU _ = Unit

  -- the induction hypothesis at a synthesised type
  IHG : Ctx → Ty → TmG
  IHG Γ X t = (B : Ty) → Infer Γ B t → TyEq X B

  UM : Ix → Type₀
  UM ((syn , Γ , A) , t) = IHG Γ A t
  UM ((chk , Γ , C) , t) = Unit

  -- ================================================================
  -- The three matching cases.
  -- ================================================================

  varvar : (Γ : Ctx) (A B : Ty)
         → (VarG (Lookup Γ A) & VarG (Lookup Γ B)) ⊢ Kty A B
  varvar Γ A B =
    merge2 varOp (varFam (Lookup Γ A)) (varFam (Lookup Γ B)) (Kty A B)
           (λ m sp h → lookupUnique Γ A B (TParts varOp m sp tt) (h tt))

  -- no induction: both annotations ARE the index, by the representable
  annann : (X Y : TmG) (A B : Ty)
         → (AnnG X (⌈_⌉ {s = ty} A) & AnnG Y (⌈_⌉ {s = ty} B)) ⊢ Kty A B
  annann X Y A B =
    merge2 annOp (annFam X (⌈_⌉ {s = ty} A)) (annFam Y (⌈_⌉ {s = ty} B))
           (Kty A B)
           (λ m sp h → tyEq-trans A (TParts annOp m sp false) B
                         (tyEq-sym (TParts annOp m sp false) A (h false .fst))
                         (h false .snd))

  -- the one use of the induction hypothesis, and the one use of
  -- injectivity of the arrow
  appapp : (Γ : Ctx) (A B A₀ B₀ : Ty)
         → (AppG (IHG Γ (A₀ ⇒ᵗ A)) KU & AppG (Infer Γ (B₀ ⇒ᵗ B)) (Check Γ B₀))
         ⊢ Kty A B
  appapp Γ A B A₀ B₀ =
    merge2 appOp (appFam (IHG Γ (A₀ ⇒ᵗ A)) KU)
                 (appFam (Infer Γ (B₀ ⇒ᵗ B)) (Check Γ B₀)) (Kty A B)
           (λ m sp h →
              Eq.pathToEq (⇒ᵗ-inj A₀ A B₀ B
                            (h true .fst (B₀ ⇒ᵗ B) (h true .snd)) .snd))

  -- ================================================================
  -- The six impossible cases, and the dispatch.
  -- ================================================================

  module _ (Γ : Ctx) (A B : Ty) where

    private
      QP₁ : Ty → TmG
      QP₁ A₀ = AppG (IHG Γ (A₀ ⇒ᵗ A)) KU

      QP₂ : Ty → TmG
      QP₂ B₀ = AppG (Infer Γ (B₀ ⇒ᵗ B)) (Check Γ B₀)

      V₁ : TmG
      V₁ = VarG (Lookup Γ A)
      P₁ : TmG
      P₁ = ⊕ᴰ Ty QP₁
      N₁ : TmG
      N₁ = AnnG KU (⌈_⌉ {s = ty} A)
      V₂ : TmG
      V₂ = VarG (Lookup Γ B)
      P₂ : TmG
      P₂ = ⊕ᴰ Ty QP₂
      N₂ : TmG
      N₂ = AnnG (Check Γ B) (⌈_⌉ {s = ty} B)

      vp : (V₁ & P₂) ⊢ Kty A B
      vp = ⊥-E ∘g (⊕ᴰ-E (λ _ → varApp-⊥) ∘g ⊕ᴰ-&-in Ty {A = V₁} {P = QP₂})

      vn : (V₁ & N₂) ⊢ Kty A B
      vn = ⊥-E ∘g varAnn-⊥

      pv : (P₁ & V₂) ⊢ Kty A B
      pv = ⊥-E ∘g (⊕ᴰ-E (λ _ → varApp-⊥)
                   ∘g (⊕ᴰ-&-in Ty {A = V₂} {P = QP₁} ∘g &-swap))

      nv : (N₁ & V₂) ⊢ Kty A B
      nv = ⊥-E ∘g (varAnn-⊥ ∘g &-swap)

      pn : (P₁ & N₂) ⊢ Kty A B
      pn = ⊥-E ∘g (⊕ᴰ-E (λ _ → appAnn-⊥ ∘g &-swap)
                   ∘g (⊕ᴰ-&-in Ty {A = N₂} {P = QP₁} ∘g &-swap))

      np : (N₁ & P₂) ⊢ Kty A B
      np = ⊥-E ∘g (⊕ᴰ-E (λ _ → appAnn-⊥ ∘g &-swap)
                   ∘g ⊕ᴰ-&-in Ty {A = N₁} {P = QP₂})

      pp : (P₁ & P₂) ⊢ Kty A B
      pp = ⊕ᴰ-E (λ A₀ → ⊕ᴰ-E (λ B₀ → appapp Γ A B A₀ B₀)
                        ∘g (⊕ᴰ-&-in Ty {A = QP₁ A₀} {P = QP₂} ∘g &-swap))
           ∘g (⊕ᴰ-&-in Ty {A = P₂} {P = QP₁} ∘g &-swap)

      nn : (N₁ & N₂) ⊢ Kty A B
      nn = annann KU (Check Γ B) A B

    -- the whole nine-way case analysis, by two four-way distributions
    uStep : (JStep (λ y s → UM (y , s)) (syn , Γ , A) & JStep Jμ (syn , Γ , B))
          ⊢ Kty A B
    uStep = ⊕-E (⊕-E (varvar Γ A B) (⊕-E vp vn ∘g dist&r))
                (⊕-E (⊕-E pv nv ∘g dist&)
                     (⊕-E (⊕-E pp pn) (⊕-E np nn) ∘g dist&₂))
            ∘g dist&₂

  -- ================================================================
  -- The theorem, by the generic fold.
  -- ================================================================

  uAlg : (x : NT) (t : Raw) → JStep (λ y s → UM (y , s)) x t → UM (x , t)
  uAlg (syn , Γ , A) t v B d = uStep Γ A B t (v , j-unroll (syn , Γ , B) t d)
  uAlg (chk , Γ , C) t v = tt

  synUnique : (Γ : Ctx) (A B : Ty) → (Infer Γ A & Infer Γ B) ⊢ Kty A B
  synUnique Γ A B t (d₁ , d₂) =
    fold UM (λ x m sh rc → uAlg x m (⟦J⟧ x m (sh , rc)))
         ((syn , Γ , A) , t) d₁ B d₂
