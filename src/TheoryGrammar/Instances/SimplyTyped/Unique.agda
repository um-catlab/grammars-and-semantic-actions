{- THE SUBSINGLETON THEOREM. synUnique : (Infer Γ A & Infer Γ B) ⊢ Kty A B
   Two synthesis derivations of one term give equal types -- stated with
   the calculus' own equality of types (`Kty A B = ⌈ B ⌉ A`), proved with
   the calculus' own rules. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.SimplyTyped.Unique where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Unit using (Unit; tt)
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

  -- `KU` denotes the erased checking slot: the motive says nothing at
  -- `chk`, so a `chk` subderivation contributes no information.
  KU : TmG
  KU _ = Unit

  -- `IHG Γ X` denotes the induction hypothesis at a synthesised type:
  -- "any other synthesis of this term in `Γ` gives `X` back".
  IHG : Ctx → Ty → TmG
  IHG Γ X t = (B : Ty) → Infer Γ B t → TyEq X B

  -- `UM` denotes the fold's motive: the hypothesis above at `syn`,
  -- nothing at `chk`.  Stating it this way is what makes the induction
  -- hypothesis arrive already at the right index.
  UM : Ix → Type₀
  UM ((syn , Γ , A) , t) = IHG Γ A t
  UM ((chk , Γ , C) , t) = Unit

  -- The three matching cases.

  -- two `var` derivations: the types agree because the LOOKUP is
  -- unique.  No induction -- this is `lookupUnique` under one tensor.
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
              Eq.pathToEq (⇒ᵗ-injʳ A₀ A B₀ B
                            (h true .fst (B₀ ⇒ᵗ B) (h true .snd))))

  -- The six impossible cases, and the dispatch.

  -- a refutation survives a GUESSED index on the right ...
  ⊕ᴰ-⊥ʳ : (X : TmG) (P : Ty → TmG) (K : TmG)
        → ((A₀ : Ty) → (X & P A₀) ⊢ ⊥G) → (X & ⊕ᴰ Ty P) ⊢ K
  ⊕ᴰ-⊥ʳ X P K h = ⊥-E ∘g (⊕ᴰ-E h ∘g ⊕ᴰ-&-in Ty {A = X} {P = P})

  -- ... and on the left
  ⊕ᴰ-⊥ˡ : (X : TmG) (P : Ty → TmG) (K : TmG)
        → ((A₀ : Ty) → (X & P A₀) ⊢ ⊥G) → (⊕ᴰ Ty P & X) ⊢ K
  ⊕ᴰ-⊥ˡ X P K h = ⊕ᴰ-⊥ʳ X P K h ∘g &-swap

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

      -- the six impossible pairings: `varApp-⊥`, `varAnn-⊥` and
      -- `appAnn-⊥`, each with and without a guessed index and each in
      -- both variances.  Nothing here is new about the representation.
      vp : (V₁ & P₂) ⊢ Kty A B
      vp = ⊕ᴰ-⊥ʳ V₁ QP₂ (Kty A B) (λ _ → varApp-⊥)

      vn : (V₁ & N₂) ⊢ Kty A B
      vn = ⊥-E ∘g varAnn-⊥

      pv : (P₁ & V₂) ⊢ Kty A B
      pv = ⊕ᴰ-⊥ˡ V₂ QP₁ (Kty A B) (λ _ → varApp-⊥)

      nv : (N₁ & V₂) ⊢ Kty A B
      nv = ⊥-E ∘g (varAnn-⊥ ∘g &-swap)

      pn : (P₁ & N₂) ⊢ Kty A B
      pn = ⊕ᴰ-⊥ˡ N₂ QP₁ (Kty A B) (λ _ → appAnn-⊥ ∘g &-swap)

      np : (N₁ & P₂) ⊢ Kty A B
      np = ⊕ᴰ-⊥ʳ N₁ QP₂ (Kty A B) (λ _ → appAnn-⊥ ∘g &-swap)

      pp : (P₁ & P₂) ⊢ Kty A B
      pp = ⊕ᴰ-E (λ A₀ → ⊕ᴰ-E (λ B₀ → appapp Γ A B A₀ B₀)
                        ∘g (⊕ᴰ-&-in Ty {A = QP₁ A₀} {P = QP₂} ∘g &-swap))
           ∘g (⊕ᴰ-&-in Ty {A = P₂} {P = QP₁} ∘g &-swap)

      nn : (N₁ & N₂) ⊢ Kty A B
      nn = annann KU (Check Γ B) A B

    -- ONE step of the theorem: the whole nine-way case analysis, by two
    -- four-way distributions of `&` over `⊕`
    uStep : (JStep (λ y s → UM (y , s)) (syn , Γ , A) & JStep Jμ (syn , Γ , B))
          ⊢ Kty A B
    uStep = ⊕-E (⊕-E (varvar Γ A B) (⊕-E vp vn ∘g dist&r))
                (⊕-E (⊕-E pv nv ∘g dist&)
                     (⊕-E (⊕-E pp pn) (⊕-E np nn) ∘g dist&₂))
            ∘g dist&₂

  -- The theorem, by the generic fold.

  -- the algebra: at `syn`, unroll the SECOND derivation and dispatch;
  -- at `chk` there is nothing to say
  uAlg : (x : NT) (t : Raw) → JStep (λ y s → UM (y , s)) x t → UM (x , t)
  uAlg (syn , Γ , A) t v B d = uStep Γ A B t (v , j-unroll (syn , Γ , B) t d)
  uAlg (chk , Γ , C) t v = tt

  -- `synUnique Γ A B` denotes: two synthesis derivations of one term in
  -- one context give EQUAL types, in the calculus' own equality of types.
  synUnique : (Γ : Ctx) (A B : Ty) → (Infer Γ A & Infer Γ B) ⊢ Kty A B
  synUnique Γ A B t (d₁ , d₂) =
    fold UM (λ x m sh rc → uAlg x m (⟦J⟧ x m (sh , rc)))
         ((syn , Γ , A) , t) d₁ B d₂
