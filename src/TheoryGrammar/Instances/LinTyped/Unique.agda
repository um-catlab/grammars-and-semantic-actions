{- THE SUBSINGLETON THEOREM, linearly. synUnique : (Infer Γ A & Infer Γ B)
   ⊢ Kty A B Two synthesis derivations of one term give equal types --
   stated with the calculus' own equality of types (`Kty A B = ⌈ B ⌉ A`). -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.LinTyped.Unique where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit; tt)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Inductive
open import TheoryGrammar.Instances.LinTyped.Signature
open import TheoryGrammar.Instances.LinTyped.Fibered
open import TheoryGrammar.Instances.LinTyped.Base
open import TheoryGrammar.Instances.LinTyped.Readable
open import TheoryGrammar.Instances.LinTyped.Types
open import TheoryGrammar.Instances.LinTyped.Context
open import TheoryGrammar.Instances.LinTyped.Judgments

-- `KU` denotes the erased checking slot: the motive says nothing at
-- `chk`, so a `chk` subderivation contributes no information.
KU : TmG
KU _ = Unit

-- `IHG Γ X` denotes the induction hypothesis at a synthesised type:
-- "any other synthesis of this term, in any context blanked from a
-- common ambient, gives `X` back".
IHG : Ctx → Ty → TmG
IHG Γ X t = (Γ₀ Γ' : Ctx) → Blank Γ Γ₀ → Blank Γ' Γ₀
          → (B : Ty) → Infer Γ' B t → TyEq X B

UM : Ix → Type₀
UM ((syn , Γ , A) , t) = IHG Γ A t
UM ((chk , Γ , C) , t) = Unit

-- The three matching cases.

-- two `var` derivations: the types agree because both contexts are
-- owned outright by the same index and are blanked from one ambient.
-- No induction -- this is `Context.soloTy` under one tensor.
varvar : (Γ Γ' Γ₀ : Ctx) (A B : Ty) → Blank Γ Γ₀ → Blank Γ' Γ₀
       → (VarG (Solo Γ A) & VarG (Solo Γ' B)) ⊢ Kty A B
varvar Γ Γ' Γ₀ A B p p' =
  merge2 varOp (varFam (Solo Γ A)) (varFam (Solo Γ' B)) (Kty A B)
         (λ m sp h →
            soloTy Γ Γ' Γ₀ A B (TParts varOp m sp tt) p p'
                   (h tt .fst) (h tt .snd))

-- no induction: both annotations ARE the index, by the representable
annann : (X Y : TmG) (A B : Ty)
       → (AnnG X (⌈_⌉ {s = ty} A) & AnnG Y (⌈_⌉ {s = ty} B)) ⊢ Kty A B
annann X Y A B =
  merge2 annOp (annFam X (⌈_⌉ {s = ty} A)) (annFam Y (⌈_⌉ {s = ty} B))
         (Kty A B)
         (λ m sp h → tyEq-trans A (TParts annOp m sp false) B
                       (tyEq-sym (TParts annOp m sp false) A (h false .fst))
                       (h false .snd))

-- the one use of the induction hypothesis, and the one use of injectivity
-- of the lollipop.
appapp : (Γ₀ Γ₁ Γ₁' : Ctx) (Y : TmG) (A B A₀ B₀ : Ty)
       → Blank Γ₁ Γ₀ → Blank Γ₁' Γ₀
       → (AppG (IHG Γ₁ (A₀ ⊸ᵗ A)) KU & AppG (Infer Γ₁' (B₀ ⊸ᵗ B)) Y)
       ⊢ Kty A B
appapp Γ₀ Γ₁ Γ₁' Y A B A₀ B₀ p p' =
  merge2 appOp (appFam (IHG Γ₁ (A₀ ⊸ᵗ A)) KU)
               (appFam (Infer Γ₁' (B₀ ⊸ᵗ B)) Y) (Kty A B)
         (λ m sp h →
            Eq.pathToEq (⊸-injʳ A₀ A B₀ B
              (h true .fst Γ₀ Γ₁' p p' (B₀ ⊸ᵗ B) (h true .snd))))

-- The six impossible cases, and the dispatch.

⊕ᴰ-⊥ʳ : (Y : Type₀) (X : TmG) (P : Y → TmG) (K : TmG)
      → ((y : Y) → (X & P y) ⊢ ⊥G) → (X & ⊕ᴰ Y P) ⊢ K
⊕ᴰ-⊥ʳ Y X P K h = ⊥-E ∘g (⊕ᴰ-E h ∘g ⊕ᴰ-&-in Y {A = X} {P = P})

⊕ᴰ-⊥ˡ : (Y : Type₀) (X : TmG) (P : Y → TmG) (K : TmG)
      → ((y : Y) → (X & P y) ⊢ ⊥G) → (⊕ᴰ Y P & X) ⊢ K
⊕ᴰ-⊥ˡ Y X P K h = ⊕ᴰ-⊥ʳ Y X P K h ∘g &-swap

module _ (Γ Γ' Γ₀ : Ctx) (A B : Ty) (pΓ : Blank Γ Γ₀) (pΓ' : Blank Γ' Γ₀) where

  private
    -- the application alternative of the FIRST derivation, at a fixed
    -- splitting and argument type ...
    QP₁ : (z : SplitΣ Γ) → Ty → TmG
    QP₁ z A₀ = AppG (IHG (z .fst) (A₀ ⊸ᵗ A)) KU

    R₁ : SplitΣ Γ → TmG
    R₁ z = ⊕ᴰ Ty (QP₁ z)

    -- ... and of the SECOND
    QP₂ : (z : SplitΣ Γ') → Ty → TmG
    QP₂ z B₀ = AppG (Infer (z .fst) (B₀ ⊸ᵗ B)) (Check (z .snd .fst) B₀)

    R₂ : SplitΣ Γ' → TmG
    R₂ z = ⊕ᴰ Ty (QP₂ z)

    V₁ : TmG
    V₁ = VarG (Solo Γ A)
    P₁ : TmG
    P₁ = ⊕ᴰ (SplitΣ Γ) R₁
    N₁ : TmG
    N₁ = AnnG KU (⌈_⌉ {s = ty} A)
    V₂ : TmG
    V₂ = VarG (Solo Γ' B)
    P₂ : TmG
    P₂ = ⊕ᴰ (SplitΣ Γ') R₂
    N₂ : TmG
    N₂ = AnnG (Check Γ' B) (⌈_⌉ {s = ty} B)

    -- the six impossible pairings
    vp : (V₁ & P₂) ⊢ Kty A B
    vp = ⊕ᴰ-⊥ʳ (SplitΣ Γ') V₁ R₂ (Kty A B)
           (λ z → ⊕ᴰ-⊥ʳ Ty V₁ (QP₂ z) ⊥G (λ _ → varApp-⊥))

    vn : (V₁ & N₂) ⊢ Kty A B
    vn = ⊥-E ∘g varAnn-⊥

    pv : (P₁ & V₂) ⊢ Kty A B
    pv = ⊕ᴰ-⊥ˡ (SplitΣ Γ) V₂ R₁ (Kty A B)
           (λ z → ⊕ᴰ-⊥ʳ Ty V₂ (QP₁ z) ⊥G (λ _ → varApp-⊥))

    nv : (N₁ & V₂) ⊢ Kty A B
    nv = ⊥-E ∘g (varAnn-⊥ ∘g &-swap)

    pn : (P₁ & N₂) ⊢ Kty A B
    pn = ⊕ᴰ-⊥ˡ (SplitΣ Γ) N₂ R₁ (Kty A B)
           (λ z → ⊕ᴰ-⊥ʳ Ty N₂ (QP₁ z) ⊥G (λ _ → appAnn-⊥ ∘g &-swap))

    np : (N₁ & P₂) ⊢ Kty A B
    np = ⊕ᴰ-⊥ʳ (SplitΣ Γ') N₁ R₂ (Kty A B)
           (λ z → ⊕ᴰ-⊥ʳ Ty N₁ (QP₂ z) ⊥G (λ _ → appAnn-⊥ ∘g &-swap))

    -- ... and the matching one, four `⊕ᴰ`s deep
    pp : (P₁ & P₂) ⊢ Kty A B
    pp =
      ⊕ᴰ-E (λ z₁ →
        ⊕ᴰ-E (λ A₀ →
          ⊕ᴰ-E (λ z₂ →
            ⊕ᴰ-E (λ B₀ →
              appapp Γ₀ (z₁ .fst) (z₂ .fst) (Check (z₂ .snd .fst) B₀)
                     A B A₀ B₀
                     (Blank-trans (z₁ .fst) Γ Γ₀ (splitBlankL (z₁ .snd .snd)) pΓ)
                     (Blank-trans (z₂ .fst) Γ' Γ₀ (splitBlankL (z₂ .snd .snd)) pΓ'))
            ∘g ⊕ᴰ-&-in Ty {A = QP₁ z₁ A₀} {P = QP₂ z₂})
          ∘g (⊕ᴰ-&-in (SplitΣ Γ') {A = QP₁ z₁ A₀} {P = R₂} ∘g &-swap))
        ∘g ⊕ᴰ-&-in Ty {A = P₂} {P = QP₁ z₁})
      ∘g (⊕ᴰ-&-in (SplitΣ Γ) {A = P₂} {P = R₁} ∘g &-swap)

    nn : (N₁ & N₂) ⊢ Kty A B
    nn = annann KU (Check Γ' B) A B

  -- ONE step of the theorem: the whole nine-way case analysis, by two
  -- four-way distributions of `&` over `⊕`
  uStep : (JStep (λ y s → UM (y , s)) (syn , Γ , A) & JStep Jμ (syn , Γ' , B))
        ⊢ Kty A B
  uStep = ⊕-E (⊕-E (varvar Γ Γ' Γ₀ A B pΓ pΓ') (⊕-E vp vn ∘g dist&r))
              (⊕-E (⊕-E pv nv ∘g dist&)
                   (⊕-E (⊕-E pp pn) (⊕-E np nn) ∘g dist&₂))
          ∘g dist&₂

-- The theorem, by the generic fold.

uAlg : (x : NT) (t : Raw) → JStep (λ y s → UM (y , s)) x t → UM (x , t)
uAlg (syn , Γ , A) t v Γ₀ Γ' p p' B d =
  uStep Γ Γ' Γ₀ A B p p' t (v , j-unroll (syn , Γ' , B) t d)
uAlg (chk , Γ , C) t v = tt

-- `synUnique Γ A B` denotes: two synthesis derivations of one term in one
-- context give EQUAL types, in the calculus' own equality of types.
synUnique : (Γ : Ctx) (A B : Ty) → (Infer Γ A & Infer Γ B) ⊢ Kty A B
synUnique Γ A B t (d₁ , d₂) =
  fold UM (λ x m sh rc → uAlg x m (⟦J⟧ x m (sh , rc)))
       ((syn , Γ , A) , t) d₁ Γ Γ (Blank-refl Γ) (Blank-refl Γ) B d₂
