{- ONE GRAMMAR, ANY CONTEXT SUBSTRATE. Uses (var n) = Lf n -- leaf,
   possibly modal Uses (app u v) = Uses u ⊗ᶜ Uses v -- the context tensor
   Uses (lam n t) = Uses t ⟜ᶜ ⌈ n ⌉ -- ITS residual DENOTATIONS. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Modes.Core where

open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Unit
open import Cubical.Foundations.Prelude
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.CanonicalFocus
open import TheoryGrammar.Decidable
open import TheoryGrammar.Decidable.Splittings
open import TheoryGrammar.Fibered
open import TheoryGrammar.Instances.Lambda.Fibered using (module Terms)
open import TheoryGrammar.Instances.Lambda.Modes.Ctx
open import TheoryGrammar.Instances.Lambda.Modes.Fold
open import TheoryGrammar.Instances.Lambda.Signature using (tm)

-- The context `Fibered` comes with a total point: `_·_` and the canonical
-- focus are the two places a MODE needs the operation itself.  Everything
-- else below -- `⊗ᶜ`, `check`, the decision layer -- sees only `CFib`.
module Core (Name : Type₀)
            (CFib : Fibered ctxSig ℓ-zero ℓ-zero)
            (CPoint : LaxPoint CFib)
            (CDec : DecSplittings CFib ℓ-zero)
            (sing : Name → CFib .carrier tt)
  where

  open Terms Name using (Raw; λFib)
  open Fold Name using (indRaw)
  open DecFib CFib public

  Ctx : Type₀
  Ctx = CFib .carrier tt

  CtxG : Type₁
  CtxG = TheoryTy ℓ-zero tt

  -- `Γ · Δ` : Γ extended on the right by Δ
  infixl 20 _·_
  _·_ : Ctx → Ctx → Ctx
  Γ · Δ = CPoint .op mul λ b → if b then Γ else Δ

  -- `(A ⊗ᶜ B) Γ` : Γ decomposes into an A-part beside a B-part
  infixr 21 _⊗ᶜ_
  _⊗ᶜ_ : CtxG → CtxG → CtxG
  A ⊗ᶜ B = ⊗ˢ mul λ b → if b then A else B

  -- The tensor's decision rule, and the ONLY place `CDec` is consulted:
  -- `dec-⊗ˢ` at `mul`, with the two slots supplied uniformly.  Both the
  -- `app` node of `check` and affine's modal leaf are this one term.
  dec-⊗ᶜ : (A B : CtxG) → ⊤G ⊢ Dec⟨ A ⟩ → ⊤G ⊢ Dec⟨ B ⟩ → ⊤G ⊢ Dec⟨ A ⊗ᶜ B ⟩
  dec-⊗ᶜ A B dA dB Γ _ =
    CDec .dec-⊗ˢ mul (λ b → if b then A else B) Γ
      λ { sp true → dA _ tt ; sp false → dB _ tt }

  -- The residual, at the LEFT slot: "extend the context on the right".

  -- `Rest` names the other slots and `tuple` reassembles: what this
  -- instance forces is that the complement of `mul`'s left slot is ONE
  -- slot, filled by `false`.
  asm : Assembly CFib mul true
  asm .Rest       = Unit
  asm .restOf _   = false
  asm .tuple Γ f b = if b then Γ else f tt

  private module Cn = Canon CFib CPoint mul true asm

  open Cn public using (⊸ᶠ; ⊸ᶠ-lam; ⊸ᶠ-app; ⊸ᶠ-β; ⊸ᶠ-η)

  -- The generic residual's hypothesis, discharged.
  repJ : (Δ : Ctx) → ∀ {ℓM}
         (M : (f : Unit → Ctx) → ((r : Unit) → f r Eq.≡ Δ) → Type ℓM)
       → M (λ _ → Δ) (λ _ → Eq.refl)
       → (f : Unit → Ctx) (q : (r : Unit) → f r Eq.≡ Δ) → M f q
  repJ Δ M m f q = singJ (λ y e → M (λ _ → y) (λ _ → e)) m (f tt) (q tt)

  private
    module Res (Δ : Ctx) =
      Cn.Residual {A = λ _ → ⌈ Δ ⌉} (λ _ → Δ) (λ _ → Eq.refl) (repJ Δ) (λ _ _ → refl)

  -- `(B ⟜ᶜ Δ) Γ` : B holds of Γ extended on the right by Δ
  infixl 2 _⟜ᶜ_
  _⟜ᶜ_ : CtxG → Ctx → CtxG
  B ⟜ᶜ Δ = ⊸ᶠ (λ _ → ⌈ Δ ⌉) B

  -- the context shifted by a fixed Δ: what the residual classifies
  shift : CtxG → Ctx → CtxG
  shift B Δ Γ = B (Γ · Δ)

  -- ⊸-ELIM and ⊸-INTRO at the representable, and their two round trips:
  -- all four are `Canon.Residual` instantiated at `repJ`.  β is `refl`
  -- there and η is one `funExt`; neither is reproved here.
  ⟜-app : (B : CtxG) (Δ : Ctx) → (B ⟜ᶜ Δ) ⊢ shift B Δ
  ⟜-app B Δ = Res.plug-at Δ {B = B}

  ⟜-lam : (B : CtxG) (Δ : Ctx) → shift B Δ ⊢ (B ⟜ᶜ Δ)
  ⟜-lam B Δ = Res.unplug Δ {B = B}

  ⟜-β : (B : CtxG) (Δ : Ctx) (Γ : Ctx) (b : shift B Δ Γ)
      → ⟜-app B Δ Γ (⟜-lam B Δ Γ b) ≡ b
  ⟜-β B Δ = Res.⊸-β Δ {B = B}

  ⟜-η : (B : CtxG) (Δ : Ctx) (Γ : Ctx) (h : (B ⟜ᶜ Δ) Γ)
      → ⟜-lam B Δ Γ (⟜-app B Δ Γ h) ≡ h
  ⟜-η B Δ = Res.⊸-η Δ {B = B}

  -- The grammar and its checker.  A mode supplies only the leaf.

  module Mode (Lf : Name → CtxG)
              (decLf : (n : Name) → ⊤G ⊢ Dec⟨ Lf n ⟩) where

    -- `Uses t Γ` : "t is well-used in Γ", at THIS `Fibered` and leaf
    Uses : Raw → CtxG
    Uses = indRaw (λ _ → CtxG)
                  Lf
                  (λ _ _ P Q → P ⊗ᶜ Q)
                  (λ n _ P → P ⟜ᶜ sing n)

    -- the same eliminator at a decision-valued motive: for every Γ,
    -- either a use-derivation or its refutation
    check : (t : Raw) → ⊤G ⊢ Dec⟨ Uses t ⟩
    check = indRaw (λ t → ⊤G ⊢ Dec⟨ Uses t ⟩) decLf cApp cLam
      where
      cApp : (u v : Raw) → (⊤G ⊢ Dec⟨ Uses u ⟩) → (⊤G ⊢ Dec⟨ Uses v ⟩)
           → ⊤G ⊢ Dec⟨ Uses u ⊗ᶜ Uses v ⟩
      cApp u v = dec-⊗ᶜ (Uses u) (Uses v)

      cLam : (n : Name) (t : Raw) → (⊤G ⊢ Dec⟨ Uses t ⟩)
           → ⊤G ⊢ Dec⟨ Uses t ⟜ᶜ sing n ⟩
      cLam n t ct Γ _ =
        dec-map (shift (Uses t) (sing n)) (Uses t ⟜ᶜ sing n)
                (⟜-lam (Uses t) (sing n)) (⟜-app (Uses t) (sing n))
                Γ (ct (Γ · sing n) tt)

    -- The same checker read in the AST calculus: ONE map ⊤ ⊢ &ᴰ Ctx (λ Γ →
    -- Dec⟨ Scoped Γ ⟩) exactly as `Lambda.ScopeCheck.check`.
    private module AST = DecFib λFib

    -- `Scoped Γ t` : the same proposition as `Uses t Γ`, at the term sort
    Scoped : Ctx → AST.TheoryTy ℓ-zero tm
    Scoped Γ t = Uses t Γ

    checkAST : AST._⊢_ AST.⊤G (AST.&ᴰ Ctx (λ Γ → AST.Dec⟨ Scoped Γ ⟩))
    checkAST t _ Γ = check t Γ tt

    -- Observing a decision. `okA` (TheoryGrammar.SemanticAction) is the
    -- generic observer -- it reads a `Result E A` at ANY error grammar,
    -- and a decision is `Result (¬G A) A`.
    accepts : (t : Raw) → ⊤G ⊢ Δ Bool
    accepts t = okA (Uses t) (¬G (Uses t)) ∘g check t

    -- the same observation of the LEAF decision, whose world is a
    -- CONTEXT rather than a term.  Same reader, different sort.
    acceptsLf : (n : Name) → ⊤G ⊢ Δ Bool
    acceptsLf n = okA (Lf n) (¬G (Lf n)) ∘g decLf n
