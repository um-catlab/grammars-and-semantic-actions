{-
  ONE GRAMMAR, ANY CONTEXT SUBSTRATE.

      Uses (var n)   =  Lf n                  -- leaf, possibly modal
      Uses (app u v) =  Uses u ⊗ᶜ Uses v      -- the context tensor
      Uses (lam n t) =  Uses t ⟜ᶜ ⌈ n ⌉       -- ITS residual

  `Uses t Γ` reads "t is well-used in Γ".  `var`/`app`/`lam` are fixed
  once and for all here; a MODE is the pair (context substrate, leaf).
  The binder is not a bump of a nonterminal index -- it is `⊸ᶠ` at the
  canonical focus, so `Γ ⊢ λn.t iff Γ·n ⊢ t` is the residual adjunction
  and not a definition.

  `check` is the same eliminator at a decision-valued motive.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Modes.Core where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Substrate
open import TheoryGrammar.CanonicalFocus
open import TheoryGrammar.Decidable
open import TheoryGrammar.Decidable.Splittings
open import TheoryGrammar.Instances.Lambda.Signature using (tm)
open import TheoryGrammar.Instances.Lambda.Substrate using (module Terms)
open import TheoryGrammar.Instances.Lambda.Modes.Ctx
open import TheoryGrammar.Instances.Lambda.Modes.Fold

module Core (Name : Type₀)
            (CSub : Substrate ctxSig ℓ-zero ℓ-zero)
            (CDec : DecSplittings CSub ℓ-zero)
            (sing : Name → CSub .carrier tt)
  where

  open Terms Name using (Raw; var; app; lam; λSub)
  open Fold Name using (indRaw)
  open DecSub CSub public

  Ctx : Type₀
  Ctx = CSub .carrier tt

  CtxG : Type₁
  CtxG = TheoryTy ℓ-zero tt

  -- the operation, and the tensor it convolves
  infixl 20 _·_
  _·_ : Ctx → Ctx → Ctx
  Γ · Δ = CSub .op mul λ b → if b then Γ else Δ

  infixr 21 _⊗ᶜ_
  _⊗ᶜ_ : CtxG → CtxG → CtxG
  A ⊗ᶜ B = ⊗ˢ mul λ b → if b then A else B

  -- ================================================================
  -- The residual, at the LEFT slot: "extend the context on the right".
  -- ================================================================

  asm : Assembly CSub mul true
  asm .Rest       = Unit
  asm .restOf _   = false
  asm .tuple Γ f b = if b then Γ else f tt

  open Canon CSub mul true asm public using (⊸ᶠ; ⊸ᶠ-lam; ⊸ᶠ-app; ⊸ᶠ-β; ⊸ᶠ-η)

  _⟜ᶜ_ : CtxG → Ctx → CtxG
  B ⟜ᶜ Δ = ⊸ᶠ (λ _ → ⌈ Δ ⌉) B

  -- the context shifted by a fixed Δ: what the residual classifies
  shift : CtxG → Ctx → CtxG
  shift B Δ Γ = B (Γ · Δ)

  -- ⊸-ELIM at the representable: `Canon.plug` with the point `Eq.refl`.
  ⟜-app : (B : CtxG) (Δ : Ctx) → (B ⟜ᶜ Δ) ⊢ shift B Δ
  ⟜-app B Δ = Canon.plug CSub mul true asm {A = λ _ → ⌈ Δ ⌉} {B = B}
                         (λ _ → Δ) (λ _ → Eq.refl)

  -- ⊸-INTRO at the representable.
  --
  -- MEASUREMENT.  This is the one step of the mode development that is
  -- not a combinator: it transports along the representable's equation.
  -- It is a SINGLE `Eq.transport` only because the complement of the
  -- focused slot is a singleton, so the rest-tuple is determined by one
  -- component; for a wider complement the same step would need function
  -- extensionality for `Eq`, which does not hold definitionally.  The
  -- generic `Canon.plug` (the elim) needs no such thing.
  ⟜-lam : (B : CtxG) (Δ : Ctx) → shift B Δ ⊢ (B ⟜ᶜ Δ)
  ⟜-lam B Δ Γ b f e = Eq.transport (λ z → B (Γ · z)) (Eq.sym (e tt)) b

  -- ================================================================
  -- The grammar and its checker.  A mode supplies only the leaf.
  -- ================================================================

  module Mode (Lf : Name → CtxG)
              (decLf : (n : Name) → ⊤G ⊢ Dec⟨ Lf n ⟩) where

    Uses : Raw → CtxG
    Uses = indRaw (λ _ → CtxG)
                  Lf
                  (λ _ _ P Q → P ⊗ᶜ Q)
                  (λ n _ P → P ⟜ᶜ sing n)

    check : (t : Raw) → ⊤G ⊢ Dec⟨ Uses t ⟩
    check = indRaw (λ t → ⊤G ⊢ Dec⟨ Uses t ⟩) decLf cApp cLam
      where
      cApp : (u v : Raw) → (⊤G ⊢ Dec⟨ Uses u ⟩) → (⊤G ⊢ Dec⟨ Uses v ⟩)
           → ⊤G ⊢ Dec⟨ Uses u ⊗ᶜ Uses v ⟩
      cApp u v cu cv Γ _ =
        CDec .dec-⊗ˢ mul (λ b → if b then Uses u else Uses v) Γ
          λ { sp true → cu _ tt ; sp false → cv _ tt }

      cLam : (n : Name) (t : Raw) → (⊤G ⊢ Dec⟨ Uses t ⟩)
           → ⊤G ⊢ Dec⟨ Uses t ⟜ᶜ sing n ⟩
      cLam n t ct Γ _ =
        dec-map (shift (Uses t) (sing n)) (Uses t ⟜ᶜ sing n)
                (⟜-lam (Uses t) (sing n)) (⟜-app (Uses t) (sing n))
                Γ (ct (Γ · sing n) tt)

    -- The same checker read in the AST calculus: ONE map
    --     ⊤ ⊢ &ᴰ Ctx (λ Γ → Dec⟨ Scoped Γ ⟩)
    -- exactly as `Lambda.ScopeCheck.check`.  `Dec⟨_⟩` is pointwise, so
    -- which of the two indices is bound is a matter of reading.
    private module AST = DecSub λSub

    Scoped : Ctx → AST.TheoryTy ℓ-zero tm
    Scoped Γ t = Uses t Γ

    checkAST : AST._⊢_ AST.⊤G (AST.&ᴰ Ctx (λ Γ → AST.Dec⟨ Scoped Γ ⟩))
    checkAST t _ Γ = check t Γ tt

    -- observing a decision: `⊕-E` into a constant grammar, never a match
    accepts : (t : Raw) → ⊤G ⊢ (λ _ → Bool)
    accepts t = ⊕-E {A = Uses t} {C = λ _ → Bool} {B = ¬G (Uses t)}
                    (λ _ _ → true) (λ _ _ → false)
                ∘g check t
