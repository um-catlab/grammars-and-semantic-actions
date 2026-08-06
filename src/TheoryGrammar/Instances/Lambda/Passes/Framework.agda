{-
  What a pass IS, in the calculus.

  A pass rewrites the term, so it moves the index.  Its output type is
  therefore the internal existential over the carrier,

      Out Γ = ⊕ᴰ Raw (λ t' → Scoped Γ t'),

  which is CONSTANT in the index -- and that is the whole difference
  from `mergesort`, where `⊗ˢ` pinned the index and correctness came
  free.  Here the index pins nothing; what is free is the recursion.

  `idAlg` rebuilds every alternative.  A pass is `idAlg` with the ONE
  alternative it rewrites replaced, so "the rest of the pass preserves
  scope" is discharged once, here.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Passes.Framework where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.List using (List; []; _∷_)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Inductive
open import TheoryGrammar.Instances.Lambda.Signature
open import TheoryGrammar.Instances.Lambda.Base
open import TheoryGrammar.Instances.Lambda.Scoped

module PassKit (Name : Type₀) where

  open LamBase Name
  open Wellscoped Name

  -- the output of a pass: some term, with its scoping derivation
  Out : Scope → TmG
  Out Γ = ⊕ᴰ Raw (λ t _ → Scoped Γ t)

  -- `⊕ᴰ-I` at the index itself.  This is the bridge to `CarrierMap`:
  -- a term `A ⊢ pull B` along a named carrier map gives a term
  -- `A ⊢ ⊕ᴰ carrier B`, and this is that map at `h = id`.
  emit : (Γ : Scope) → Scoped Γ ⊢ Out Γ
  emit Γ t = ⊕ᴰ-I Raw {A = λ t' _ → Scoped Γ t'} t t

  -- ================================================================
  -- The three rebuilding rules: `roll` after an injection, packaged.
  -- These are the FREE part of every pass.
  -- ================================================================

  outVar : (Γ : Scope) → VarG (In Γ) ⊢ Out Γ
  outVar Γ =
    var-elim λ n i → emit Γ (var n) (sc-var Γ (var n) (var-mk {P = In Γ} i))

  outApp : (Γ : Scope) → AppG (Out Γ) (Out Γ) ⊢ Out Γ
  outApp Γ = app-elim λ _ _ ou ov →
    emit Γ (app (ou .fst) (ov .fst))
      (sc-app Γ (app (ou .fst) (ov .fst)) (app-mk (ou .snd) (ov .snd)))

  outLam : (Γ : Scope) (n : Name) → Scoped (n ∷ Γ) ⊢ Out Γ
  outLam Γ n b d =
    emit Γ (lam n b) (sc-lam Γ n (lam n b) (lam-mk Eq.refl d))

  outLamG : (Γ : Scope) → ⊕ᴰ Name (λ n → LamG ⌈ n ⌉ (Out (n ∷ Γ))) ⊢ Out Γ
  outLamG Γ = ⊕ᴰ-E λ n → lam-elim λ _ _ _ o → outLam Γ n (o .fst) (o .snd)

  -- the identity pass's algebra
  idAlg : (Γ : Scope) → Step Out Γ ⊢ Out Γ
  idAlg Γ = ⊕-E (outVar Γ) (⊕-E (outApp Γ) (outLamG Γ))

  -- ================================================================
  -- Running a pass: the generic `fold`, exactly as `toDB`.
  -- ================================================================

  PassAlg : Type₀
  PassAlg = (Γ : Scope) → Step Out Γ ⊢ Out Γ

  runPass : PassAlg → (Γ : Scope) → Scoped Γ ⊢ Out Γ
  runPass alg Γ t d = fold Mot α (Γ , t) d
    where
    Mot : Ix → Type₀
    Mot (Δ , s) = Out Δ s

    α : (Δ : Scope) (s : Raw) (sh : Sh (ScopedF Δ) s)
      → ((p : Pos (ScopedF Δ) s sh) → Mot (nx (ScopedF Δ) s sh p))
      → Mot (Δ , s)
    α Δ s sh rc = alg Δ s (⟦Sc⟧ {M = Mot} Δ s (sh , rc))

  idPass : (Γ : Scope) → Scoped Γ ⊢ Out Γ
  idPass = runPass idAlg

  -- Observing a pass: the output term, as a SEMANTIC ACTION.  `Out Γ`
  -- is a `⊕ᴰ Raw`, so reading its index off is the GENERIC `tagA`
  -- (TheoryGrammar.SemanticAction) -- there is nothing pass-specific
  -- here, and no constant grammar.
  term : (Γ : Scope) → Action (Out Γ) Raw
  term Γ = tagA Raw
