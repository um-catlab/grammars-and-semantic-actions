{- What a pass IS -- and the NEGATIVE result that shapes everything here. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Passes.Framework where

open import Cubical.Data.List using (_∷_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt)
open import Cubical.Foundations.Prelude
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Inductive
open import TheoryGrammar.Instances.Lambda.Base
open import TheoryGrammar.Instances.Lambda.Scoped
open import TheoryGrammar.Instances.Lambda.Signature

module PassKit (Name : Type₀) where

  open LamBase Name
  open Wellscoped Name

  -- the output of a pass: some term, with its scoping derivation.  The
  -- input index `t` does not occur on the right, and that constancy is
  -- what the whole file is about.
  Out : Scope → TmG
  Out Γ = ⊕ᴰ Raw (λ t _ → Scoped Γ t)

  -- `⊕ᴰ-I` at the index itself.  This is the bridge to `CarrierMap`:
  -- a term `A ⊢ pull B` along a named carrier map gives a term
  -- `A ⊢ ⊕ᴰ carrier B`, and this is that map at `h = id`.
  emit : (Γ : Scope) → Scoped Γ ⊢ Out Γ
  emit Γ t = ⊕ᴰ-I Raw {A = λ t' _ → Scoped Γ t'} t t

  -- The three rebuilding rules: `roll` after an injection, packaged.
  -- Each denotes "this node, put back exactly as it was, with the
  -- derivation reassembled".  These are the FREE part of every pass.

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

  -- The move every pass that lifts a subterm out from under a binder
  -- makes, and the reason none of them needs a strengthening lemma: if `s`
  -- is already scoped at the SMALLER Γ, emit it -- carrying the derivation
  -- the decision produced, never re-deriving it -- else fall back.
  tryEmit : (Γ : Scope) → (⊤G ⊢ Dec⟨ Scoped Γ ⟩) → (s : Raw) → Out Γ s → Out Γ s
  tryEmit Γ dec s fallback =
    ⊕-E {A = Scoped Γ} {C = Out Γ} {B = ¬G (Scoped Γ)}
        (emit Γ) (λ _ _ → fallback) s (dec s tt)

  -- the identity pass's algebra: every alternative rebuilt
  idAlg : (Γ : Scope) → Step Out Γ ⊢ Out Γ
  idAlg Γ = ⊕-E (outVar Γ) (⊕-E (outApp Γ) (outLamG Γ))

  -- Running a pass: the generic `fold`, exactly as `toDB`.

  -- DENOTES: one rewriting step at each node, given already-rewritten
  -- children.  A pass IS `idAlg` with the one alternative it rewrites
  -- replaced.
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

  -- Observing a pass: the output term, as a SEMANTIC ACTION.
  term : (Γ : Scope) → Action (Out Γ) Raw
  term Γ = tagA Raw
