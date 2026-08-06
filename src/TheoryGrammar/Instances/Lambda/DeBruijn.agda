{-
  Elaboration to de Bruijn, as the generic `fold`.

  Motive `(Γ , t) ↦ DB (length Γ)`.  There is no `Maybe`:
  scope-correctness sits in the INDEX, so elaboration is total.  The
  algebra is `⟦Sc⟧` followed by the elimination rules, one per
  alternative; no clause looks at a term or at a shape.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.DeBruijn where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.List using ([]; _∷_; length)
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Bool using (Bool; true; false; if_then_else_)
open import Cubical.Data.FinData.Base using (Fin) renaming (zero to fzero; suc to fsuc)

open import TheoryGrammar.Base
open import TheoryGrammar.Instances.Lambda.Signature
open import TheoryGrammar.Instances.Lambda.Base
open import TheoryGrammar.Instances.Lambda.Scoped

module DeBruijn (Name : Type₀) where

  open LamBase Name
  open Wellscoped Name

  data DB : ℕ → Type₀ where
    dvar : ∀ {k} → Fin k → DB k
    dapp : ∀ {k} → DB k → DB k → DB k
    dlam : ∀ {k} → DB (suc k) → DB k

  -- Elaboration is a SEMANTIC ACTION -- `Action A X = A ⊢ Δ X`, from
  -- TheoryGrammar.SemanticAction -- not a map into a hand-written
  -- constant grammar `λ _ → X`.  That is what lets it be composed with
  -- a parser or a checker by the GENERIC `runResult`, with no `Maybe`
  -- spelled out at the use site and no mention of `Raw` there at all.
  --
  -- Reading a de Bruijn index off a scope membership.  The hit branch
  -- DISCARDS the representable rather than eliminating it with `⌈⌉-E`:
  -- `⌈⌉-E` matches `Eq.refl`, and a witness built from `Discrete Name`
  -- via `pathToEq` does not reduce to `Eq.refl` in cubical.  The index
  -- is fixed by the POSITION in the scope, not by the proof, so nothing
  -- is lost -- and this is the difference between the tests computing
  -- and not.
  toIxA : (Γ : Scope) → Action (In Γ) (Fin (length Γ))
  toIxA []      = ⊥A
  toIxA (m ∷ Γ) = caseA (pureA (Fin (length (m ∷ Γ))) fzero)
                        (mapA fsuc (toIxA Γ))

  Mot : Ix → Type₀
  Mot i = Δ (DB (length (i .fst))) (i .snd)

  -- One action per alternative.  Every branch is a composite of the
  -- generic `Δ`-combinators (`Δ-map`, `Δ-pair`, `Δ-at`) with this
  -- instance's own tensor eliminators; no constant grammar, no `Maybe`,
  -- and nothing built by hand.  `Δ-at` is what crosses from a slot's
  -- world to the whole's -- the move a residual would otherwise need,
  -- and available here only because `Δ` is discrete.
  module _ (Γ : Scope) where
    private k = length Γ

    dbStepA : Step (λ Δ' x → Mot (Δ' , x)) Γ ⊢ Δ (DB k)
    dbStepA =
      ⊕-E (var-elim λ n i → Δ-map dvar (var n) (toIxA Γ n i))
     (⊕-E (app-elim λ u v a b →
             Δ-map (λ p → dapp (p .fst) (p .snd)) (app u v)
                   (Δ-pair (app u v) (Δ-at u (app u v) a , Δ-at v (app u v) b)))
          (⊕ᴰ-E λ _ → lam-elim λ n t _ d →
                        Δ-map dlam (lam n t) (Δ-at t (lam n t) d)))

  toDB : (Γ : Scope) → Action (Scoped Γ) (DB (length Γ))
  toDB Γ t d = fold Mot alg (Γ , t) d
    where
    alg : (Γ' : Scope) (t' : Raw) (sh : Sh (ScopedF Γ') t')
        → ((p : Pos (ScopedF Γ') t' sh) → Mot (nx (ScopedF Γ') t' sh p))
        → Mot (Γ' , t')
    alg Γ' t' sh rc = dbStepA Γ' t' (⟦Sc⟧ {M = Mot} Γ' t' (sh , rc))
