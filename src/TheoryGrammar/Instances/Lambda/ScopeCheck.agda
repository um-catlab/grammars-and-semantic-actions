{-
  The scope checker, as a map of the calculus:

      ⊤ ⊢ &ᴰ Scope (λ Δ → Scoped Δ ⊕ ¬G (Scoped Δ))

  "for every term and every scope, a scoping derivation or a refutation".
  Deciding in EVERY scope at once is forced: the scope grows while the
  term shrinks, so no single scope is an invariant of the recursion.
  Instantiate at `[]` with `&ᴰ-E` to get closedness.

  The algorithm: unfold one step (`sc-unroll`), decide the three
  summands, recombine with `dec-⊕`, fold back (`sc-roll`).  Recursive
  calls sit at `LParts o t sp a`, and `proper` is their descent proof.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.ScopeCheck where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Unit
open import Cubical.Data.List using ([]; _∷_)
open import Cubical.Data.Nat.Order using (_<_)
open import Cubical.Data.Empty as E using (⊥)
open import Cubical.Relation.Nullary.Base using (yes; no; Discrete)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.View
open import TheoryGrammar.Instances.Lambda.Signature
open import TheoryGrammar.Instances.Lambda.Base
open import TheoryGrammar.Instances.Lambda.Grading
open import TheoryGrammar.Instances.Lambda.Readable
open import TheoryGrammar.Instances.Lambda.Binder
open import TheoryGrammar.Instances.Lambda.Scoped

module ScopeCheck (Name : Type₀) (_≟_ : Discrete Name) where

  open LamBase Name
  open Grading Name
  open Readable Name
  open Binder Name
  open Wellscoped Name
  open Views λSub

  -- The ONE place `Discrete Name` is used -- and it is used to BUILD an
  -- internal map, never to case-split on one.  That is the whole rule
  -- for how external decidability may enter the calculus.
  dec-⌈⌉ : (m : Name) → ⊤G ⊢ Dec⟨ ⌈_⌉ {s = nm} m ⟩
  dec-⌈⌉ m n _ with n ≟ m
  ... | yes p = dec-yes (⌈_⌉ {s = nm} m) n (Eq.pathToEq p)
  ... | no ¬p = dec-no  (⌈_⌉ {s = nm} m) n λ e → E.rec (¬p (Eq.eqToPath e))

  -- Membership is decidable by induction on the scope, using nothing
  -- but `⊥`'s rule and the generic `dec-⊕`.
  --
  -- As a PROBE (TheoryGrammar.View): a partial view of a name, built
  -- from the partial view at each scope entry.  `probe-⊕` is `dec-⊕`
  -- under its view name -- coverage-checking a pattern and deciding a
  -- grammar are one notion, which is why no new combinator was needed.
  dec-In : (Γ : Scope) → Probe (In Γ)
  dec-In []      = dec-no (In []) ∘g ⇒-I &-E₂
  dec-In (m ∷ Γ) = probe-⊕ ⌈ m ⌉ (In Γ) (dec-⌈⌉ m) (dec-In Γ)

  DecScoped : TmG
  DecScoped = &ᴰ Scope (λ Δ → Dec⟨ Scoped Δ ⟩)

  check : ⊤G ⊢ DecScoped
  check t _ = recSize {M = DecScoped} step t
    where
    step : (t : Raw)
         → ((s : Raw) → size s < size t → DecScoped s) → DecScoped t
    step t rec Δ =
      dec-map (Step Scoped Δ) (Scoped Δ) (sc-roll Δ) (sc-unroll Δ) t dStep
      where
      Vr Ap Lm : TmG
      Vr = VarG (In Δ)
      Ap = AppG (Scoped Δ) (Scoped Δ)
      Lm = ⊕ᴰ Name (λ n → LamG ⌈ n ⌉ (Scoped (n ∷ Δ)))

      -- the recursive call, with `&ᴰ` eliminated at the scope we need
      rec' : (s : Raw) → size s < size t → (Δ' : Scope) → Dec⟨ Scoped Δ' ⟩ s
      rec' s p Δ' = &ᴰ-E Scope {B = λ Δ'' → Dec⟨ Scoped Δ'' ⟩} Δ' s (rec s p)

      dVar : Dec⟨ Vr ⟩ t
      dVar = dec-⊗ varOp (λ _ → In Δ) t λ sp a →
               dec-In Δ (LParts varOp t sp a) tt

      dApp : Dec⟨ Ap ⟩ t
      dApp = dec-⊗ appOp (λ b → if b then Scoped Δ else Scoped Δ) t λ sp →
               λ { true  → rec' _ (proper appOp t sp true)  Δ
                 ; false → rec' _ (proper appOp t sp false) Δ }

      dLam : Dec⟨ Lm ⟩ t
      dLam = dec-map (LamGᵈ (λ n → Scoped (n ∷ Δ))) Lm collapse⁻ collapse t
               (dec-lamᵈ (λ n → Scoped (n ∷ Δ)) t λ sp →
                  rec' _ (proper lamOp t sp false) (LParts lamOp t sp true ∷ Δ))

      dStep : Dec⟨ Step Scoped Δ ⟩ t
      dStep = dec-⊕ Vr (Ap ⊕ Lm) t (dVar , dec-⊕ Ap Lm t (dApp , dLam))

  closed? : ⊤G ⊢ Dec⟨ Scoped [] ⟩
  closed? = &ᴰ-E Scope [] ∘g check
