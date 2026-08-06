{-
  The same development as Grammar.SplitExperiment, at a different
  substrate: raw lambda ASTs instead of strings.

  Substrate  = the free algebra on the signature
                 var : Name → Tm ; app : Tm Tm → Tm ; lam : Name Tm → Tm
  Grammars   = families indexed by that carrier
  Connectives= one per operation, as inductive families
  Algorithm  = a scope checker, structural on the tree

  Two things this exhibits that the string case did not:
   * `lam` needs the DEPENDENT tensor -- the body's grammar depends on
     the bound name, so an external product will not do;
   * the scope grows while the term shrinks, which is why the checker
     is quantified over all scopes.
-}
module Grammar.LambdaScope where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Empty as Empty
open import Cubical.Relation.Nullary.Base

module Scope (Name : Type ℓ-zero) (_≟_ : Discrete Name) where

  -- ================================================================
  -- 1.  The substrate: the free algebra on the signature.
  -- ================================================================

  data Raw : Type ℓ-zero where
    var : Name → Raw
    app : Raw → Raw → Raw
    lam : Name → Raw → Raw

  TmG : Type₁
  TmG = Raw → Type ℓ-zero

  _⊢_ : TmG → TmG → Type ℓ-zero
  A ⊢ B = ∀ t → A t → B t

  -- ================================================================
  -- 2.  The connectives: one per operation of the signature.
  -- ================================================================

  data VarG (P : Name → Type ℓ-zero) : Raw → Type ℓ-zero where
    mk : ∀ {n} → P n → VarG P (var n)

  data AppG (A B : TmG) : Raw → Type ℓ-zero where
    mk : ∀ {u v} → A u → B v → AppG A B (app u v)

  -- the DEPENDENT tensor: F is indexed by the bound name
  data LamG (F : Name → TmG) : Raw → Type ℓ-zero where
    mk : ∀ {n t} → F n t → LamG F (lam n t)

  ⊤G : TmG
  ⊤G _ = Unit
    where open import Cubical.Data.Unit

  -- ================================================================
  -- 3.  Scopes and well-scopedness.
  -- ================================================================

  Scope : Type ℓ-zero
  Scope = List Name

  _∈_ : Name → Scope → Type ℓ-zero
  n ∈ []      = ⊥
  n ∈ (m ∷ Γ) = (n ≡ m) ⊎ (n ∈ Γ)

  _∈?_ : (n : Name) (Γ : Scope) → Dec (n ∈ Γ)
  n ∈? []      = no λ ()
  n ∈? (m ∷ Γ) with n ≟ m | n ∈? Γ
  ... | yes p | _     = yes (inl p)
  ... | no ¬p | yes i = yes (inr i)
  ... | no ¬p | no ¬i = no λ { (inl p) → ¬p p ; (inr i) → ¬i i }

  -- `Scoped` is the μ in `Scope → TmG` whose rules are exactly the
  -- three connectives above.
  data Scoped (Γ : Scope) : Raw → Type ℓ-zero where
    var : ∀ {n} → n ∈ Γ           → Scoped Γ (var n)
    app : ∀ {u v} → Scoped Γ u → Scoped Γ v → Scoped Γ (app u v)
    lam : ∀ {n t} → Scoped (n ∷ Γ) t        → Scoped Γ (lam n t)

  -- the rules, stated as morphisms of grammars
  var-rule : (Γ : Scope) → VarG (_∈ Γ) ⊢ Scoped Γ
  var-rule Γ _ (mk i) = var i

  app-rule : (Γ : Scope) → AppG (Scoped Γ) (Scoped Γ) ⊢ Scoped Γ
  app-rule Γ _ (mk a b) = app a b

  lam-rule : (Γ : Scope) → LamG (λ n → Scoped (n ∷ Γ)) ⊢ Scoped Γ
  lam-rule Γ _ (mk a) = lam a

  -- ================================================================
  -- 4.  The scope checker.  Structural on the tree; the scope grows
  --     while the term shrinks, hence the quantification over Γ.
  -- ================================================================

  scopecheck : (t : Raw) (Γ : Scope) → Dec (Scoped Γ t)
  scopecheck (var n) Γ with n ∈? Γ
  ... | yes i = yes (var i)
  ... | no ¬i = no λ { (var i) → ¬i i }
  scopecheck (app u v) Γ with scopecheck u Γ | scopecheck v Γ
  ... | no ¬a | _     = no λ { (app a b) → ¬a a }
  ... | yes a | no ¬b = no λ { (app a b) → ¬b b }
  ... | yes a | yes b = yes (app a b)
  scopecheck (lam n t) Γ with scopecheck t (n ∷ Γ)
  ... | yes a = yes (lam a)
  ... | no ¬a = no λ { (lam a) → ¬a a }

  -- the instantiation we actually want
  closed? : (t : Raw) → Dec (Scoped [] t)
  closed? t = scopecheck t []

-- ==================================================================
-- 5.  It runs.  Each `refl` below holds only if the whole pipeline
--     reduces -- which is the property the Split presentation was
--     chosen for.
-- ==================================================================

module Test where

  open import Cubical.Data.Nat
  open import Cubical.Data.Bool
  open Scope ℕ discreteℕ

  toBool : {A : Type ℓ-zero} → Dec A → Bool
  toBool (yes _) = true
  toBool (no  _) = false

  -- λx. x
  idT : Raw
  idT = lam 0 (var 0)

  -- λx. y   -- y is free
  openTerm : Raw
  openTerm = lam 0 (var 1)

  -- (λx. x) (λy. λz. y)
  bigger : Raw
  bigger = app (lam 0 (var 0)) (lam 1 (lam 2 (var 1)))

  _ : toBool (closed? idT) ≡ true
  _ = refl

  _ : toBool (closed? openTerm) ≡ false
  _ = refl

  _ : toBool (closed? bigger) ≡ true
  _ = refl

  -- shadowing: λx. λx. x  is closed, and the inner binder wins
  shadow : Raw
  shadow = lam 0 (lam 0 (var 0))

  _ : toBool (closed? shadow) ≡ true
  _ = refl
