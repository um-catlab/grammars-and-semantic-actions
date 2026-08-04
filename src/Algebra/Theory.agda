{-
  Algebraic theories and their free models on a set of constants.

  Copied (and trimmed) from cubical-categorical-logic's `alg-theory`
  branch — `Cubical.Algebra.Theory` and `Cubical.Algebra.Theory.Free` —
  so that the examples in `Examples.*` stand alone.  See the `algtheory`
  worktree for the general development: the universal property, the
  category of models, displayed models, sorted theories, ...

  `FreeModel σeq V` is the term algebra of σ with a generator for each
  constant in V, quotiented by the theory's equations.  It is a HIT: the
  equations are *paths*, so terms that a theory identifies are
  propositionally equal in the free model.
-}
module Algebra.Theory where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Unit using (Unit ; tt)

private
  variable
    ℓ ℓ' ℓ'' ℓv ℓX : Level

record AlgTheorySig (ℓ ℓ' : Level) : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  field
    ops : Type ℓ
    arities : ops → Type ℓ'

open AlgTheorySig public

-- Raw terms over a signature.  (Named `tvar`/`tnode` so the free model's
-- own constructors can keep the shorter names.)
data Tm (σ : AlgTheorySig ℓ ℓ') (V : Type ℓv)
  : Type (ℓ-max (ℓ-max ℓ ℓ') ℓv) where
  tvar : V → Tm σ V
  tnode : (op : σ .ops) → (σ .arities op → Tm σ V) → Tm σ V

TmRec : {σ : AlgTheorySig ℓ ℓ'} {X : Type ℓX}
  (α : (op : σ .ops) → (σ .arities op → X) → X)
  {V : Type ℓv} (ρ : V → X) → Tm σ V → X
TmRec α ρ (tvar v) = ρ v
TmRec α ρ (tnode op ts) = α op (λ a → TmRec α ρ (ts a))

record AlgTheoryEqns {ℓ ℓ'} (σ : AlgTheorySig ℓ ℓ') (ℓ'' ℓv : Level)
  : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max (ℓ-suc ℓ'') (ℓ-suc ℓv))) where
  field
    eqns : Type ℓ''
    vars : eqns → Type ℓv
    lhs rhs : (e : eqns) → Tm σ (vars e)

module _ {σ : AlgTheorySig ℓ ℓ'} (σeq : AlgTheoryEqns σ ℓ'' ℓv) where
  private module E = AlgTheoryEqns σeq

  data FreeModel (V : Type ℓv)
    : Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-max ℓ'' ℓv)) where
    var : V → FreeModel V
    node : (op : σ .ops) → (σ .arities op → FreeModel V) → FreeModel V
    eqn : (e : E.eqns) (ρ : E.vars e → FreeModel V)
      → TmRec node ρ (E.lhs e) ≡ TmRec node ρ (E.rhs e)
    trunc : isSet (FreeModel V)

-- A note on arities, used by every example below.  `TmRec` always
-- produces `node op (λ a → …)`, whereas the readable way to build a term
-- is an infix `s ⊕ t` = `node op (λ { true → s ; false → t })`.  For
-- `Unit` arities (unary operations) these agree definitionally, since
-- records have η; for `Bool` arities (binary operations) they do not, so
-- a one-line `bridge` is needed before an equation of the theory can be
-- applied.  Cf. `compBridge` in Cubical.Algebra.Instances.FreeCategory.
