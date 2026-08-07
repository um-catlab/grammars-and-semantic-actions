{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  LINEAR TERMS OVER THE CONTEXT PROMODEL.

  With `Context.agda` in place the typing rules of the linear λ-calculus
  stop being rules with side conditions and become TERMS OF THE
  CALCULUS.  Two of the three are worth reading closely.

      appT : (Tm ⊛ Tm) ⊢ Tm

  `⊛` is `⊗ˢ appop`, so its very type says the context splits.  There is
  no premise "Γ = Γ₁ ⊎ Γ₂ with Γ₁ # Γ₂" to discharge, because `⊗ˢ` IS
  that premise; and since `_⊢_` preserves the usage, no term of this type
  can invent or discard a variable.  That is the linear analogue of
  `merge : Sorted ⊗ Sorted ⊢ Sorted` being permutation-correct for free.

      lamT : (λ u → Tm (true ∷ u)) ⊢ Tm

  A binder EXTENDS the context, so it cannot be a plain `⊢` -- the index
  moves.  What it is instead is reindexing: `λ u → Tm (true ∷ u)` is
  `Tm` pulled back along `u ↦ true ∷ u`, i.e. the Cartesian lift of the
  weakening map.  So the two constructs use the two halves of the
  framework exactly once each:

      application  =  the multiplicative connective  (⊗ˢ)
      abstraction  =  reindexing along a carrier map (pull)

  which is the sense in which the calculus already contains linear λ
  rather than having to encode it.
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.LinLam.Syntax where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib

open import TheoryGrammar.Instances.LinLam.Context public

-- ==================================================================
-- "exactly one variable is live", as a recursive predicate.
-- ==================================================================

Solo : Usage → Type₀
Solo []          = ⊥
Solo (true  ∷ u) = Empty u
Solo (false ∷ u) = Solo u

-- ==================================================================
-- The terms.  `tapp` carries the splitting, so an ill-split
-- application is not a term -- linearity is structural.
-- ==================================================================

data Tm : Usage → Type₀ where
  tvar : ∀ {u} → Solo u → Tm u
  tapp : ∀ {u₁ u₂ u} → Use⊎ u₁ u₂ u → Tm u₁ → Tm u₂ → Tm u
  tlam : ∀ {u} → Tm (true ∷ u) → Tm u

TmG : Ctx
TmG = Tm

-- ==================================================================
-- THE TYPING RULES, as terms of the calculus.
-- ==================================================================

-- PRIMITIVE (phase 1): the intro rule for application.  It matches the
-- splitting because that is what an intro rule does -- compare `⊗-mk`
-- in every other instance.
appT : (TmG ⊛ TmG) ⊢ TmG
appT u ((u₁ , u₂ , s) , k) = tapp s (k true) (k false)

-- ... and its elimination, so downstream passes never match a term.
appE : {C : Ctx} → ((TmG ⊛ TmG) ⊢ C) → (u : Usage)
     → (u₁ u₂ : Usage) → Use⊎ u₁ u₂ u → Tm u₁ → Tm u₂ → C u
appE f u u₁ u₂ s t₁ t₂ =
  f u ((u₁ , u₂ , s)
      , boolΠ {M = λ a → boolΠ {M = λ _ → Ctx} TmG TmG a
                           (linFib .parts appop u (u₁ , u₂ , s) a)} t₁ t₂)

-- PRIMITIVE (phase 1): abstraction is reindexing along weakening.
lamT : (λ u → Tm (true ∷ u)) ⊢ TmG
lamT u t = tlam t

-- PRIMITIVE (phase 1): a variable is available exactly at its own usage.
varT : (λ u → Solo u) ⊢ TmG
varT u s = tvar s

-- ==================================================================
-- A closed term: the linear identity `λx. x`.  Its usage is the empty
-- one, and the body's usage is `true ∷ []` -- the binder's variable, and
-- nothing else, which is what makes it LINEAR rather than merely
-- well-scoped.
-- ==================================================================

idLin : Tm []
idLin = tlam (tvar tt)

-- application of two closed terms splits the empty context as `[] ⊎ []`
selfApp : Tm []
selfApp = tapp unil idLin idLin

-- ==================================================================
-- WHAT THE INDEX BUYS.  Any transformation of terms is a `⊢`, so it
-- preserves the usage -- an optimisation pass CANNOT silently drop or
-- duplicate a variable.  Stated once here so later phases can cite it.
-- ==================================================================

Pass : Type₀
Pass = TmG ⊢ TmG

-- the identity pass, and composition -- passes form a category, and
-- `_∘g_` is their sequencing
idPass : Pass
idPass = idg

_then_ : Pass → Pass → Pass
p then q = q ∘g p

infixl 5 _then_
