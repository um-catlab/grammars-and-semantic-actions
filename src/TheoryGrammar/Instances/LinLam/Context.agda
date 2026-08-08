{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- PHASE 2's THEORY: LINEAR CONTEXTS AS A PARTIAL COMMUTATIVE MONOID. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.LinLam.Context where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false; if_then_else_)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.List using (List; []; _∷_; length)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Theories.Monoid public
open import TheoryGrammar.Theories.MonoidSep
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib
open import TheoryGrammar.Graded

-- Usages.  Position n says whether variable n is still available.
-- The length is the scope size, so a usage is a scope together with a
-- choice of which of its variables this subterm is responsible for.

Usage : Type₀
Usage = List Bool

-- the empty usage of a given scope size
none : ℕ → Usage
none zero    = []
none (suc n) = false ∷ none n

-- exactly variable `i` of a scope of size `n`
only : ℕ → ℕ → Usage
only zero    (suc n) = true  ∷ none n
only (suc i) (suc n) = false ∷ only i n
only _       zero    = []

-- DISJOINT SPLITTING.  Note there is NO constructor taking `true` on
-- both sides: that absence IS linearity, and it is structural -- no
-- equation, no proof component, nothing to unfold.

data Use⊎ : Usage → Usage → Usage → Type₀ where
  unil : Use⊎ [] [] []
  uleft  : ∀ {u v w} → Use⊎ u v w → Use⊎ (true  ∷ u) (false ∷ v) (true  ∷ w)
  uright : ∀ {u v w} → Use⊎ u v w → Use⊎ (false ∷ u) (true  ∷ v) (true  ∷ w)
  uskip  : ∀ {u v w} → Use⊎ u v w → Use⊎ (false ∷ u) (false ∷ v) (false ∷ w)

-- "nothing is available", as a RECURSIVE predicate -- the same choice
-- `IsNil` makes for strings, so every split happens on the usage itself.
Empty : Usage → Type₀
Empty []          = Unit
Empty (true  ∷ _) = ⊥
Empty (false ∷ u) = Empty u

UseSplit : (o : MonOp) → Usage → Type₀
UseSplit nilop u = Empty u
UseSplit appop u = Σ[ u₁ ∈ Usage ] Σ[ u₂ ∈ Usage ] Use⊎ u₁ u₂ u

-- the dependent eliminator for the `Bool` arity, as in `Heap/Base`: ONE
-- place where `true`/`false` are matched, so no extended lambda is ever
-- written and nominal mismatch cannot arise.

UseParts : (o : MonOp) (u : Usage) → UseSplit o u → MonAr o → Usage
UseParts nilop u sp ()
UseParts appop u (u₁ , u₂ , _) = boolΠ u₁ u₂

-- THE `Fibered`.  As with heaps there is no `op`: joining two usages is
-- PARTIAL, undefined exactly when they both claim a variable.

linFib : Fibered monoidSig ℓ-zero ℓ-zero
linFib .carrier _ = Usage
linFib .Split     = UseSplit
linFib .parts     = UseParts

open RulesF linFib public

Ctx : Type₁
Ctx = TheoryTy ℓ-zero tt

-- LINEAR APPLICATION is the tensor, and the empty context is its unit.
private module S = MonSep linFib

_⊛_ : Ctx → Ctx → Ctx
_⊛_ = S._∗_

infixr 20 _⊛_

nothingLeft : Ctx
nothingLeft = S.empS

-- LINEARITY IS REAL: no usage that owns a variable splits as itself twice.

-- PRIMITIVE (phase 1)
noDupUse : (u : Usage) → Use⊎ (true ∷ u) (true ∷ u) (true ∷ u) → ⊥
noDupUse u ()

-- THE GRADING. `deg` counts AVAILABLE variables; a split slot never has
-- more, and has strictly fewer as soon as its sibling has any.

live : Usage → ℕ
live []          = 0
live (true  ∷ u) = suc (live u)
live (false ∷ u) = live u

-- PRIMITIVE (phase 1): usage is additive across a split.  The missing
-- (true,true) clause is what makes this true.
liveSplit : ∀ {u v w} → Use⊎ u v w → live u + live v ≡ live w
liveSplit unil        = refl
liveSplit (uleft s)   = cong suc (liveSplit s)
liveSplit (uright s)  = +-suc _ _ ∙ cong suc (liveSplit s)
liveSplit (uskip s)   = liveSplit s

private
  weak : (a b : ℕ) → a ≤ a + b
  weak a b = b , +-comm b a

  strict : (a b : ℕ) → 0 < b → a < a + b
  strict a zero    p = E.rec (¬-<-zero p)
  strict a (suc b) _ = subst (suc a ≤_) (sym (+-suc a b)) (suc-≤-suc (weak a b))

linGrading : Grading linFib
linGrading .deg _ = live

linGrading .Proper nilop u sp ()
linGrading .Proper appop u (u₁ , u₂ , _) b = 0 < live (boolΠ {M = λ _ → Usage} u₂ u₁ b)

linGrading .deg≤ nilop u sp ()
linGrading .deg≤ appop u (u₁ , u₂ , s) =
  boolΠ {M = λ a → live (boolΠ {M = λ _ → Usage} u₁ u₂ a) ≤ live u}
        (subst (live u₁ ≤_) (liveSplit s) (weak (live u₁) (live u₂)))
        (subst (live u₂ ≤_) (+-comm (live u₂) (live u₁) ∙ liveSplit s)
               (weak (live u₂) (live u₁)))

linGrading .deg< nilop u sp ()
linGrading .deg< appop u (u₁ , u₂ , s) =
  boolΠ {M = λ a → 0 < live (boolΠ {M = λ _ → Usage} u₂ u₁ a)
                 → live (boolΠ {M = λ _ → Usage} u₁ u₂ a) < live u}
        (λ pr → subst (live u₁ <_) (liveSplit s) (strict (live u₁) (live u₂) pr))
        (λ pr → subst (live u₂ <_) (+-comm (live u₂) (live u₁) ∙ liveSplit s)
                      (strict (live u₂) (live u₁) pr))

linGraded : GradedFib monoidSig ℓ-zero ℓ-zero
linGraded = graded linFib linGrading
