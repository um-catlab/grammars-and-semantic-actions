{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  WHERE THE DEAD-CODE ARGUMENT BREAKS.

  This is the point of the whole instance, so it is worth stating with
  the linear proof beside it.

  ------------------------------------------------------------------
  1.  THE LINEAR THEOREM.

  `Instances/LinLam/Opt.agda` §4 proves that dead-code elimination is
  VACUOUS in the linear calculus.  It does so with a budget:

      Budget u = Σ[ oc ] Σ[ lm ] (oc ≡ live u + lm)

  -- "occurrences = owned variables + binders" -- and folds the term
  with that as the MOTIVE, so the invariant is produced as the counts
  are computed.  Then, with `b : Tm (true ∷ u)` a λ-body whose bound
  variable is dead and `c : Tm u` the term DCE would put in its place,

      occ b  =  live (true ∷ u) + lam b  =  suc (live u + lam b)
      occ c  =  live u + lam c           =  live u + lam b

  and `suc n ≡ n` is absurd.  Hence `deadBinder : DeadBinder ⊢ ⊥G`.

  ------------------------------------------------------------------
  2.  THE EQUATION SPLITS IN TWO, AND AFFINE KEEPS ONE HALF.

  An equation of naturals is two inequalities, and they say different
  things:

      occ ≤ live + lam    every owned variable is used AT MOST once
      occ ≥ live + lam    every owned variable is used AT LEAST once

  The first is no-contraction.  The second is no-weakening.  Linearity
  is both; affinity is the first alone.  Accordingly:

      budgetLe   : occ t ≤ live u + lam t        -- PROVED below
      noBudgetGe : ¬ (∀ t → live u + lam t ≤ occ t)   -- REFUTED below

  and the refutation is `Syntax.constAff`, the K combinator `λx.λy.x`:
  one occurrence, two binders, at the empty usage, so `0 + 2 ≤ 1` is
  false.  `adrop`/`tdrop` is the sole source of the failure -- restrict
  the syntax to `tvar`/`tapp`/`tlam` over `Use⊎` and the ≥ half returns,
  because that is `LinLam`.

  ------------------------------------------------------------------
  3.  ... AND THE DEAD-CODE PROOF USES EXACTLY THE HALF THAT IS LOST.

  Read the linear chain again with the two halves separated:

      suc (live u + lam b)  ≤  occ b        -- the ≥ half, AT THE BODY
                            ≡  occ c        -- the hypothesis
                            ≤  live u + lam c
                            ≡  live u + lam b

  The FIRST step is the ≥ half applied to `b`, and it is the only ≥ step
  in the argument.  `deadBinderFromGe` below is precisely that proof,
  with the missing step taken as an explicit premise -- so the linear
  theorem is recovered verbatim the moment the premise is available, and
  the break is localised to one inequality at one subterm.

  It is worth being precise about WHICH subterm: `b` is the λ-BODY, at
  usage `true ∷ u`.  The `true` is the bound variable, and the ≥ half
  says it must be used.  `tdrop` is the term former that owns it without
  using it.  So the failure is not diffuse -- it is the single bit that
  `adrop` was added to un-pin.

  ------------------------------------------------------------------
  4.  AND THE CONCLUSION IS FALSE, NOT MERELY UNPROVED.

      deadWitness : DeadBinder []
      noDeadEmpty : ¬ (DeadBinder ⊢ ⊥G)

  with `b = tdrop tt (λx.x) : ATm (true ∷ [])` and `c = λx.x : ATm []`
  -- profiles `(occ 1 , lam 1)` on both sides, so the hypothesis holds
  by `refl`.  Reading it back: `λ_. λx. x` has a dead binder, and DCE
  really does replace it by `λx. x`.

  Consequently the DCE branch of a pass is no longer `⊥-E`, and there is
  a genuine choice to make: `dceNotUnique` exhibits two distinct maps
  `DeadBinder ⊢ ATmG`.  `Opt.dceUnique` proves the opposite linearly.
  That is the sharpest single statement of what affinity costs -- the
  optimiser acquires content, and with it the obligation to be correct,
  which the index does not supply (see `Opt`'s "BOUGHT NOTHING").

  ------------------------------------------------------------------
  WHAT SURVIVES IS NOT NOTHING.  `budgetLe` is a real theorem with the
  same shape as the linear one, and it still forbids duplication: no
  affine term has more occurrences than it has owned variables plus
  binders.  Half of `Opt`'s "no variable is dropped or duplicated" is
  intact, and it is the half `Base.affDiag` states structurally.
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Affine.Dead where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Bool.Properties using (false≢true)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib

open import TheoryGrammar.Instances.Affine.Syntax public

-- ==================================================================
-- §1  THE BUDGET, as an INEQUALITY.
--
-- The motive of the fold IS the statement being proved -- the
-- Quicksort idiom, and `Opt.agda`'s -- so the algebra produces the
-- invariant as it computes the counts.  The only change from the
-- linear version is `≡` becoming `≤`, and it is forced in exactly one
-- branch (`budgetApp`, via `liveSplit≤`) plus the new one
-- (`budgetWk`).
-- ==================================================================

Budget : Ctx
Budget u = Σ[ oc ∈ ℕ ] Σ[ lm ∈ ℕ ] (oc ≤ live u + lm)

-- PRIMITIVE (phase 1): a `Solo` usage owns exactly one variable
soloLive : (u : Usage) → Solo u → live u ≡ 1
soloLive (true  ∷ u) e = cong suc (liveEmpty u e)
soloLive (false ∷ u) e = soloLive u e

private
  shuffle : (a b c d : ℕ) → (a + b) + (c + d) ≡ (a + c) + (b + d)
  shuffle a b c d =
      sym (+-assoc a b (c + d))
    ∙ cong (a +_) (+-assoc b c d)
    ∙ cong (λ z → a + (z + d)) (+-comm b c)
    ∙ cong (a +_) (sym (+-assoc c b d))
    ∙ +-assoc a c (b + d)

-- one variable, no binder.  Unchanged from `Opt.budgetVar` except that
-- the equation is weakened to `≤-reflexive`.
budgetVar : SoloG ⊢ Budget
budgetVar u s = 1 , 0 , ≤-reflexive (sym (+-zero (live u) ∙ soloLive u s))

-- occurrences add, binders add -- and the usages add only up to `≤`,
-- because `Base.liveSplit≤` is an inequality.  THIS is the first place
-- the linear equation is lost.
budgetApp : (Budget ⊛ Budget) ⊢ Budget
budgetApp = ⊛-E' Budget Budget
  λ u u₁ u₂ s (o₁ , l₁ , e₁) (o₂ , l₂ , e₂) →
    (o₁ + o₂) , (l₁ + l₂) ,
      ≤-trans (≤-+-≤ e₁ e₂)
              (subst (_≤ live u + (l₁ + l₂))
                     (sym (shuffle (live u₁) l₁ (live u₂) l₂))
                     (≤-+k (liveSplit≤ s)))

-- a binder trades one owned variable for one binder: still `+-suc`
budgetLam : Own Budget ⊢ Budget
budgetLam u (o , l , e) = o , suc l , subst (o ≤_) (sym (+-suc (live u) l)) e

-- ... and the NEW branch: weakening only enlarges the right-hand side,
-- so the inequality is preserved and the equation could not have been.
budgetWk : WkG Budget ⊢ Budget
budgetWk v (u , p , (o , l , e)) = o , l , ≤-trans e (≤-+k (⊑-live p))

budgetAlg : StepG Budget ⊢ Budget
budgetAlg = ⊕-E budgetVar (⊕-E budgetApp (⊕-E budgetLam budgetWk))

-- THE INTRINSIC INVARIANT, as a term of the calculus.
budget : ATmG ⊢ Budget
budget = foldATm Budget budgetAlg

occOf : ∀ {u} → ATm u → ℕ
occOf {u} t = budget u t .fst

lamOf : ∀ {u} → ATm u → ℕ
lamOf {u} t = budget u t .snd .fst

-- THEOREM (the half that survives).  No affine term uses more than it
-- owns.  This is `Base.affDiag` counted.
budgetLe : (u : Usage) (t : ATm u) → occOf t ≤ live u + lamOf t
budgetLe u t = budget u t .snd .snd

-- ==================================================================
-- §2  THE HALF THAT DOES NOT SURVIVE.
-- ==================================================================

-- the counts of the K combinator, by `refl` -- one occurrence, two
-- binders, nothing owned
_ : occOf constAff ≡ 1
_ = refl

_ : lamOf constAff ≡ 2
_ = refl

-- THEOREM.  THE `≥` HALF OF THE LINEAR BUDGET IS FALSE.
--
-- `λx. λy. x` owns nothing, binds twice, and mentions a variable once.
-- Linearly `occ ≡ live + lam` would demand `1 ≡ 2`.
noBudgetGe : ((u : Usage) (t : ATm u) → live u + lamOf t ≤ occOf t) → ⊥
noBudgetGe ge = ¬m<m (ge [] constAff)

-- ==================================================================
-- §3  THE LINEAR PROOF, WITH ITS MISSING STEP MADE EXPLICIT.
--
-- Everything `Opt.deadBinder` does, except the ONE inequality that
-- affinity refutes -- which is taken as a premise.  So the theorem is
-- not lost through some diffuse weakening of the framework: it is one
-- application of `≥` at the λ-body, and `noBudgetGe` says that
-- application is unavailable.
-- ==================================================================

DeadBinder : Ctx
DeadBinder u =
  Σ[ b ∈ Own ATmG u ] Σ[ c ∈ ATmG u ]
    ((occOf b ≡ occOf c) × (lamOf b ≡ lamOf c))

deadBinderFromGe :
    ((u : Usage) (t : ATm u) → live u + lamOf t ≤ occOf t)
  → DeadBinder ⊢ ⊥G
deadBinderFromGe ge u (b , c , eo , el) = E.rec (¬m<m chain)
  where
  -- `live (true ∷ u) + lam b` is `suc (live u + lam b)` definitionally
  chain : suc (live u + lamOf b) ≤ live u + lamOf b
  chain =
    ≤-trans (ge (true ∷ u) b)
      (≤-trans (≤-reflexive eo)
        (≤-trans (budgetLe u c)
                 (≤-reflexive (cong (live u +_) (sym el)))))

-- ==================================================================
-- §4  ... AND THE CONCLUSION IS REFUTED OUTRIGHT.
--
-- `λ_. λx. x`: the body owns the bound variable and drops it, and the
-- term DCE would substitute has the same occurrence profile -- by
-- `refl`, not by an argument.
-- ==================================================================

deadWitness : DeadBinder []
deadWitness = deadBody , idAff , refl , refl

-- THEOREM.  The dead-binder grammar is INHABITED, so `Opt.deadBinder`
-- has no affine counterpart.
noDeadEmpty : (DeadBinder ⊢ ⊥G) → ⊥
noDeadEmpty f = E.rec* (f [] deadWitness)

-- COROLLARY.  A dead-code eliminator's rewriting branch is a real
-- choice, not `⊥-E`.  `Opt.dceUnique` proves any two agree linearly;
-- here they do not.
stripDead : DeadBinder ⊢ ATmG
stripDead u (b , c , _) = c

stripDeadOwned : DeadBinder ⊢ ATmG
stripDeadOwned u (b , c , _) = tdrop (⊑-refl u) c

private
  isDrop : ∀ {u} → ATm u → Bool
  isDrop (tdrop _ _) = true
  isDrop (tvar _)    = false
  isDrop (tapp _ _ _) = false
  isDrop (tlam _)    = false

dceNotUnique : ((f g : DeadBinder ⊢ ATmG) → f ≡ g) → ⊥
dceNotUnique h =
  false≢true (cong (λ k → isDrop (k [] deadWitness)) (h stripDead stripDeadOwned))

-- ==================================================================
-- §5  IT COMPUTES.
-- ==================================================================

_ : occOf deadBody ≡ 1
_ = refl

_ : occOf idAff ≡ 1
_ = refl

_ : lamOf deadBody ≡ 1
_ = refl

_ : lamOf idAff ≡ 1
_ = refl

-- the dropped argument really is dropped: `(λ_. λx.x) (λx.x)` has TWO
-- occurrences and three binders, and owns nothing
_ : occOf deadApp ≡ 2
_ = refl

_ : lamOf deadApp ≡ 3
_ = refl
