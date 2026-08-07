{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  CALL-BY-VALUE EVALUATION OF CLOSED LINEAR TERMS, AND THE INTERFACE
  A TERM-DIRECTED BACKEND ACTUALLY NEEDS.

  `Normalise.agda` gives a NORMALISER: leftmost-outermost, reducing
  under binders, landing in the β-normal forms.  That is the right
  object for "what does this term mean" and the wrong one for "what
  does the emitted code do", because no machine reduces under a
  binder.  A backend needs a big-step relation in ITS evaluation
  order, on CLOSED terms, whose values are exactly what the target
  represents.  This file supplies it, and it is deliberately a
  separate artifact rather than a corollary of `nf`.

  ------------------------------------------------------------------
  1.  THE STRATEGY IS PART OF THE INTERFACE
  ------------------------------------------------------------------

      ⇓lam :  λx.b ⇓ λx.b
      ⇓app :  f ⇓ λx.b  →  a ⇓ v  →  b[v/x] ⇓ w  →  f a ⇓ w

  CALL BY VALUE, in the order CALLEE, then ARGUMENT, then BODY.  That
  order is not a detail: a call-by-name source semantics does not
  square with a target that evaluates arguments before the call, so
  the strategy must be pinned in the interface and not left implicit.
  It is pinned here.

  A closed linear term has no reduction that this misses, in the
  following sense: §3 proves the relation is TOTAL by well-founded
  recursion on `size`, using nothing but `Size.agda`'s (★).  So the
  choice of strategy costs no partiality -- which is again the linear
  calculus being unusually well behaved, and again for the reason that
  β cannot duplicate.

  ------------------------------------------------------------------
  2.  VALUES ARE LAMBDAS, AS A THEOREM
  ------------------------------------------------------------------

  A backend wants to assume its values are closures.  Here that is not
  an assumption:

      closedVal : (t : Tm []) → Nf t → Σ[ b ] (t ≡ tlam b)

  Every closed β-normal linear term IS a λ.  The proof is three lines
  and both of the non-λ cases are killed by the INDEX: `Solo [] = ⊥`,
  so there is no closed variable, and an application's function part
  is closed and normal, so by induction it is a λ and the application
  was a redex after all.  In an untyped calculus this is false (`x y`
  is a closed-context normal form only because `x` is free), and it is
  the index that rules the counterexample out.

  ------------------------------------------------------------------
  3.  THE COMMUTATION POINT
  ------------------------------------------------------------------

  Substitution at closed terms is

      _[_] : Tm (true ∷ []) → Tm [] → Tm []
      b [ v ] = subSize mhere unil b v

  -- `Opt.subT`'s recursion, at the only splitting `Use⊎ [] [] []` has.
  A term-directed backend's blocking lemma is that ITS substitution
  commutes with compilation,

      compile (b [ v ])  ≡  substE (compile v) (compile b),

  and everything this side of that equation is here: `_[_]` is a plain
  binary operation on closed terms with no side conditions to
  discharge (the splitting is `unil`, uniquely), and its size law

      subst-size : suc ∣ b [ v ] ∣ ≡ ∣ b ∣ + ∣ v ∣

  is (★), which is what makes any induction over the commutation
  terminate on the source side.

  ------------------------------------------------------------------
  4.  THE SQUARE, FOR A CONSUMER
  ------------------------------------------------------------------

      StrongCBV B = ∀ t v → t ⇓ v → exec B t ≡ obs B v

  This is `Simulation.Backend`'s strong square transposed into
  big-step form, and it is the shape a backend proving
  `compile t ⇓ᵗ compile v` wants: with a deterministic target
  semantics the two are interderivable, since the target's value is
  then forced to be the compilation of the source value.

  `Simulation.agda`'s verdict transfers unchanged: `noBlindCBV` below
  shows a usage-directed compiler cannot satisfy `StrongCBV` together
  with adequacy either.  The witnesses have to change, because
  `Simulation`'s `w₁`/`w₂` are open and this square is about closed
  terms.  The closed pair is

      idLin  = λx. x
      twoLam = λx. λy. y x

  -- two distinct closed VALUES (both are λs, so both are their own
  CBV results, and neither reduces to the other) at the SAME usage,
  namely the empty one.  Every backend in `Compile/` emits the empty
  program for both.
-}
open import Cubical.Foundations.Prelude

module Compile.Semantics.CBV where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false; true≢false)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
  using (_<_; _≤_; ≤-refl; ≤-trans; ≤-reflexive; ≤-sucℕ; ≤-+k; ≤-k+;
         <-weaken; suc-≤-suc)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Empty as E using (⊥)
open import Cubical.Induction.WellFounded using (Acc; acc)
open import Cubical.Relation.Nullary using (¬_)

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib

open import Compile.Semantics.Simulation public

-- ==================================================================
-- §1  CLOSED SUBSTITUTION, AND ITS SIZE LAW.
--
-- At usage `[]` the only splitting is `unil`, so substitution loses
-- its side condition entirely and becomes a binary operation.  This is
-- the operation a backend's commutation lemma is about.
-- ==================================================================

_[_] : Tm (true ∷ []) → Tm [] → Tm []
b [ v ] = subSize mhere unil b v

infixl 8 _[_]

-- (★) at closed terms.  One occurrence in, one copy out.
subst-size : (b : Tm (true ∷ [])) (v : Tm []) → suc ∣ b [ v ] ∣ ≡ ∣ b ∣ + ∣ v ∣
subst-size b v = substSize mhere unil b v

-- ==================================================================
-- §2  VALUES ARE LAMBDAS -- AS A THEOREM ABOUT THE INDEX.
-- ==================================================================

Value : Tm [] → Type₀
Value (tvar _)     = ⊥
Value (tapp _ _ _) = ⊥
Value (tlam _)     = Unit

-- a closed normal form cannot be a non-λ.  `Solo [] = ⊥` kills the
-- variable case; the application case is killed by its own function
-- part, which is closed and normal, hence a λ, hence the application
-- was a redex.
closedNotLam : (t : Tm []) → Nf t → NotLam t → ⊥
closedNotLam (tvar so)        n              nl = so
closedNotLam (tapp unil f a) (nlf , nf , na) nl = closedNotLam f nf nlf
closedNotLam (tlam b)         n              nl = nl

-- THEOREM.  Every closed β-normal linear term is a λ.  A backend may
-- therefore represent values as closures and nothing else.
closedVal : (t : Tm []) → Nf t → Σ[ b ∈ Tm (true ∷ []) ] (t ≡ tlam b)
closedVal (tvar so)       n               = E.rec so
closedVal (tapp unil f a) (nlf , nf , na) = E.rec (closedNotLam f nf nlf)
closedVal (tlam b)        n               = b , refl

-- ... hence `Value` is `Nf` at usage `[]`, in the direction a backend
-- consumes it
nfIsValue : (t : Tm []) → Nf t → Value t
nfIsValue (tvar so)       n               = so
nfIsValue (tapp unil f a) (nlf , nf , na) = closedNotLam f nf nlf
nfIsValue (tlam b)        n               = tt

-- ==================================================================
-- §3  BIG-STEP CALL-BY-VALUE.
--
-- Callee, then argument, then body.  The strategy is in the
-- constructor and nowhere else.
-- ==================================================================

data _⇓_ : Tm [] → Tm [] → Type₀ where
  ⇓lam : ∀ {b} → tlam b ⇓ tlam b
  ⇓app : ∀ {f a b v w}
       → f ⇓ tlam b                      -- (1) the callee
       → a ⇓ v                           -- (2) the argument
       → (b [ v ]) ⇓ w                   -- (3) the body, at the value
       → tapp unil f a ⇓ w

-- results are values, by construction
⇓Value : ∀ {t v} → t ⇓ v → Value v
⇓Value ⇓lam           = tt
⇓Value (⇓app _ _ dw)  = ⇓Value dw

-- ------------------------------------------------------------------
-- EVALUATION DOES NOT GROW A TERM.  This is (★) again: the contractum
-- of a redex is three nodes shorter than the redex, and the two
-- premises are evaluated to things no larger than themselves.  In an
-- untyped calculus the corresponding statement is false.
-- ------------------------------------------------------------------
⇓Size : ∀ {t v} → t ⇓ v → ∣ v ∣ ≤ ∣ t ∣
⇓Size ⇓lam = ≤-refl
⇓Size {tapp unil f a} (⇓app {b = b} {v = v} {w = w} df da dw) =
  ≤-trans (⇓Size dw)
    (≤-trans (≤-trans ≤-sucℕ (≤-reflexive (subst-size b v)))
      (≤-trans (≤-trans (≤-+k (<-weaken (⇓Size df))) (≤-k+ (⇓Size da)))
               ≤-sucℕ))

-- ==================================================================
-- §4  EVALUATION IS TOTAL.
--
-- Well-founded recursion on `size`, exactly as in `Normalise.agda` and
-- with the same accessibility (`wfℕ`, transport-free so that closed
-- terms evaluate by `refl`).  The three descents are:
--
--     the callee    ∣f∣            < 1 + ∣f∣ + ∣a∣    -- structural
--     the argument  ∣a∣            < 1 + ∣f∣ + ∣a∣    -- structural
--     the body      ∣b[v]∣         < 1 + ∣f∣ + ∣a∣    -- (★) + ⇓Size
--
-- and only the third is interesting: `b` is smaller than `f` because
-- `f` evaluated to `λx.b`, `v` is no larger than `a`, and (★) says the
-- substitution costs a further `-1`.  Every inequality in it is an
-- equation elsewhere.
-- ==================================================================

private
  -- ∣f∣ < ∣ tapp unil f a ∣
  fLt : (m n : ℕ) → m < suc (m + n)
  fLt m n = suc-≤-suc (n , +-comm n m)

  -- ∣a∣ < ∣ tapp unil f a ∣
  aLt : (m n : ℕ) → n < suc (m + n)
  aLt m n = suc-≤-suc (m , refl)

evalAcc : (t : Tm []) → Acc _<_ ∣ t ∣ → Σ[ v ∈ Tm [] ] (t ⇓ v)
evalAcc (tvar so)       _       = E.rec so
evalAcc (tlam b)        _       = tlam b , ⇓lam
evalAcc (tapp unil f a) (acc r) with evalAcc f (r ∣ f ∣ (fLt ∣ f ∣ ∣ a ∣))
... | (tvar so , df)       = E.rec (⇓Value df)
... | (tapp s' g y , df)   = E.rec (⇓Value df)
... | (tlam b , df) with evalAcc a (r ∣ a ∣ (aLt ∣ f ∣ ∣ a ∣))
...   | (v , da) =
        let (w , dw) = evalAcc (b [ v ])
                         (r ∣ b [ v ] ∣
                            (≤-trans (≤-reflexive (subst-size b v))
                              (≤-trans (≤-trans (≤-+k (<-weaken (⇓Size df)))
                                                (≤-k+ (⇓Size da)))
                                       ≤-sucℕ)))
        in w , ⇓app df da dw

-- THE HEADLINE.  Call-by-value evaluation of a closed linear term
-- terminates, and the measure is `size`.
eval : (t : Tm []) → Σ[ v ∈ Tm [] ] (t ⇓ v)
eval t = evalAcc t (wfℕ ∣ t ∣)

evalV : Tm [] → Tm []
evalV t = eval t .fst

evalD : (t : Tm []) → t ⇓ evalV t
evalD t = eval t .snd

evalValue : (t : Tm []) → Value (evalV t)
evalValue t = ⇓Value (evalD t)

-- ==================================================================
-- §5  THE SQUARE, IN BIG-STEP FORM.
--
-- `StrongCBV B` is `Simulation.Backend.Strong` transposed: instead of
-- naming the value as `nf t`, it quantifies over an evaluation
-- derivation.  A backend that proves `compile t ⇓ᵗ compile v` on the
-- target and has a DETERMINISTIC target semantics gets this, and
-- conversely.
-- ==================================================================

StrongCBV : ∀ {ℓ} → Backend ℓ → Type ℓ
StrongCBV B = (t v : Tm []) → t ⇓ v → Backend.exec B t ≡ Backend.obs B v

-- adequacy, restricted to closed values -- which by §2 is all values
SeparatingV : ∀ {ℓ} → Backend ℓ → Type ℓ
SeparatingV B = (t t' : Tm []) → Value t → Value t'
              → Backend.obs B t ≡ Backend.obs B t' → t ≡ t'

-- ------------------------------------------------------------------
-- TWO CLOSED VALUES A USAGE-DIRECTED BACKEND CANNOT TELL APART.
--
-- `Simulation.agda`'s witnesses are open, so they need replacing at
-- usage `[]`.  Both of these are λs (hence values, hence their own
-- CBV results), both are closed, and they are distinct:
--
--     idLin    = λx. x
--     twoLam   = λx. λy. y x        (the "apply-flipped" combinator)
--
-- They have the same usage -- the empty one -- so every existing
-- backend emits the SAME program for them: the empty program.
-- ------------------------------------------------------------------

twoLam : Tm []
twoLam = tlam (tlam (tapp (uright (uleft unil)) (tvar tt) (tvar tt)))

idLin⇓ : idLin ⇓ idLin
idLin⇓ = ⇓lam

twoLam⇓ : twoLam ⇓ twoLam
twoLam⇓ = ⇓lam

private
  -- `λx.x`'s body is a variable, `twoLam`'s is a λ
  bodyTag : Tm [] → Bool
  bodyTag (tvar _)     = false
  bodyTag (tapp _ _ _) = false
  bodyTag (tlam (tvar _))     = false
  bodyTag (tlam (tapp _ _ _)) = false
  bodyTag (tlam (tlam _))     = true

idLin≢twoLam : ¬ (idLin ≡ twoLam)
idLin≢twoLam p = true≢false (cong bodyTag (sym p))

-- THE VERDICT, in big-step form.  A backend whose compiler reads only
-- the usage cannot be both correct for call-by-value and adequate.
-- Every backend in `Compile/` has such a compiler.
noBlindCBV : ∀ {ℓ} (B : Backend ℓ)
           → Backend.BlindCompiler B → StrongCBV B → SeparatingV B → ⊥
noBlindCBV B blind st sep = idLin≢twoLam (sep idLin twoLam tt tt same)
  where
  open Backend B
  same : obs idLin ≡ obs twoLam
  same = sym (st idLin idLin idLin⇓)
       ∙ cong run (blind idLin twoLam)
       ∙ st twoLam twoLam twoLam⇓

-- ==================================================================
-- §6  IT COMPUTES.
-- ==================================================================

_ : evalV idLin ≡ idLin
_ = refl

_ : evalV selfApp ≡ idLin
_ = refl

_ : evalV bigApp ≡ idLin
_ = refl

_ : evalV applyK ≡ idLin
_ = refl

-- CBV and the normaliser AGREE on these, but they are different
-- functions: `nf` reduces under binders and `evalV` does not.  The
-- separating example is `twoLam`'s cousin with a redex in the body:
-- `λx. (λy.y) x` is already a value for `⇓`, and `λx.x` for `nf`.
betaUnderLam : Tm []
betaUnderLam = betaEtaRedex

_ : evalV betaUnderLam ≡ betaUnderLam
_ = refl

_ : nf betaUnderLam ≡ idLin
_ = refl
