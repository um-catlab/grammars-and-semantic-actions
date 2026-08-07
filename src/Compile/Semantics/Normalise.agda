{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE SOURCE SEMANTICS: A TERMINATING NORMALISER FOR THE LINEAR
  λ-CALCULUS, AND THE MEASURE THAT MAKES IT ONE.

  `Size.agda` proves the arithmetic:

      suc (size (b[a/x]))  ≡  size b + size a                   (★)
      size ((λx.b) a)      ≡  size (b[a/x]) + 3                 (β↓)

  (★) is an EQUATION because the calculus is linear (`markT-both`: the
  substituted variable is live in exactly one half of any splitting), and
  (β↓) is the consequence that matters: β strictly decreases `size`, by
  exactly three, always.  This file is what (β↓) buys.

  ------------------------------------------------------------------
  1.  THE SHAPE OF THE RECURSION
  ------------------------------------------------------------------

  A normaliser is a fixed point of "contract a redex", and there are
  three ways to get one:

    * `foldTm`.  Structural, and NOT enough -- `Opt.betaPass` is a
      single bottom-up sweep, and contracting a redex can expose a new
      one at an ANCESTOR, which the sweep has already passed.  This is
      exactly the gap `Opt.agda` names.

    * `hyloC`/`löb`.  Needs the framework's grading to descend, and
      `linGrading .deg = live` ASCENDS under a binder.  Unavailable, as
      `Opt.agda` says.

    * well-founded recursion on a measure of our own.  `size` is one,
      by (β↓).  This is the route taken.

  The recursion is packaged in the standard two pieces:

      stepTm : (t : Tm u) → Nf t ⊎ Reduct t

  -- either `t` is β-normal, WITH THE PROOF, or there is a strictly
  smaller term to continue with -- and then `Acc _<_ ∣ t ∣`-guarded
  iteration.  `stepTm` is total: the sum is a decision, not a search,
  because the leftmost-outermost redex is found by one pass over the
  spine.  Nothing here is an approximation and there is no fuel.

  ------------------------------------------------------------------
  2.  WHY THE ACCESSIBILITY IS BUILT BY HAND
  ------------------------------------------------------------------

  `Cubical.Data.Nat.Order.<-wellfounded` goes through `acc-suc`, whose
  body is

      case <-split y<sn of { … ; (inr y≡n) → subst _ (sym y≡n) a }

  -- a `subst` at `Acc _<_` over a path in ℕ.  That is precisely the
  documented trap ("a derivation that introduces `subst` is the wrong
  derivation"): the boundary case `size t' + 1 = size t` is the COMMON
  one here, so every β step would go through a transport at an indexed
  data type, and the `refl` tests in §5 would stop reducing.

  `accℕ` below is the same theorem with the transport removed: bound
  the argument by a fuel and recurse structurally on the fuel.  It never
  forces an `_≤_` proof -- the proofs only ever appear under the `acc`
  constructor's function field -- so the whole normaliser evaluates by
  δ/ι alone, and §5's tests are `refl`.  This is a presentation choice,
  not a weakening: `wfℕ : ∀ n → Acc _<_ n` is the honest statement, and
  `normalise` is `Acc`-guarded recursion against it.

  ------------------------------------------------------------------
  3.  NORMALITY IS IN THE MOTIVE
  ------------------------------------------------------------------

      normalise : (t : Tm u) → Σ[ t' ∈ Tm u ] Nf t'

  so "the output is normal" is not a theorem proved afterwards about a
  function `Tm u → Tm u`; it is the codomain, produced by `stepTm`'s
  `inl` branch, which is the only way the recursion can stop.  This is
  the same discipline `Size.subS` uses for (★) and `Opt.Budget` uses for
  the dead-code theorem.  `Nf` itself is a RECURSIVE PREDICATE (Unit/⊥
  valued) rather than an inductive family, for the reason `Context.Empty`
  and `Codegen.Below` are: it never blocks a `refl`.

  Internally the statement is

      normaliseG : TmG ⊢ NfG,        NfG u = Σ[ t ∈ Tm u ] Nf t

  -- a `⊢`-map, so normalisation preserves the usage on the nose.  That
  is worth pausing on: it says the normal form of a term uses EXACTLY
  the free variables the term used, which for an untyped λ-calculus is
  false (β can erase) and here is definitional.

  ------------------------------------------------------------------
  4.  WHAT IS AND IS NOT NORMALISED
  ------------------------------------------------------------------

  `Nf` is β-normality: no `tapp` whose function part is a `tlam`.
  η is NOT contracted, and that is a deliberate scope decision, not an
  obstruction -- `etaSize` below records that η is size-decreasing too
  (by three, again), so the very same recursion accommodates it and the
  only cost is the extra branches in `stepTm`.  What the calculus's η
  needs on top of that is `Opt.freshSplit` and `Opt.soloUnit`, both
  already primitives there.

  A pleasant accident: on `Opt.agda`'s own η examples, β alone suffices.
  `betaEtaRedex = λx. (λy.y) x` has a function part that IS a `tlam`, so
  it is a β-redex, and `etaRedex = λx. ((λy.y)(λy.y)) x` becomes one
  after its inner redex fires.  Both normalise to `idLin`, and §5 checks
  it by `refl`.
-}
open import Cubical.Foundations.Prelude

module Compile.Semantics.Normalise where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
  using (_<_; _≤_; ≤-refl; ≤-trans; suc-≤-suc; pred-≤-pred; <-+k; <-k+;
         ¬-<-zero)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Empty as E using (⊥)
open import Cubical.Induction.WellFounded using (Acc; acc)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib

open import Compile.Semantics.Size public

-- ==================================================================
-- §1  NORMAL FORMS.
--
-- Recursive predicates, Unit/⊥-valued, in the style of
-- `Context.Empty`/`Syntax.Solo`.  A normal form is a term with no
-- β-redex anywhere; `NotLam` is the one local condition.
-- ==================================================================

NotLam : ∀ {u} → Tm u → Type₀
NotLam (tvar _)     = Unit
NotLam (tapp _ _ _) = Unit
NotLam (tlam _)     = ⊥

Nf : ∀ {u} → Tm u → Type₀
Nf (tvar _)     = Unit
Nf (tapp _ f a) = NotLam f × (Nf f × Nf a)
Nf (tlam b)     = Nf b

-- normal forms as a GRAMMAR: the subgrammar of `TmG` cut out by `Nf`
NfG : Ctx
NfG u = Σ[ t ∈ Tm u ] Nf t

-- ... and the inclusion, which is a term of the calculus
nfInc : NfG ⊢ TmG
nfInc u = fst

-- ==================================================================
-- §2  ONE STEP, WITH ITS CERTIFICATE.
--
-- `Reduct t` is "a term strictly smaller than `t`", so a step carries
-- the reason the recursion may continue.  Both components come from
-- `Size.agda`; nothing is re-proved.
-- ==================================================================

Reduct : ∀ {u} → Tm u → Type₀
Reduct {u} t = Σ[ t' ∈ Tm u ] (∣ t' ∣ < ∣ t ∣)

-- THE β STEP.  The `<` proof is (β↓) read as an inequality: the redex
-- is `2 + suc (size of the contractum)`, and `_<_` is `Σ k, k + suc m ≡
-- n`, so the witness IS the number 2 together with (★).
betaStep : ∀ {u₁ u₂ u} (s : Use⊎ u₁ u₂ u) (b : Tm (true ∷ u₁)) (a : Tm u₂)
         → Reduct (tapp s (tlam b) a)
betaStep s b a =
    subSize mhere s b a
  , 2 , cong (λ z → suc (suc z)) (substSize mhere s b a)

-- "is the function part a λ?" -- the only decision in the whole
-- normaliser, and it is structural
tryBeta : ∀ {u₁ u₂ u} (s : Use⊎ u₁ u₂ u) (f : Tm u₁) (a : Tm u₂)
        → NotLam f ⊎ Reduct (tapp s f a)
tryBeta s (tvar so)      a = inl tt
tryBeta s (tapp s' g y)  a = inl tt
tryBeta s (tlam b)       a = inr (betaStep s b a)

-- PRIMITIVE (phase 1): THE STEP.  Structural recursion on `Tm`, in the
-- leftmost-outermost order: contract at the root if you can, else in
-- the function part, else in the argument.  The `inl` branches assemble
-- exactly the three conjuncts of `Nf`, so a term is declared normal
-- only when every subterm has been checked.
stepTm : ∀ {u} (t : Tm u) → Nf t ⊎ Reduct t
stepTm (tvar so) = inl tt
stepTm (tlam b) with stepTm b
... | inl nb        = inl nb
... | inr (b' , p)  = inr (tlam b' , suc-≤-suc p)
stepTm (tapp s f a) with tryBeta s f a
... | inr r  = inr r
... | inl nl with stepTm f
...   | inr (f' , p) = inr (tapp s f' a , suc-≤-suc (<-+k p))
...   | inl nf with stepTm a
...     | inr (a' , p) = inr (tapp s f a' , suc-≤-suc (<-k+ p))
...     | inl na       = inl (nl , nf , na)

-- ==================================================================
-- §3  ACCESSIBILITY, WITHOUT A TRANSPORT.
--
-- `accℕ k n` says "every `n ≤ k` is accessible", by structural
-- recursion on the fuel `k`; `wfℕ` closes it at `k = n`.  The `_≤_`
-- arguments are never scrutinised, so nothing here blocks reduction.
-- See the header §2 for why the library's `<-wellfounded` does.
-- ==================================================================

accℕ : (k n : ℕ) → n ≤ k → Acc _<_ n
accℕ zero    n le = acc λ m m<n → E.rec (¬-<-zero (≤-trans m<n le))
accℕ (suc k) n le = acc λ m m<n → accℕ k m (pred-≤-pred (≤-trans m<n le))

wfℕ : (n : ℕ) → Acc _<_ n
wfℕ n = accℕ n n ≤-refl

-- ==================================================================
-- §4  THE NORMALISER.
--
-- Recursion on the accessibility proof, so Agda's termination checker
-- sees a structural descent; the mathematical content is (β↓).
-- ==================================================================

normAcc : ∀ {u} (t : Tm u) → Acc _<_ ∣ t ∣ → Σ[ t' ∈ Tm u ] Nf t'
normAcc t (acc r) with stepTm t
... | inl n        = t , n
... | inr (t' , p) = normAcc t' (r ∣ t' ∣ p)

-- THE HEADLINE.  Total, and normality is in the codomain.
normalise : ∀ {u} (t : Tm u) → Σ[ t' ∈ Tm u ] Nf t'
normalise t = normAcc t (wfℕ ∣ t ∣)

nf : ∀ {u} → Tm u → Tm u
nf t = normalise t .fst

-- THEOREM.  The output is normal -- by projection, because the motive
-- of the recursion said so.
nfNormal : ∀ {u} (t : Tm u) → Nf (nf t)
nfNormal t = normalise t .snd

-- ------------------------------------------------------------------
-- ... and internally.  `normaliseG` is a term of the calculus landing
-- in the subgrammar of normal forms, so the usage is preserved on the
-- nose: NORMALISATION NEITHER DROPS NOR DUPLICATES A FREE VARIABLE.
-- In an untyped calculus the corresponding map does not exist, since β
-- there can erase its argument.
-- ------------------------------------------------------------------

normaliseG : TmG ⊢ NfG
normaliseG u = normalise

normPass : Pass
normPass = nfInc ∘g normaliseG

-- normal forms are fixed by the normaliser -- the `inl` branch of
-- `stepTm` is the only one that can fire at the top of the recursion
-- ... which is not provable generically for the reason `Size.agda`'s
-- header gives (`stepTm` is defined by `with`), but is `refl` at every
-- concrete normal form, as §5 shows.

-- ==================================================================
-- §5  IT COMPUTES.
--
-- Every one of these is `refl`, so the normaliser really runs: the
-- accessibility witness reduces, the substitutions reduce, and the
-- `Eq`-world coercions in `subS` cancel on `Eq.refl` exactly as
-- `Opt.agda` arranged.
-- ==================================================================

-- (a) a normal form is its own normal form
_ : nf idLin ≡ idLin
_ = refl

-- (b) β fires once: `(λx.x)(λx.x) ↦ λx.x`
_ : nf selfApp ≡ idLin
_ = refl

-- (c) `Opt.agda`'s η example.  Its inner redex fires first, exposing a
-- β-redex at the ancestor.  Two steps, and the answer is `idLin`.
_ : nf etaRedex ≡ idLin
_ = refl

-- (d) ... and the one whose function part is already a λ
_ : nf betaEtaRedex ≡ idLin
_ = refl

-- three iterations: `((λx.x)(λx.x)) (λx.x)`
bigApp : Tm []
bigApp = tapp unil selfApp idLin

_ : ∣ bigApp ∣ ≡ 8
_ = refl

_ : nf bigApp ≡ idLin
_ = refl

-- ------------------------------------------------------------------
-- (e) THE SEPARATING TEST -- what a single sweep cannot do.
--
-- A bottom-up fold DOES cope with "the child's contraction exposes a
-- redex at the parent", because the child is rewritten before the
-- parent is examined; that is why (c) succeeds for `Opt.betaPass` too.
-- What it cannot cope with is a redex CREATED BY THE SUBSTITUTION, at
-- a node the sweep has already left.
--
--     applyK  =  (λf. f (λz.z)) (λx.x)
--
-- Contracting the outer redex substitutes `λx.x` for `f`, and the
-- result `(λx.x) (λz.z)` is a redex that did not exist anywhere in the
-- input.  `Opt.betaPass` stops there; `normalise` does not.  This is
-- the gap `Opt.agda`'s header names, exhibited.
-- ------------------------------------------------------------------

Kterm : Tm []
Kterm = tlam (tapp (uleft unil) (tvar tt) idLin0)

applyK : Tm []
applyK = tapp unil Kterm idLin

_ : betaPass [] applyK ≡ selfApp
_ = refl

_ : nf applyK ≡ idLin
_ = refl

-- (f) an OPEN term, so the tests are not all about the empty usage.
-- `x y` is already normal, and `normaliseG` returns it at the same
-- usage it came in at.
appVars : Tm (true ∷ true ∷ [])
appVars = tapp (uleft (uright unil)) (tvar tt) (tvar tt)

_ : nf appVars ≡ appVars
_ = refl

-- (g) ... and an OPEN β-redex: `(λy.y) x  ↦  x`, at usage `true ∷ []`.
-- The result still owns exactly the variable the input owned, which is
-- `normaliseG`'s type saying so at a point.
openBeta : Tm (true ∷ [])
openBeta = tapp (uright unil) idLin0 (tvar tt)

_ : nf openBeta ≡ tvar tt
_ = refl

-- ==================================================================
-- §6  η IS SIZE-DECREASING TOO.
--
-- Recorded, not used.  `λx. f x  ↦  f` removes a `tlam`, a `tapp` and
-- the variable occurrence, and `delT` (STRENGTHENING -- available here
-- precisely because the usage already says `f` does not mention `x`)
-- leaves the size alone.  So the measure of §1 covers βη, and extending
-- `stepTm` is a matter of branches, not of a new termination argument.
-- ==================================================================

etaSize : ∀ {w₁ w₂ u} (s : Use⊎ w₁ w₂ u)
          (f : Tm (false ∷ w₁)) (so : Solo (true ∷ w₂))
        → ∣ tlam (tapp (uright s) f (tvar so)) ∣
        ≡ suc (suc (suc ∣ delT mhere f ∣))
etaSize s f so =
    cong (λ z → suc (suc z)) (+-suc ∣ f ∣ 0 ∙ cong suc (+-zero ∣ f ∣))
  ∙ cong (λ z → suc (suc (suc z))) (sym (size-del mhere f))
