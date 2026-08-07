{-
  `refl` TESTS AT 𝔽₃.

  Every decision is OBSERVED through a sanctioned eliminator (`⊕-E-at`,
  `dec-elim`) rather than matched, and every expected value is an
  element of 𝔽, so a wrong table is a type error.  Each block was
  checked non-vacuous by perturbation.
-}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Instances.Field.Tests where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.List using ([]; _∷_)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Domain
open import TheoryGrammar.SemanticAction using (passes; _↦_; _at_; module ActFib)
open import TheoryGrammar.Instances.Field.Base
open import TheoryGrammar.Instances.Field.Partial
open import TheoryGrammar.Instances.Field.NoPoint

open ActFib fldFib using (Δ; run; caseA; pureA; refute; witness)

-- ==================================================================
-- 1.  The tables.
-- ==================================================================

private
  _ : f1 +𝔽 f2 ≡ f0
  _ = refl

  _ : f2 +𝔽 f2 ≡ f1
  _ = refl

  _ : f2 ·𝔽 f2 ≡ f1
  _ = refl

  _ : f2 ·𝔽 f1 ≡ f2
  _ = refl

-- ==================================================================
-- 2.  THE INVERSE, READ OFF A SPLITTING.  `parts invOp m sp tt` is the
-- element whose inverse is m; the splitting comes from the internal
-- proof that m is nonzero, so nothing here inspects 𝔽.
-- ==================================================================

inverse-of : (m : 𝔽) → Nonzero m → 𝔽
inverse-of m k = fldFib .parts invOp m (nonzero⊢img-inv m k .fst) tt

nonzero-f1 : Nonzero f1
nonzero-f1 = img-inv⊢nonzero f1 (tt , λ _ → tt)

nonzero-f2 : Nonzero f2
nonzero-f2 = img-inv⊢nonzero f2 (tt , λ _ → tt)

private
  _ : inverse-of f1 nonzero-f1 ≡ f1
  _ = refl

  _ : inverse-of f2 nonzero-f2 ≡ f2
  _ = refl

  -- the domain witness produced by `nonzero⊢dom-inv`: which element has
  -- f2 as its inverse
  _ : nonzero⊢dom-inv f2 nonzero-f2 .fst ≡ f2
  _ = refl

  _ : nonzero⊢dom-inv f1 nonzero-f1 .fst ≡ f1
  _ = refl

-- ==================================================================
-- 3.  THE COVERING WITNESSES for + and ·, through the generic
-- `covering→img`.  These exercise `splitEq` (transport of a splitting
-- along an `Eq`), which computes because the equation is `Eq.refl`.
-- ==================================================================

private
  _ : rngFib .parts addR f2 (img-add f2 tt .fst) lhs ≡ f0
  _ = refl

  _ : rngFib .parts addR f2 (img-add f2 tt .fst) rhs ≡ f2
  _ = refl

  _ : rngFib .parts mulR f2 (img-mul f2 tt .fst) lhs ≡ f1
  _ = refl

  _ : rngFib .parts mulR f2 (img-mul f2 tt .fst) rhs ≡ f2
  _ = refl

  -- and the round trip through `img→covering`, which needs `Honest`
  _ : cover-add-again f1 .fst lhs ≡ f0
  _ = refl

  _ : cover-add-again f1 .fst rhs ≡ f1
  _ = refl

  -- the DOMAIN side: `point→dom` at a ring slot names the composite the
  -- argument was placed in.  f2 sits in the left summand of f2 + 0 = f2.
  _ : dom-add-total f2 tt .fst ≡ f2
  _ = refl

  -- and in the right factor of 1 · f1 = f1
  _ : dom-mul-total f1 tt .fst ≡ f1
  _ = refl

-- ==================================================================
-- 4.  THE POINT OF THE FRAGMENT still computes: `rngPoint` is a real
-- total algebra on the same carrier.
-- ==================================================================

private
  _ : rngPoint .op addR (λ { lhs → f2 ; rhs → f2 }) ≡ f1
  _ = refl

  _ : rngPoint .op mulR (λ { lhs → f2 ; rhs → f2 }) ≡ f1
  _ = refl

  _ : rngPoint .op oneR (λ ()) ≡ f1
  _ = refl

-- ==================================================================
-- 5.  THE DECISION, OBSERVED AS A TERM.
--
-- A reader of type `𝔽 → 𝔽` would externalise at the DEFINITION, one
-- step early.  These observations are `⊤G ⊢ Δ 𝔽` instead -- built from
-- `caseA`/`pureA`, so still inside the calculus -- and `run` belongs in
-- the `refl` line.  Batching the cases into a suite writes the term
-- under test once.
-- ==================================================================

imgA decA : ⊤G ⊢ Δ 𝔽
imgA = caseA (pureA 𝔽 f1) (pureA 𝔽 f0) ∘⊢ dec-inv
decA = caseA (pureA 𝔽 f1) (pureA 𝔽 f0) ∘⊢ dec-invOp

_ : passes (run imgA at (f0 ↦ f0 ∷ f1 ↦ f1 ∷ f2 ↦ f1 ∷ []))
_ = refl

-- ... and the NORMALISED decision agrees, which is what says
-- `toDec`/`largest` compute
_ : passes (run decA at (f0 ↦ f0 ∷ f1 ↦ f1 ∷ f2 ↦ f1 ∷ []))
_ = refl

-- ==================================================================
-- 6.  THE REJECTION IS A THEOREM, and this instance shows why a
-- POSITIVE complement is worth having.
--
-- `refute` (TheoryGrammar.SemanticAction) turns a negative observation
-- into whatever the error branch carries.  `dec-invOp` carries
-- `¬G (Imgˢ invOp)` and yields a refutation; `dec-inv` carries the
-- REPRESENTABLE `⌈ f0 ⌉` and yields the proof that the element IS zero.
-- Same combinator, same `refl`, strictly more information -- because
-- `invDecision`'s complement was chosen positively.
-- ==================================================================

no-img-f0 : (¬G (Imgˢ invOp)) f0
no-img-f0 = refute (Imgˢ invOp) (¬G (Imgˢ invOp)) dec-invOp f0 refl

is-zero-f0 : ⌈ f0 ⌉ f0
is-zero-f0 = refute (Imgˢ invOp) ⌈ f0 ⌉ dec-inv f0 refl

-- ... and the accepting side hands back the splitting itself
inv-witness-f2 : Imgˢ invOp f2
inv-witness-f2 = witness (Imgˢ invOp) ⌈ f0 ⌉ dec-inv f2 refl
