{-
  THE FOUR MODES SEPARATE, and they compute.

  Each `refl` holds only if `Uses`, the promodel's `dec-⊗ˢ`, the
  residual's transport and `dec-map` all reduce.  Acceptance is OBSERVED
  with the generic `okA` (`accepts`, a TERM `⊤G ⊢ Δ Bool`), never by
  matching a
  decision.

                 ordered  linear  affine  relevant
      λx.x          T        T       T        T
      λx.λy.x       F        F       T        F     -- weakening only
      λx.x x        F        F       F        T     -- contraction only
      λx.λy.y x     F        T       T        T     -- exchange only
      λx.λy.x y     T        T       T        T
      S             F        F       F        T     -- contraction only
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Modes.Tests where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool
open import Cubical.Data.Unit
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Nat using (ℕ; discreteℕ)

open import TheoryGrammar.SemanticAction using (passes; _↦_; _at_)
open import TheoryGrammar.Instances.Lambda.Fibered
open import TheoryGrammar.Instances.Lambda.Modes.Instances

open Terms ℕ using (Raw; var; app; lam)
open Modes ℕ discreteℕ

tI tK tW tC tB tS : Raw
tI = lam 0 (var 0)                                   -- λx. x
tK = lam 0 (lam 1 (var 0))                           -- λx. λy. x
tW = lam 0 (app (var 0) (var 0))                     -- λx. x x
tC = lam 0 (lam 1 (app (var 1) (var 0)))             -- λx. λy. y x
tB = lam 0 (lam 1 (app (var 0) (var 1)))             -- λx. λy. x y
tS = lam 0 (lam 1 (lam 2 (app (app (var 0) (var 2))  -- λx. λy. λz. (x z)(y z)
                              (app (var 1) (var 2)))))

-- ==================================================================
-- ORDERED
-- ==================================================================
_ : passes ((λ t → Ord.run (Ord.accepts t) []) at
             ( tI ↦ true
             ∷ tK ↦ false
             ∷ tW ↦ false
             ∷ tC ↦ false
             ∷ tB ↦ true
             ∷ tS ↦ false
             ∷ [] ))
_ = refl

-- ==================================================================
-- LINEAR
-- ==================================================================
_ : passes ((λ t → Lin.run (Lin.accepts t) []) at
             ( tI ↦ true
             ∷ tK ↦ false
             ∷ tW ↦ false
             ∷ tC ↦ true
             ∷ tB ↦ true
             ∷ tS ↦ false
             ∷ [] ))
_ = refl

-- ==================================================================
-- AFFINE
-- ==================================================================
_ : passes ((λ t → Aff.run (Aff.accepts t) []) at
             ( tI ↦ true
             ∷ tK ↦ true
             ∷ tW ↦ false
             ∷ tC ↦ true
             ∷ tB ↦ true
             ∷ tS ↦ false
             ∷ [] ))
_ = refl

-- ==================================================================
-- RELEVANT
-- ==================================================================
_ : passes ((λ t → Rel.run (Rel.accepts t) []) at
             ( tI ↦ true
             ∷ tK ↦ false
             ∷ tW ↦ true
             ∷ tC ↦ true
             ∷ tB ↦ true
             ∷ tS ↦ true
             ∷ [] ))
_ = refl

-- ==================================================================
-- The LEAF checker of each mode, which is what `check` bottoms out in.
-- `decLf n` decides "this context is exactly the singleton n", so its
-- world is a CONTEXT -- a different sort from the tests above, read by
-- the same `accepts?`.
-- ==================================================================

leafOrd : (n : ℕ) → Ord._⊢_ Ord.⊤G (Ord.Δ Bool)
leafOrd n = Ord.okA (Ord.Lf n) (Ord.¬G (Ord.Lf n)) Ord.∘g Ord.decLf n

leafLin : (n : ℕ) → Lin._⊢_ Lin.⊤G (Lin.Δ Bool)
leafLin n = Lin.okA (Lin.Lf n) (Lin.¬G (Lin.Lf n)) Lin.∘g Lin.decLf n

leafAff : (n : ℕ) → Aff._⊢_ Aff.⊤G (Aff.Δ Bool)
leafAff n = Aff.okA (Aff.Lf n) (Aff.¬G (Aff.Lf n)) Aff.∘g Aff.decLf n

leafRel : (n : ℕ) → Rel._⊢_ Rel.⊤G (Rel.Δ Bool)
leafRel n = Rel.okA (Rel.Lf n) (Rel.¬G (Rel.Lf n)) Rel.∘g Rel.decLf n

-- ORDERED and LINEAR: the context must be the singleton, on the nose
_ : passes ((λ Γ → Ord.run (leafOrd 0) Γ) at
             ( (0 ∷ [])     ↦ true
             ∷ []           ↦ false
             ∷ (1 ∷ [])     ↦ false
             ∷ (0 ∷ 0 ∷ []) ↦ false
             ∷ [] ))
_ = refl

_ : passes ((λ Γ → Lin.run (leafLin 0) Γ) at
             ((0 ∷ []) ↦ true ∷ (0 ∷ 1 ∷ []) ↦ false ∷ []))
_ = refl

-- AFFINE admits WEAKENING, RELEVANT admits CONTRACTION
_ : passes ((λ Γ → Aff.run (leafAff 0) Γ) at
             ((0 ∷ []) ↦ true ∷ [] ↦ false ∷ []))
_ = refl

_ : passes ((λ Γ → Rel.run (leafRel 0) Γ) at
             ((0 ∷ []) ↦ true ∷ (1 ∷ []) ↦ false ∷ []))
_ = refl

-- ==================================================================
-- THE TABLE, AS THEOREMS.
--
-- Everything above is a computation check: it says the checker returns
-- `false`.  That is strictly weaker than what the modes actually claim.
-- `refute` (TheoryGrammar.SemanticAction) turns each negative
-- observation into the REFUTATION the decision was carrying all along --
--
--     Uses t []  →  ⊥
--
-- -- so the `false` entries of the table become theorems about the
-- substructural discipline rather than reports about an algorithm.  The
-- inputs are exactly the `refl`s already proved above.
-- ==================================================================

refuteOrd : (t : Raw) → Ord.run (Ord.accepts t) [] ≡ false
          → (Ord.¬G (Ord.Uses t)) []
refuteOrd t = Ord.refute (Ord.Uses t) (Ord.¬G (Ord.Uses t)) (Ord.check t) []

refuteLin : (t : Raw) → Lin.run (Lin.accepts t) [] ≡ false
          → (Lin.¬G (Lin.Uses t)) []
refuteLin t = Lin.refute (Lin.Uses t) (Lin.¬G (Lin.Uses t)) (Lin.check t) []

refuteAff : (t : Raw) → Aff.run (Aff.accepts t) [] ≡ false
          → (Aff.¬G (Aff.Uses t)) []
refuteAff t = Aff.refute (Aff.Uses t) (Aff.¬G (Aff.Uses t)) (Aff.check t) []

refuteRel : (t : Raw) → Rel.run (Rel.accepts t) [] ≡ false
          → (Rel.¬G (Rel.Uses t)) []
refuteRel t = Rel.refute (Rel.Uses t) (Rel.¬G (Rel.Uses t)) (Rel.check t) []

-- ORDERED rejects everything but the two that use their binders once,
-- left to right.
no-ord-K : (Ord.¬G (Ord.Uses tK)) []
no-ord-K = refuteOrd tK refl

no-ord-W : (Ord.¬G (Ord.Uses tW)) []
no-ord-W = refuteOrd tW refl

no-ord-C : (Ord.¬G (Ord.Uses tC)) []      -- exchange really is unavailable
no-ord-C = refuteOrd tC refl

no-ord-S : (Ord.¬G (Ord.Uses tS)) []
no-ord-S = refuteOrd tS refl

-- LINEAR: exchange is fine, weakening and contraction are not.
no-lin-K : (Lin.¬G (Lin.Uses tK)) []      -- no weakening
no-lin-K = refuteLin tK refl

no-lin-W : (Lin.¬G (Lin.Uses tW)) []      -- no contraction
no-lin-W = refuteLin tW refl

no-lin-S : (Lin.¬G (Lin.Uses tS)) []
no-lin-S = refuteLin tS refl

-- AFFINE has weakening, so only the contracting terms are refuted.
no-aff-W : (Aff.¬G (Aff.Uses tW)) []
no-aff-W = refuteAff tW refl

no-aff-S : (Aff.¬G (Aff.Uses tS)) []
no-aff-S = refuteAff tS refl

-- RELEVANT has contraction, so only the weakening term is refuted --
-- and `tS`, which `Aff` refutes, is now DERIVABLE.  The two modes
-- separate, and both directions are theorems.
no-rel-K : (Rel.¬G (Rel.Uses tK)) []
no-rel-K = refuteRel tK refl

-- ... the positive direction, by the dual combinator
yes-rel-S : Rel.Uses tS []
yes-rel-S = Rel.witness (Rel.Uses tS) (Rel.¬G (Rel.Uses tS)) (Rel.check tS) []
                        refl

yes-ord-I : Ord.Uses tI []
yes-ord-I = Ord.witness (Ord.Uses tI) (Ord.¬G (Ord.Uses tI)) (Ord.check tI) []
                        refl

yes-lin-C : Lin.Uses tC []
yes-lin-C = Lin.witness (Lin.Uses tC) (Lin.¬G (Lin.Uses tC)) (Lin.check tC) []
                        refl
