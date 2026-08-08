{- THE FOUR MODES SEPARATE, and they compute. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Modes.Tests where

open import Cubical.Data.Bool using (true; false)
open import Cubical.Data.List using ([]; _∷_)
open import Cubical.Data.Nat using (ℕ; discreteℕ)
open import Cubical.Foundations.Prelude

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

-- ORDERED
_ : passes ((λ t → Ord.run (Ord.accepts t) []) at
             ( tI ↦ true
             ∷ tK ↦ false
             ∷ tW ↦ false
             ∷ tC ↦ false
             ∷ tB ↦ true
             ∷ tS ↦ false
             ∷ [] ))
_ = refl

-- LINEAR
_ : passes ((λ t → Lin.run (Lin.accepts t) []) at
             ( tI ↦ true
             ∷ tK ↦ false
             ∷ tW ↦ false
             ∷ tC ↦ true
             ∷ tB ↦ true
             ∷ tS ↦ false
             ∷ [] ))
_ = refl

-- AFFINE
_ : passes ((λ t → Aff.run (Aff.accepts t) []) at
             ( tI ↦ true
             ∷ tK ↦ true
             ∷ tW ↦ false
             ∷ tC ↦ true
             ∷ tB ↦ true
             ∷ tS ↦ false
             ∷ [] ))
_ = refl

-- RELEVANT
_ : passes ((λ t → Rel.run (Rel.accepts t) []) at
             ( tI ↦ true
             ∷ tK ↦ false
             ∷ tW ↦ true
             ∷ tC ↦ true
             ∷ tB ↦ true
             ∷ tS ↦ true
             ∷ [] ))
_ = refl

-- The LEAF checker of each mode, which is what `check` bottoms out in.

-- ORDERED and LINEAR: the context must be the singleton, on the nose
_ : passes ((λ Γ → Ord.run (Ord.acceptsLf 0) Γ) at
             ( (0 ∷ [])     ↦ true
             ∷ []           ↦ false
             ∷ (1 ∷ [])     ↦ false
             ∷ (0 ∷ 0 ∷ []) ↦ false
             ∷ [] ))
_ = refl

_ : passes ((λ Γ → Lin.run (Lin.acceptsLf 0) Γ) at
             ((0 ∷ []) ↦ true ∷ (0 ∷ 1 ∷ []) ↦ false ∷ []))
_ = refl

-- AFFINE admits WEAKENING, RELEVANT admits CONTRACTION
_ : passes ((λ Γ → Aff.run (Aff.acceptsLf 0) Γ) at
             ((0 ∷ []) ↦ true ∷ [] ↦ false ∷ []))
_ = refl

_ : passes ((λ Γ → Rel.run (Rel.acceptsLf 0) Γ) at
             ((0 ∷ []) ↦ true ∷ (1 ∷ []) ↦ false ∷ []))
_ = refl

-- THE TABLE, AS THEOREMS. Everything above is a computation check: it says
-- the checker returns `false`.

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
