{-
  BI'S ADJUNCTION  (P ∗ Q ⊢ R) ≅ (Q ⊢ P ─∗ R),  AND WHERE IT DIVERGES.

  `⊸ᶠ` at `heapFocus` IS the textbook magic wand on the nose -- `wandIso`,
  both round trips `refl`.  The adjunction itself is NOT free, and the
  reason is in what the framework's two universal properties classify:
  `⊗ˢ-UP` lands on `MultiHomˢ`, whose splitting is indexed by the WHOLE,
  and `⊸ᶠ-UP` on `FocusedHom`, indexed by the focused SLOT.  Same data
  reassociated -- but the payload changes from an n-ary slot function to
  two separate arguments.  `refocus` is that identification, and it is
  where the cost sits:

      refocus-β   refl     Σ-η reassociates, Unit-η collapses `Rest`
      refocus-η   funExt   the slot function over `MonAr appop = Bool`
      ∗-η         refl     all three components definitional
      ∗-β         funExt   exactly one, inherited from `refocus-η`

  `Bool` is `data`, so a function out of it has no η, and `∗-β` cannot be
  made definitional without giving the ARITY type η.  That is the defect
  `Fibered`'s own header names for `Eq._≡_`, one level up.

  DEFINES `Wand` and `wandIso`; `Multi`/`Foc` with the refocusing
  `refocus`/`unfocus`/`refocus-β`/`refocus-η`/`refocus-UP`; the
  adjunction `curry∗`/`uncurry∗`/`∗-η`/`∗-β`/`∗─∗-UP`; and `wand-app`.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Heap.Adjunction where

open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit
open import Cubical.Data.List using (List; []; _∷_)

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered

open import TheoryGrammar.Instances.Heap.Connectives public

-- ==================================================================
-- 1.  `⊸ᶠ` IS THE TEXTBOOK WAND, on the nose.
--
-- `Wand` is separation logic's definition written out.  It differs from
-- `⊸ᶠ` only by currying a Σ and by `Rest = Unit`, and both round trips
-- are `refl`.
-- ==================================================================

-- `Wand A B v` DENOTES "hand me any heap DISJOINT from mine satisfying
-- A, and the join satisfies B".  Disjointness is a hypothesis of the
-- function, so a caller must already hold the proof -- it is never
-- re-tested inside.
Wand : Gr → Gr → Gr
Wand A B v = (u h : Heap) → Ilv u v h → u # v → A u → B h

wandIso : (A B : Gr) (v : Heap) → Iso ((A ─∗ B) v) (Wand A B v)
wandIso A B v .Iso.fun f u h ilv apt a = f (u , h , ilv , apt) (λ _ → a)
wandIso A B v .Iso.inv g sa ps =
  g (sa .fst) (sa .snd .fst) (sa .snd .snd .fst) (sa .snd .snd .snd) (ps tt)
wandIso A B v .Iso.sec _ = refl
wandIso A B v .Iso.ret _ = refl

-- ==================================================================
-- 2.  REFOCUSING: the whole-indexed and slot-indexed hom-sets.
-- ==================================================================

module _ (P Q R : Gr) where

  Multi : Type₀
  Multi = MultiHomˢ appop (boolΠ P Q) R

  Foc : Type₀
  Foc = FocusedHom {A = boolΠ P Q} {B = R}

  refocus : Multi → Foc
  refocus g v sa q ps =
    g (sa .snd .fst) (sa .fst , v , sa .snd .snd) (boolΠ (ps tt) q)

  unfocus : Foc → Multi
  unfocus f m (u , v , ilv , apt) k = f v (u , m , ilv , apt) (k false) (λ _ → k true)

  -- refl: Σ-η reassociates the splitting, Unit-η collapses `Rest`
  refocus-β : (f : Foc) → refocus (unfocus f) ≡ f
  refocus-β f = refl

  -- funExt, and the reason is `MonAr appop = Bool` being `data`
  refocus-η : (g : Multi) → unfocus (refocus g) ≡ g
  refocus-η g = funExt λ m → funExt λ sp → funExt λ k →
    cong (g m sp) (funExt (boolΠ refl refl))

  refocus-UP : Iso Multi Foc
  refocus-UP .Iso.fun = refocus
  refocus-UP .Iso.inv = unfocus
  refocus-UP .Iso.sec = refocus-β
  refocus-UP .Iso.ret = refocus-η

  -- ================================================================
  -- 3.  THE ADJUNCTION, composed from `⊗ˢ-UP`, `refocus`, `⊸ᶠ-UP`.
  -- ================================================================

  curry∗ : (P ∗ Q ⊢ R) → (Q ⊢ (P ─∗ R))
  curry∗ f = ⊸ᶠ-lam {A = boolΠ P Q} {B = R}
               (refocus (curryˢ appop {A = boolΠ P Q} {B = R} f))

  uncurry∗ : (Q ⊢ (P ─∗ R)) → (P ∗ Q ⊢ R)
  uncurry∗ g = uncurryˢ appop {A = boolΠ P Q} {B = R}
                 (unfocus (⊸ᶠ-app {A = boolΠ P Q} {B = R} g))

  -- ALL THREE components are definitional in this direction
  ∗-η : (g : Q ⊢ (P ─∗ R)) → curry∗ (uncurry∗ g) ≡ g
  ∗-η g = refl

  -- ... and in the other, `refocus-η` is the only cost
  ∗-β : (f : P ∗ Q ⊢ R) → uncurry∗ (curry∗ f) ≡ f
  ∗-β f = cong (uncurryˢ appop {A = boolΠ P Q} {B = R})
               (refocus-η (curryˢ appop {A = boolΠ P Q} {B = R} f))

  ∗─∗-UP : Iso (P ∗ Q ⊢ R) (Q ⊢ (P ─∗ R))
  ∗─∗-UP .Iso.fun = curry∗
  ∗─∗-UP .Iso.inv = uncurry∗
  ∗─∗-UP .Iso.sec = ∗-η
  ∗─∗-UP .Iso.ret = ∗-β

-- ==================================================================
-- 4.  Modus ponens for the wand: the counit, i.e. `uncurry∗` at the
--     identity.  No new content, which is the point.
-- ==================================================================

wand-app : (P R : Gr) → (P ∗ (P ─∗ R)) ⊢ R
wand-app P R = uncurry∗ P (P ─∗ R) R idg
