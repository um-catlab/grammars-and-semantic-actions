{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  WEAKEST PRECONDITIONS, AND THE FRAME RULE.

  Everything up to here is the ASSERTION logic -- `Gr = Heap → Type` with
  `&`/`⇒` pointwise and `∗`/`─∗` from the promodel, i.e. a model of BI.
  What was missing is the PROGRAM logic, and the point of this file is
  that it needs no new category.

  A command is a relation `c : Heap → Heap → Type`, ordinary metalanguage
  data.  The weakest precondition

      wp c Q h  =  (h' : Heap) → c h h' → Q h'

  is again a `Heap → Type`, hence again a `Gr`.  So a Hoare triple is an
  ENTAILMENT of the logic we already have:

      ⟪ P ⟫ c ⟪ Q ⟫   =   P ⊢ wp c Q

  and the frame rule becomes an internal theorem rather than a
  meta-level soundness argument.

  ------------------------------------------------------------------
  WHY THIS IS REINDEXING (and `wp` a Cartesian lift)
  ------------------------------------------------------------------

  `TheoryTy ℓ s = carrier s → Type ℓ` is a DISPLAYED presentation: a
  grammar is a family over the carrier, and the whole development is
  fibred over it -- which is what `Fibered.agda` is named for.  In that
  reading:

    * a command `c` is a profunctor `Heap ⇸ Heap` (both discrete);
    * `sp c` is its direct image, `wp c` its right adjoint;
    * for a FUNCTION `f`, `wp (fn f) Q` is `Q ∘ f` -- reindexing along
      `f`, i.e. the CARTESIAN LIFT of `f` in the family fibration.

  `wp-fn` below is exactly that statement, and it is the Yoneda lemma
  (`⌈⌉-UP`) in disguise.  So `wp` generalises `ChangeOfTheory.pull` from
  functions to relations: `pull` reindexes along a `ModelHom`, `wp`
  reindexes along a span.

  That analogy predicts the shape of the frame rule, and the prediction
  holds.  `ChangeOfTheory` proves the additive fragment reindexes
  DEFINITIONALLY and the multiplicative fragment only LAXLY, with
  invertibility exactly when the map REFLECTS SPLITTINGS.  Here `wp`'s
  interaction with `∗` is likewise lax, and the side condition that makes
  it hold is LOCALITY -- which is the same shape as reflecting
  splittings: a decomposition downstream must come from one upstream.

  ------------------------------------------------------------------
  PHASE.  `wp`, `sp`, the adjunction, `wp-fn` and `frame-wp` are phase 2
  up to three marked primitives (`mkSplit`, `split-Ilv`, and `split-#`
  from `Connectives`), which are the interface to `HeapSplit`'s
  components.  No heap is matched in any theorem.
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Heap.Hoare where

open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib

open import TheoryGrammar.Instances.Heap.Precise public

-- ==================================================================
-- Commands, and the two images.
-- ==================================================================

Cmd : Type₁
Cmd = Heap → Heap → Type₀

-- WEAKEST PRECONDITION -- reindexing along the relation.
wp : Cmd → Gr → Gr
wp c Q h = (h' : Heap) → c h h' → Q h'

-- STRONGEST POSTCONDITION -- the direct image.
sp : Cmd → Gr → Gr
sp c P h' = Σ[ h ∈ Heap ] (P h × c h h')

-- THE ADJUNCTION `sp c ⊣ wp c`.  Currying and swapping; both round
-- trips are `refl`, because Σ and Π both have η.
sp⊣wp : (c : Cmd) (P Q : Gr) → Iso (sp c P ⊢ Q) (P ⊢ wp c Q)
sp⊣wp c P Q .Iso.fun f h p h' r = f h' (h , p , r)
sp⊣wp c P Q .Iso.inv g h' (h , p , r) = g h p h' r
sp⊣wp c P Q .Iso.sec _ = refl
sp⊣wp c P Q .Iso.ret _ = refl

-- ==================================================================
-- HOARE TRIPLES are entailments.  Nothing new is introduced.
-- ==================================================================

⟪_⟫_⟪_⟫ : Gr → Cmd → Gr → Type₀
⟪ P ⟫ c ⟪ Q ⟫ = P ⊢ wp c Q

-- the rule of consequence, from `∘g` alone
consequence : {P P' Q Q' : Gr} (c : Cmd)
            → P' ⊢ P → Q ⊢ Q' → ⟪ P ⟫ c ⟪ Q ⟫ → ⟪ P' ⟫ c ⟪ Q' ⟫
consequence c pre post tr h p h' r = post h' (tr h (pre h p) h' r)

-- ==================================================================
-- A DETERMINISTIC COMMAND IS A FUNCTION, AND `wp` AT ONE IS THE
-- CARTESIAN LIFT.  `wp (fn f) Q` really is `Q ∘ f` -- reindexing.
-- The proof is the Yoneda lemma, exactly as `⌈⌉-UP` is.
-- ==================================================================

fn : (Heap → Heap) → Cmd
fn f h h' = f h Eq.≡ h'

wp-fn : (f : Heap → Heap) (Q : Gr) (h : Heap)
      → Iso (wp (fn f) Q h) (Q (f h))
wp-fn f Q h .Iso.fun w = w (f h) Eq.refl
wp-fn f Q h .Iso.inv q .(f h) Eq.refl = q
wp-fn f Q h .Iso.sec _ = refl
wp-fn f Q h .Iso.ret w = funExt λ _ → funExt λ { Eq.refl → refl }

-- ==================================================================
-- LOCALITY.  Running `c` on a heap split as `u ⊎ v` touches only `u`:
-- the result splits as `u' ⊎ v` with the SAME `v`, and `c u u'`.
--
-- This is the frame property, and note its shape -- a decomposition of
-- the OUTPUT must come from one of the INPUT.  That is `ReflectsSplit`
-- from `ChangeOfTheory`, transposed from a function to a relation.
-- ==================================================================

Local : Cmd → Type₀
Local c = (u v h : Heap) → Ilv u v h → u # v
        → (h' : Heap) → c h h'
        → Σ[ u' ∈ Heap ] (Ilv u' v h' × (u' # v) × c u u')

-- PRIMITIVES (phase 1): the interface to `HeapSplit`'s components, so
-- that no theorem below has to match one.  `split-#` is in `Connectives`.
mkSplit : {u v h : Heap} → Ilv u v h → u # v → heapFib .Split appop h
mkSplit {u} {v} il d = u , v , il , d

split-Ilv : (h : Heap) (sp : heapFib .Split appop h)
          → Ilv (heapFib .parts appop h sp true)
                (heapFib .parts appop h sp false) h
split-Ilv h (u , v , il , d) = il

-- ==================================================================
-- THE FRAME RULE.  Internal: `⊗ˢ-E` consumes the `∗`, locality moves
-- the split across the command, `⊗ˢ-I` rebuilds it.
--
-- Compare `frame` in `Connectives`, which is `⊗ˢ-map` and needs no
-- hypothesis at all.  That is the ASSERTION frame rule -- free, because
-- functoriality is free.  This is the COMMAND frame rule, and the whole
-- difference is `Local`.
-- ==================================================================

frame-wp : (c : Cmd) → Local c → (Q R : Gr)
         → ((wp c Q) ∗ R) ⊢ wp c (Q ∗ R)
frame-wp c loc Q R =
  ⊗ˢ-E appop {A = boolΠ {M = λ _ → Gr} (wp c Q) R}
    (λ h sp k h' ch →
       let u  = heapFib .parts appop h sp true
           v  = heapFib .parts appop h sp false
           lc = loc u v h (split-Ilv h sp) (split-# h sp) h' ch
           u' = lc .fst
           il' = lc .snd .fst
           d'  = lc .snd .snd .fst
           cu  = lc .snd .snd .snd
       in ⊗ˢ-I appop {A = boolΠ {M = λ _ → Gr} Q R} h' (mkSplit il' d')
            (boolΠ {M = λ a → boolΠ {M = λ _ → Gr} Q R a
                                (heapFib .parts appop h' (mkSplit il' d') a)}
                   (k true u' cu) (k false)))

-- ==================================================================
-- `skip`, as a sanity check: it is local, and its `wp` is the identity.
-- ==================================================================

skip : Cmd
skip = fn (λ h → h)

skipLocal : Local skip
skipLocal u v h il d .(h) Eq.refl = u , il , d , Eq.refl

wp-skip : (Q : Gr) (h : Heap) → Iso (wp skip Q h) (Q h)
wp-skip Q = wp-fn (λ h → h) Q
