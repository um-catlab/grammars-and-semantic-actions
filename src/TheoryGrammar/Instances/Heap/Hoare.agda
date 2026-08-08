{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- WEAKEST PRECONDITIONS, AND THE FRAME RULE. Everything up to here is the
   ASSERTION logic -- `Gr = Heap → Type` with `&`/`⇒` pointwise and
   `∗`/`─∗` from the `Fibered`, i.e. a model of BI. -}
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
open import TheoryGrammar.Hoare

open import TheoryGrammar.Instances.Heap.Precise public

-- COMMANDS AND THE TWO IMAGES, FROM THE GENERIC LAYER.

-- `Endo` is `Hoare Fib Fib` plus the endo-only maps (`skip` and its
-- three rules), which is exactly the shape a heap command has.
private module H = Endo heapFib

open H public
  using (wp; sp; sp⊣wp; ⟪_⟫_⟪_⟫; wp-map; consequence; fn; wp-fn;
         skip; wp-skip; skip-I; skip-E)

-- the generic `Cmd` is level- and sort-indexed; at one sort and ℓ-zero
-- it is exactly the relation this file used to define
Cmd : Type₁
Cmd = H.Cmd ℓ-zero tt tt

-- A DETERMINISTIC COMMAND IS A FUNCTION, AND `wp` AT ONE IS THE
-- CARTESIAN LIFT.  `wp (fn f) Q` really is `Q ∘ f` -- reindexing.
-- The proof is the Yoneda lemma, exactly as `⌈⌉-UP` is.

-- LOCALITY. Running `c` on a heap split as `u ⊎ v` touches only `u`: the
-- result splits as `u' ⊎ v` with the SAME `v`, and `c u u'`.

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

-- THE FRAME RULE. Internal: `⊗ˢ-E` consumes the `∗`, locality moves the
-- split across the command, `⊗ˢ-I` rebuilds it.

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

-- `skip`, as a sanity check: it is local, and its `wp` is the identity.

skipLocal : Local skip
skipLocal u v h il d .(h) Eq.refl = u , il , d , Eq.refl

