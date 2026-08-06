{-
  VIEWS: destructuring the world, internally.

  A view, in McBride's sense, is a datatype whose constructors are
  legitimate patterns for something else, together with a total function
  into it.  This calculus already has that, unnamed, and it costs no new
  infrastructure -- which is the point of this file.  `⟦ F ⟧c` (from
  `TheoryGrammar.Inductive`) is spelled in the connectives already: its
  `⊕e` IS `⊕ᴰ`, its `⊗e` IS `⊗ˢ`.  So a pattern is just a grammar built
  from `⌈_⌉`, `⊗ˢ`, `⊕`, `⊕ᴰ`, and

      a VIEW of a world is a term  ⊤G ⊢ P.

  Read logically: `⊤G ⊢ P` says P holds of EVERY world, so a view is an
  internal tautology whose statement happens to be a pattern.  A view
  MORPHISM is then just a term `P ⊢ Q` -- no new notion at all -- and a
  program is a view plus an algebra.

  Three abbreviations and one real combinator:

      Cover P  =  ⊤G ⊢ P            -- a total view
      Probe P  =  ⊤G ⊢ Dec⟨ P ⟩     -- a partial view; coverage-checking
                                    --   and decidability are ONE notion
      P ⇛ Q    =  P ⊢ Q             -- a view morphism

  and `withView`, which is `with`-abstraction: to USE a view in the
  middle of a derivation that already carries a payload `B`, put the
  view into the context with `&-I`, then distribute.  Both halves of
  that already exist (`Distributive.dist&r`, `Distributive.⊕ᴰ-&-in`), so
  `TheoryGrammar.Distributive` is, read correctly, the `with`-abstraction
  module.

  TWO FINDINGS FROM THE INSTANCES, recorded here so they are not
  rediscovered:

  (1) At `B = ⊤G` the payload is vacuous and `withView` degenerates to
      `_∘g_`.  That is why `Bags.Quicksort.qcoalg` was ALREADY in view
      form: its source is `⊤'`, so `⊕-elim … ∘g bagCase` is exactly
      `caseOf bagCase …` and there was nothing to rewrite.  A coalgebra
      out of `⊤` and a view are the same thing.

  (2) `withView` does NOT reach `CYK.Parser.tryCut`.  That scrutinises
      covers at the SLOT indices `u`, `v` of a splitting and concludes at
      the WHOLE `w`; `&-I` and `dist&r` are index-preserving, so no
      composite of them can cross.  This is the same boundary as the one
      match in `Decidable.Tensor.dec-⊗`, and for the same reason: the
      connective that moves between a slot and the whole is the residual
      `⊸ᶠ`, not the additives.  Do not expect the additive `with` to fix
      it.
-}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.View where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit

open import TheoryGrammar.Base
open import TheoryGrammar.Substrate
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded
open import TheoryGrammar.Distributive
open import TheoryGrammar.Decidable.Tensor

private variable ℓS ℓ ℓ' ℓX ℓP ℓA ℓB ℓC ℓM ℓY ℓV : Level

-- ==================================================================
-- The view layer.  Deliberately NOT re-exporting `RulesS` -- instances
-- already open it themselves, and a second copy would make every
-- combinator ambiguous at the use site.
-- ==================================================================

module Views {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (Sub : Substrate σ ℓX ℓP) where

  open DecSub Sub
  open Dist ⌊ Sub ⌋ using (dist&r; ⊕ᴰ-&-in)

  private variable s : S

  -- ================================================================
  -- The three abbreviations.  `_⇛_` is `_⊢_`; that it needs no new
  -- definition is the content, not an oversight.
  -- ================================================================

  Cover : TheoryTy ℓA s → Type (ℓ-max ℓX ℓA)
  Cover P = ⊤G ⊢ P

  Probe : TheoryTy ℓA s → Type (ℓ-max ℓX ℓA)
  Probe P = ⊤G ⊢ Dec⟨ P ⟩

  _⇛_ : TheoryTy ℓA s → TheoryTy ℓB s → Type (ℓ-max ℓX (ℓ-max ℓA ℓB))
  P ⇛ Q = P ⊢ Q

  infix 1 _⇛_

  -- ================================================================
  -- `with`, internally.
  --
  -- A view holds of every world, so it can be added to ANY derivation's
  -- context.  That is the whole trick, and it is one `&-I`.
  -- ================================================================

  withView : {B : TheoryTy ℓB s} {P : TheoryTy ℓA s}
           → Cover P → B ⊢ (B & P)
  withView v = &-I idg (v ∘g ⊤-I)

  -- ... and having added it, distribute and eliminate.  This composite
  -- is `with v | inl … | inr …`.
  viewCase : {B : TheoryTy ℓB s} {C : TheoryTy ℓC s}
             {P : TheoryTy ℓA s} {Q : TheoryTy ℓM s}
           → Cover (P ⊕ Q)
           → (B & P) ⊢ C → (B & Q) ⊢ C
           → B ⊢ C
  viewCase v f g = ⊕-E f g ∘g dist&r ∘g withView v

  -- the indexed form: `with v | (y , …)`
  viewCaseᴰ : {B : TheoryTy ℓB s} {C : TheoryTy ℓC s}
              (Y : Type ℓY) {P : Y → TheoryTy ℓA s}
            → Cover (⊕ᴰ Y P)
            → ((y : Y) → (B & P y) ⊢ C)
            → B ⊢ C
  viewCaseᴰ Y v f = ⊕ᴰ-E f ∘g ⊕ᴰ-&-in Y ∘g withView v

  -- ================================================================
  -- The degenerate case, named because it is the common one.
  --
  -- At `B = ⊤G` there is no payload to carry past the view, so the
  -- `with` collapses to composition.  Every coalgebra out of `⊤` in the
  -- instances is of this shape.
  -- ================================================================

  caseOf : {C : TheoryTy ℓC s} {P : TheoryTy ℓA s} {Q : TheoryTy ℓM s}
         → Cover (P ⊕ Q) → P ⊢ C → Q ⊢ C → Cover C
  caseOf v f g = ⊕-E f g ∘g v

  caseOfᴰ : {C : TheoryTy ℓC s} (Y : Type ℓY) {P : Y → TheoryTy ℓA s}
          → Cover (⊕ᴰ Y P) → ((y : Y) → P y ⊢ C) → Cover C
  caseOfᴰ Y v f = ⊕ᴰ-E f ∘g v

  -- refine a view along a view morphism
  refine : {P : TheoryTy ℓA s} {Q : TheoryTy ℓB s}
         → P ⇛ Q → Cover P → Cover Q
  refine f v = f ∘g v

  -- ================================================================
  -- Probes: partial views.  Coverage-checking IS decidability, so these
  -- are the `Decidable.Additive` combinators under their view names.
  -- ================================================================

  cover→probe : (P : TheoryTy ℓA s) → Cover P → Probe P
  cover→probe P v = dec-yes P ∘g v

  probe-⊕ : (P : TheoryTy ℓA s) (Q : TheoryTy ℓB s)
          → Probe P → Probe Q → Probe (P ⊕ Q)
  probe-⊕ P Q p q = dec-⊕ P Q ∘g &-I p q

  probe-& : (P : TheoryTy ℓA s) (Q : TheoryTy ℓB s)
          → Probe P → Probe Q → Probe (P & Q)
  probe-& P Q p q = dec-& P Q ∘g &-I p q

  -- a probe transports along a view ISOMORPHISM (both directions, since
  -- the refutation half is contravariant)
  probe-map : (P : TheoryTy ℓA s) (Q : TheoryTy ℓB s)
            → P ⇛ Q → Q ⇛ P → Probe P → Probe Q
  probe-map P Q f g p = dec-map P Q f g ∘g p

  -- forgetting the refutation: a probe seen as a partial view in
  -- `MaybeG` form.  This is the only sanctioned way to weaken a
  -- decision -- writing `inl`/`inr` by hand is not.
  probe→maybe : (P : TheoryTy ℓA s) → Probe P → Cover (MaybeG P)
  probe→maybe P p = ⊕-E just-I nothing-I ∘g p

  -- ================================================================
  -- OBSERVING a view.  Reading off "did it succeed?" is `⊕-E` into a
  -- CONSTANT grammar -- never a metalanguage match on `inl`/`inr`.
  -- Same move as `Lambda.Modes.Core.accepts`.  Test suites should go
  -- through these rather than defining their own `succeeded`/`isYes`.
  -- ================================================================

  probe→Bool : (P : TheoryTy ℓA s) → Probe P → Cover (λ _ → Bool)
  probe→Bool P p = ⊕-E (λ _ _ → true) (λ _ _ → false) ∘g p

  maybe→Bool : (P : TheoryTy ℓA s) → Cover (MaybeG P) → Cover (λ _ → Bool)
  maybe→Bool P v = MaybeG-E {A = P} (λ _ _ → true) (λ _ _ → false) v

  -- ================================================================
  -- Descending into a tensor.
  --
  -- Refining EVERY slot is free -- it is the tensor's own functorial
  -- action.  Refining ONE NAMED slot is not: picking slot `i` out of the
  -- arity is the `Discrete (σ .arities o)` obstruction that `Focus`'s
  -- `Rest` field exists to dodge.  So there is no `⇛-slot` here, and
  -- that absence is the honest state of affairs.
  -- ================================================================

  ⇛-slots : (o : σ .ops)
            {A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a)}
            {B : (a : σ .arities o) → TheoryTy ℓB (σ .sortOf o a)}
          → ((a : σ .arities o) → A a ⇛ B a)
          → ⊗ˢ o A ⇛ ⊗ˢ o B
  ⇛-slots o f = ⊗ˢ-map o f

  -- ================================================================
  -- Sanity: the payload-carrying forms really do subsume the
  -- degenerate ones, so `caseOf` is an abbreviation and not a
  -- separate rule.  Discharging the payload is `&-E₂`.
  -- ================================================================

  private
    _ : {C : TheoryTy ℓC s} {P : TheoryTy ℓA s} {Q : TheoryTy ℓM s}
      → Cover (P ⊕ Q) → P ⊢ C → Q ⊢ C → Cover C
    _ = λ v f g → viewCase v (f ∘g &-E₂) (g ∘g &-E₂)

    _ : {C : TheoryTy ℓC s} (Y : Type ℓY) {P : Y → TheoryTy ℓA s}
      → Cover (⊕ᴰ Y P) → ((y : Y) → P y ⊢ C) → Cover C
    _ = λ Y v f → viewCaseᴰ Y v (λ y → f y ∘g &-E₂)

    -- ... and the payload survives the analysis, which is the whole
    -- reason `withView` is not just `_∘g_`: both branches still have
    -- `B` in hand.  This is the shape `Lambda.ScopeCheck.dec-In` uses.
    _ : {B : TheoryTy ℓB s} {C : TheoryTy ℓC s} {P : TheoryTy ℓA s}
      → Cover P → (B & P) ⊢ C → B ⊢ C
    _ = λ v k → k ∘g withView v

-- ==================================================================
-- Programming BY a view.
--
-- A description `F` is a pattern with recursive holes, so a family of
-- views -- one per nonterminal -- is exactly a coalgebra out of ⊤.  The
-- recursion is then `hyloC`, and totality is discharged ONCE per view
-- (`Guarded F`) rather than once per program: `Quicksort`'s `qalg` and
-- `qalgV` are two right-hand sides against one such analysis.
-- ==================================================================

module Rec {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
           (GS : GradedSubstrate σ ℓX ℓP) (ℓA : Level)
           (X : Type ℓV) (xs : X → S) where

  open Guard GS ℓA X xs

  -- the terminal motive, at the level the descriptions live at
  ⊤ᴵ : Ix → Type ℓSh
  ⊤ᴵ _ = Unit*

  -- ONE VIEW PER NONTERMINAL.  This is the coalgebra, renamed.
  ViewsOf : ((x : X) → Functor (xs x)) → Type _
  ViewsOf F = CoalgC F ⊤ᴵ

  -- ... and a program is a view plus an algebra.  `byView` IS `hyloC`;
  -- naming it is what makes the discipline visible at the use site.
  byView : {F : (x : X) → Functor (xs x)} {B : Ix → Type ℓSh}
         → ((x : X) → Guarded (F x))
         → ViewsOf F → AlgC F B → ⊤ᴵ ⊢ᴵ B
  byView gF V alg = hyloC gF V alg

  -- NOTE.  `Bags.Quicksort.qcoalg` has motive `λ _ → Unit` rather than
  -- `⊤ᴵ`.  Any contractible motive works and `hyloC` is stated at an
  -- arbitrary one, so that instance needs no change to be a `ViewsOf`
  -- in substance -- only in spelling.
