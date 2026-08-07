{-
  THE DEGENERATE CASE, CHECKED.

  `Reindex.Base` generalises `CarrierMap` along a signature morphism.
  The generalisation is only worth having if it CHANGES NOTHING at the
  identity signature morphism -- not up to an isomorphism, not up to a
  coercion, but definitionally, so that every `refl` test written against
  the old notion still holds against the new one.  This file is that
  check, and the witness is the one fully worked pass in the development,
  `Instances/LinLam/Codegen`:

      layoutMap : Reindex linFib H.heapFib          the layout of
      layPres   : SplitPresAt at BOTH operations    linear contexts into
      layRefl   : ReflectsSplitAt at BOTH           a heap

  Four claims, in increasing strength:

    (1) `layPresOver` is built from `layPres` BY PROJECTION -- the two
        records have definitionally equal field types, so no coercion
        appears on either side of the translation.

    (2) both round trips of `presToOver`/`presFromOver` are `refl`.

    (3) `layReflOver = layRefl`, with nothing written on the right --
        `ReflectsSplitAtOver` at `φ = id` IS `Along.ReflectsSplitAt`, as
        `reflectsSame` states by `refl`.

    (4) Codegen's own `refl` test -- that the two premises of a
        two-variable application lay out to DISJOINT regions, with the
        `_#_` proof reducing to a nest of `tt` -- still holds when run
        through `SplitPresAtOver`, AND when run through the composite of
        the chain `layoutPass ◅ done`.  (4) is the one that would break
        if a `subst` had crept in: a coercion at a family over a variable
        world does not reduce, so the nest of `tt` would go stuck.

  The chain test is the real content of (4).  `composite` builds the
  composite `SigMor` as `idSigMor ⨟σ idSigMor`, whose `resEq` is
  `Eq.refl Eq.∙ Eq.ap _ Eq.refl`; that reduces to `Eq.refl`, hence
  `homAt` still reduces to `hom`, hence the test still evaluates.  Had
  `_⨟σ_` been stated with cubical paths instead of `Eq`, it would not.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Reindex.Sanity where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit
open import Cubical.Data.List using (List; []; _∷_)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.CarrierMap
open import TheoryGrammar.ChangeOfTheory using (SigMor)
open import TheoryGrammar.Reindex.Base
open import TheoryGrammar.Reindex.Pass

-- `Syntax` re-exports `Pass`/`idPass` (its own, unrelated notion: an
-- endo-term `TmG ⊢ TmG`).  Hidden, so the names here mean this file's.
open import TheoryGrammar.Instances.LinLam.Codegen
  hiding (Pass; idPass)
import TheoryGrammar.Instances.Heap.Graded as H

-- ==================================================================
-- (0) The two theories, bundled.
-- ==================================================================

linTheory : Theory ℓ-zero ℓ-zero ℓ-zero ℓ-zero ℓ-zero
linTheory = theory monoidSig linFib

heapTheory : Theory ℓ-zero ℓ-zero ℓ-zero ℓ-zero ℓ-zero
heapTheory = theory monoidSig H.heapFib

-- ==================================================================
-- (1) THE CARRIER MAP AND ITS PRESERVATION, AS THE φ = id INSTANCE.
--
-- Note there is nothing on the right-hand sides but projections.  If the
-- generalisation had needed a coercion, one would have to appear here.
-- ==================================================================

layoutOver : ReindexOver (idSigMor monoidSig) linFib H.heapFib
layoutOver = ofReindex layoutMap

layPresOver : (o : MonOp) → SplitPresAtOver layoutOver o
layPresOver o .homSplitO = layPres o .homSplit
layPresOver o .homPartsO = layPres o .homParts

-- ==================================================================
-- (2) ... and the translation is an isomorphism on the nose.
-- ==================================================================

_ : (o : MonOp) → presToOver layoutMap o (layPres o) ≡ layPresOver o
_ = λ o → refl

_ : (o : MonOp) → presFromOver layoutMap o (layPresOver o) ≡ layPres o
_ = λ o → refl

_ : (o : MonOp) (P : SplitPresAt layoutMap o)
  → presFromOver layoutMap o (presToOver layoutMap o P) ≡ P
_ = λ o P → refl

-- ==================================================================
-- (3) REFLECTION NEEDS NO TRANSLATION AT ALL: the two types are equal,
-- and `layRefl` inhabits the new one with nothing written.
-- ==================================================================

_ : (o : MonOp) → ReflectsSplitAtOver layoutOver o ≡ Along.ReflectsSplitAt layoutMap o
_ = λ o → refl

layReflOver : (o : MonOp) → ReflectsSplitAtOver layoutOver o
layReflOver = layRefl

-- the slot section is free at `φ = id`: `onAr` is the identity
laySection : (o : MonOp) → ArSection (idSigMor monoidSig) o
laySection = idArSection monoidSig

-- ==================================================================
-- THE PASS, AND ITS REFLECTIVITY.
-- ==================================================================

layoutPass : Pass linTheory heapTheory
layoutPass .sigOf  = idSigMor monoidSig
layoutPass .mapOf  = layoutOver
layoutPass .presOf = layPresOver

layoutReflective : Reflective layoutPass
layoutReflective .reflectsAt = layReflOver
layoutReflective .secOf      = laySection

-- a one-link chain, and its composite
layoutChain : Chain linTheory heapTheory
layoutChain = layoutPass ◅ done

layoutChainReflective : Reflective (composite layoutChain)
layoutChainReflective = chainReflective layoutChain (layoutReflective , tt*)

-- ==================================================================
-- (4) THE COMPUTATION TEST.  `Codegen`'s own `refl` line, run through
-- the generalisation and then through the CHAIN.  Both still reduce, and
-- the last component -- the `_#_` proof that the two emitted regions do
-- not alias -- is still a nest of `tt`.
-- ==================================================================

private
  twoU : Usage
  twoU = true ∷ true ∷ []

  twoSp : linFib .Split appop twoU
  twoSp = true ∷ false ∷ [] , false ∷ true ∷ [] , twoSplit

_ : layPresOver appop .homSplitO twoU twoSp
  ≡ ( H.single 0 H.v1
    , H.single 1 H.v1
    , H.left (H.right H.nil)
    , ((tt , tt) , tt) )
_ = refl

_ : composite layoutChain .presOf appop .homSplitO twoU twoSp
  ≡ ( H.single 0 H.v1
    , H.single 1 H.v1
    , H.left (H.right H.nil)
    , ((tt , tt) , tt) )
_ = refl

-- ... and the back-projection still inverts it, THROUGH THE CHAIN.
_ : composite layoutChain .mapOf .homO tt twoU
  ≡ (0 , H.v1) ∷ (1 , H.v1) ∷ []
_ = refl

_ : layoutChainReflective .reflectsAt appop twoU
      ( H.single 0 H.v1 , H.single 1 H.v1
      , H.left (H.right H.nil) , ((tt , tt) , tt) ) .fst
  ≡ (true ∷ false ∷ [] , false ∷ true ∷ [] , twoSplit)
_ = refl

-- ==================================================================
-- (5) THE PHASE-2 INTERFACE.  `Codegen`'s strong monoidality of the
-- layout -- `Lay B ⊛ Lay C ⊣⊢ Lay (B ∗ C)` -- rebuilt out of `push⊗O`
-- and `pull⊗O` instead of `push⊗`/`pull⊗`.  Both TYPES are unchanged,
-- which is the claim: the generic connective interface reproduces the
-- worked pass.  The `⊗ˢ-map` that `Codegen` composes on the outside is
-- absorbed into `push⊗O`'s `tr` argument, which is the only shape change
-- the signature-generic version forces (with `onAr` neither injective
-- nor surjective in general there is no canonical source slot family, so
-- the translation of payloads has to be supplied).
--
-- WHAT IS NOT `refl`, and why -- worth recording, because it is the
-- codebase's standing trap and not a defect of this generalisation.
-- `lay∗Over B C ≡ lay∗ B C` does NOT hold definitionally.  Both sides
-- coerce the payload along `homParts`, but through two nominally
-- distinct helpers (`Along.coeTy` and `AlongOver.coeTyT`), and the
-- equation they consume is `boolΠ Eq.refl Eq.refl a`, which is STUCK at
-- a variable arity `a`.  Neither helper reduces, so the two terms differ
-- as terms while agreeing at `a = true` and at `a = false`.  This is
-- exactly "arities have no η", and it is the same fact that forces
-- `respellIn`/`respellOut` to exist at all.
-- ==================================================================

module AO = AlongOver layoutOver

lay∗Over : (B C : H.Gr) → (Lay B ⊛ Lay C) ⊢ Lay (B H.∗ C)
lay∗Over B C =
  AO.push⊗O appop (layPresOver appop)
    (boolΠ {M = λ _ → Ctx} (Lay B) (Lay C))
    (H.boolΠ {M = λ _ → H.Gr} B C)
    (respellIn B C)

lay∗⁻Over : (B C : H.Gr) → Lay (B H.∗ C) ⊢ (Lay B ⊛ Lay C)
lay∗⁻Over B C =
  AO.pull⊗O appop (layReflOver appop) (laySection appop)
    (boolΠ {M = λ _ → Ctx} (Lay B) (Lay C))
    (H.boolΠ {M = λ _ → H.Gr} B C)
    (respellOut B C)

-- ... but the TYPES are literally `Codegen`'s, which is checkable:
_ : (B C : H.Gr) → ((Lay B ⊛ Lay C) ⊢ Lay (B H.∗ C))
_ = lay∗Over

_ : (B C : H.Gr) → (Lay (B H.∗ C) ⊢ (Lay B ⊛ Lay C))
_ = lay∗⁻Over

-- and the frame rule transports through the generic interface exactly as
-- `Codegen.layFrame` does through the single-signature one
layFrameOver : {B B' : H.Gr} (C : H.Gr) → B H.⊢ B'
             → (Lay B ⊛ Lay C) ⊢ (Lay B' ⊛ Lay C)
layFrameOver {B} {B'} C f =
  lay∗⁻Over B' C ∘g AO.pullTermO (H.frame C f) ∘g lay∗Over B C
