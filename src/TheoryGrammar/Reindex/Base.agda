{-
  REINDEXING ALONG A MAP OF SIGNATURES.

  `CarrierMap.Reindex` relates two promodels over ONE signature.  That is
  enough for a pass that rewrites terms of a fixed theory, and it is not
  enough for a COMPILER, because a compiler's phases do not share a
  theory: the AST theory `λSig` has three operations with sorted slots,
  the resource theory `monoidSig` has a unit and a binary join, and a
  linearity checker is precisely a map from the first to the second.
  `LinLam/Check.agda` records the consequence in its header --

      "`CarrierMap.Reindex` relates two promodels over ONE signature, so
       there is NO `Reindex` between the de Bruijn theory and the
       linear-context theory, and the bridge cannot be a map of
       promodels at all."

  This file supplies the missing notion.  Nothing here is new
  mathematics; the whole content is BOOKKEEPING DONE IN THE Eq-WORLD, so
  that at the identity signature morphism every definition below reduces
  to the one it generalises, ON THE NOSE.  That is the design constraint
  and it is checked in `Reindex.Sanity`.

  --------------------------------------------------------------------
  THE SHAPE.  `ChangeOfTheory.SigMor σ τ` already has the four
  components a signature morphism needs:

      onSort : S → S'
      onOp   : σ .ops → τ .ops
      onAr   : (o) → τ .arities (onOp o) → σ .arities o     CONTRAVARIANT
      resEq, sortEq                                    Eq-world coherence

  `onAr` points BACKWARDS: a τ-slot of the translated operation names a
  σ-slot of the original.  That is forced by variance -- to build a
  τ-tuple out of a σ-tuple one must know, for each τ-slot, which σ-slot
  fills it -- and it is what makes the notions below asymmetric in a way
  the single-signature versions could not see:

      PRESERVATION quantifies over TARGET slots, and needs nothing of
      `onAr` beyond its existence;

      REFLECTION also quantifies over target slots, but reconstructing a
      SOURCE tensor from a target one additionally needs every source
      slot to be HIT (`ArSection` below).  A pass that drops a slot can
      still preserve; it cannot reflect a tensor.

  --------------------------------------------------------------------
  WHY THE COERCIONS ARE ON THE `hom` SIDE.

  `resEq o : τ .resultSort (onOp o) Eq.≡ onSort (σ .resultSort o)` says
  the two ways of naming the output sort agree.  Given `m` in the source,
  `hom m` lives at `onSort (σ .resultSort o)` while `Fib' .Split (onOp o)`
  wants a point at `τ .resultSort (onOp o)`.  One of the two must move.

  We move the HOM, not the splitting:

      homAt   o   m = coeIx (Eq.sym (resEq  o))   (hom _ m)
      homSlot o b x = coeIx (Eq.sym (sortEq o b)) (hom _ x)

  and then `SplitPresAtOver` and `ReflectsSplitAtOver` are stated with no
  further coercion anywhere.  The alternative -- coercing the SPLITTING
  or the PARTS -- would put a `coe` under `Fib' .Split`, i.e. under a
  family the instances define by pattern matching, and every downstream
  `refl` test would go inert.  Here the coercion sits on a carrier
  element, outside every family, and at `φ = id` both `resEq` and
  `sortEq` are `Eq.refl`, `Eq.sym Eq.refl` reduces to `Eq.refl`, and
  `coeIx C Eq.refl` reduces to the identity.  So

      homAt o m  ≡  hom _ m        DEFINITIONALLY, at φ = id

  and `SplitPresAtOver` becomes `SplitPresAt` field for field.

  --------------------------------------------------------------------
  COMPOSITION.  A chain of passes needs `SigMor` to compose, `ReindexOver`
  to compose over it, and both `SplitPresAtOver` and
  `ReflectsSplitAtOver` to compose.  All four are below.  The composite's
  coherence equations are

      resEq  = ψ.resEq  ∙ ap ψ.onSort φ.resEq
      sortEq = ψ.sortEq ∙ ap ψ.onSort φ.sortEq

  and the ONE lemma that makes the composition of preservation go through
  is `key`: the carrier map of the second pass commutes with a coercion
  of its argument, at the cost of `ap` on the sort translation.  It is
  proved by matching two `Eq.refl`s, which is possible only because both
  equations are stated with a VARIABLE endpoint -- the reason `SigMor`
  uses `Eq.≡` and not `_≡_`.

  Everything in this file is phase 1: it is the construction of an
  abstraction barrier, so it matches `Eq.refl`, projects records, and
  builds them by copattern.  `AlongOver` is the interface phase 2 sees.

  --------------------------------------------------------------------
  A DIFFERENT `Reindex`, NOT TO BE CONFUSED WITH THIS ONE.

  cubical-categorical-logic's `Multicategory/Reindex.agda` (branch
  `multicategory-cartesian`) also reindexes, and it is the OTHER
  variance.  There:

      given F : Multifunctor M N and a DISPLAYED cartesian multicategory
      Nᴰ over N, `reindexᴰ` pulls Nᴰ back to a displayed multicategory
      over M.

  That is a pullback of a structure ALONG a map -- the analogue in this
  development is `ChangeOfTheory.restrict`, which pulls a τ-model back to
  a σ-model along φ.  It is contravariant, it moves no carrier element,
  and it has nothing to say about splittings.

  What is here is covariant and is not a pullback: `ReindexOver` is a MAP
  OF PROMODELS lying over φ, i.e. a compiler pass, and its content is
  precisely what `reindexᴰ` never asks -- whether decompositions travel
  (`SplitPresAtOver`) and whether they travel back (`ReflectsSplitAtOver`).

  Their `Multicategory/Total.agda` uses "splitting" for a third thing
  again: a section of the projection out of a total multicategory, in the
  initiality-based eliminator.  That is not `Fibered.Split`, which is a
  decomposition of a carrier element.  Three notions, one word; the
  distinction is worth keeping.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Reindex.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.CarrierMap
open import TheoryGrammar.ChangeOfTheory
  using (SigMor; onSort; onOp; onAr; resEq; sortEq)

private variable
  ℓS ℓS' ℓS'' ℓ ℓ' ℓ2 ℓ2' ℓ3 ℓ3' : Level
  ℓX ℓX' ℓX'' ℓP ℓP' ℓP'' ℓA ℓB ℓV : Level

-- ==================================================================
-- The one coercion primitive.  Generic in the family, so that the SAME
-- lemma serves the result sort and the slot sorts.
-- ==================================================================

coeIx : {ℓI ℓC : Level} {I : Type ℓI} (C : I → Type ℓC) {s t : I}
      → s Eq.≡ t → C s → C t
coeIx C Eq.refl x = x                                    -- PRIMITIVE

-- ==================================================================
-- SIGNATURE MORPHISMS FORM A CATEGORY.
-- ==================================================================

idSigMor : {S : Type ℓS} (σ : SortedSig S ℓ ℓ') → SigMor σ σ
idSigMor σ .onSort s   = s
idSigMor σ .onOp   o   = o
idSigMor σ .onAr   o a = a
idSigMor σ .resEq  o   = Eq.refl
idSigMor σ .sortEq o b = Eq.refl

infixl 8 _⨟σ_

_⨟σ_ : {S : Type ℓS} {S' : Type ℓS'} {S'' : Type ℓS''}
       {σ : SortedSig S ℓ ℓ'} {τ : SortedSig S' ℓ2 ℓ2'}
       {υ : SortedSig S'' ℓ3 ℓ3'}
     → SigMor σ τ → SigMor τ υ → SigMor σ υ
(φ ⨟σ ψ) .onSort s = ψ .onSort (φ .onSort s)
(φ ⨟σ ψ) .onOp   o = ψ .onOp (φ .onOp o)
(φ ⨟σ ψ) .onAr   o c = φ .onAr o (ψ .onAr (φ .onOp o) c)
(φ ⨟σ ψ) .resEq  o =
  ψ .resEq (φ .onOp o) Eq.∙ Eq.ap (ψ .onSort) (φ .resEq o)
(φ ⨟σ ψ) .sortEq o c =
    ψ .sortEq (φ .onOp o) c
  Eq.∙ Eq.ap (ψ .onSort) (φ .sortEq o (ψ .onAr (φ .onOp o) c))

-- ==================================================================
-- A REINDEXING OVER A SIGNATURE MORPHISM.
--
-- `Reindex` with the sort map twisted by `φ .onSort`, and -- exactly as
-- there -- NO law.  The whole additive fragment is already available
-- (`AlongOver` below); every law is `SplitPresAtOver`, per-operation.
-- ==================================================================

record ReindexOver {S : Type ℓS} {S' : Type ℓS'}
                   {σ : SortedSig S ℓ ℓ'} {τ : SortedSig S' ℓ2 ℓ2'}
                   (φ : SigMor σ τ)
                   (Fib : Fibered σ ℓX ℓP) (Fib' : Fibered τ ℓX' ℓP')
                 : Type (ℓ-max ℓS (ℓ-max ℓX ℓX')) where
  field
    homO : (s : S) → Fib .carrier s → Fib' .carrier (φ .onSort s)

open ReindexOver public

-- the single-signature case, recovered
ofReindex : {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
            {Fib : Fibered σ ℓX ℓP} {Fib' : Fibered σ ℓX' ℓP'}
          → Reindex Fib Fib' → ReindexOver (idSigMor σ) Fib Fib'
ofReindex h .homO = h .hom

toReindex : {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
            {Fib : Fibered σ ℓX ℓP} {Fib' : Fibered σ ℓX' ℓP'}
          → ReindexOver (idSigMor σ) Fib Fib' → Reindex Fib Fib'
toReindex h .hom = h .homO

idReindexOver : {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (Fib : Fibered σ ℓX ℓP)
              → ReindexOver (idSigMor σ) Fib Fib
idReindexOver Fib .homO s x = x

module _ {S : Type ℓS} {S' : Type ℓS'} {S'' : Type ℓS''}
         {σ : SortedSig S ℓ ℓ'} {τ : SortedSig S' ℓ2 ℓ2'}
         {υ : SortedSig S'' ℓ3 ℓ3'}
         {φ : SigMor σ τ} {ψ : SigMor τ υ}
         {Fib : Fibered σ ℓX ℓP} {Fib₁ : Fibered τ ℓX' ℓP'}
         {Fib₂ : Fibered υ ℓX'' ℓP''} where

  infixl 8 _⨟r_

  _⨟r_ : ReindexOver φ Fib Fib₁ → ReindexOver ψ Fib₁ Fib₂
       → ReindexOver (φ ⨟σ ψ) Fib Fib₂
  (h ⨟r k) .homO s x = k .homO (φ .onSort s) (h .homO s x)

-- ==================================================================
-- THE TWO TRANSLATED CARRIER MAPS.  Everything below is stated with
-- these and with no other coercion.  At `φ = id` both reduce to
-- `h .homO _`, which is why the specialisation is definitional.
-- ==================================================================

module _ {S : Type ℓS} {S' : Type ℓS'}
         {σ : SortedSig S ℓ ℓ'} {τ : SortedSig S' ℓ2 ℓ2'}
         {φ : SigMor σ τ}
         {Fib : Fibered σ ℓX ℓP} {Fib' : Fibered τ ℓX' ℓP'}
         (h : ReindexOver φ Fib Fib') where

  homAtOf : (o : σ .ops) → Fib .carrier (σ .resultSort o)
          → Fib' .carrier (τ .resultSort (φ .onOp o))
  homAtOf o m = coeIx (Fib' .carrier) (Eq.sym (φ .resEq o)) (h .homO _ m)

  homSlotOf : (o : σ .ops) (b : τ .arities (φ .onOp o))
            → Fib .carrier (σ .sortOf o (φ .onAr o b))
            → Fib' .carrier (τ .sortOf (φ .onOp o) b)
  homSlotOf o b x = coeIx (Fib' .carrier) (Eq.sym (φ .sortEq o b)) (h .homO _ x)

-- ==================================================================
-- SPLIT PRESERVATION, OVER φ.
--
-- Read the two fields against `CarrierMap.SplitPresAt`:  the splitting
-- transported lands at the operation `φ .onOp o` and at the point
-- `homAt o m`; the parts are indexed by TARGET slots `b`, and the
-- source part consulted is the one `onAr` names.  There is no coercion
-- in either field -- both were absorbed into `homAt`/`homSlot`.
-- ==================================================================

record SplitPresAtOver {S : Type ℓS} {S' : Type ℓS'}
                       {σ : SortedSig S ℓ ℓ'} {τ : SortedSig S' ℓ2 ℓ2'}
                       {φ : SigMor σ τ}
                       {Fib : Fibered σ ℓX ℓP} {Fib' : Fibered τ ℓX' ℓP'}
                       (h : ReindexOver φ Fib Fib') (o : σ .ops)
  : Type (ℓ-max ℓ2' (ℓ-max ℓX (ℓ-max ℓX' (ℓ-max ℓP ℓP')))) where
  field
    homSplitO : (m : Fib .carrier (σ .resultSort o))
              → Fib .Split o m → Fib' .Split (φ .onOp o) (homAtOf h o m)
    homPartsO : (m : Fib .carrier (σ .resultSort o)) (sp : Fib .Split o m)
                (b : τ .arities (φ .onOp o))
              → Fib' .parts (φ .onOp o) (homAtOf h o m) (homSplitO m sp) b
                Eq.≡ homSlotOf h o b (Fib .parts o m sp (φ .onAr o b))

open SplitPresAtOver public

-- ==================================================================
-- SPLIT REFLECTION, OVER φ -- THE BACK-PROJECTION.
--
-- This is what makes a chain of passes usable in reverse: given a
-- decomposition of the COMPILED object, produce the decomposition of the
-- SOURCE object it came from, together with the evidence that its parts
-- compile to the given ones.  It is the discrete Conduche condition of
-- `ChangeOfTheory`, now allowed to cross a signature.
--
-- Note it is a plain Σ-type, not a record.  That is deliberate: at
-- `φ = id` the type is then DEFINITIONALLY `Along.ReflectsSplitAt`, and
-- `Reindex.Sanity` states that as a `refl`.
-- ==================================================================

ReflectsSplitAtOver :
  {S : Type ℓS} {S' : Type ℓS'}
  {σ : SortedSig S ℓ ℓ'} {τ : SortedSig S' ℓ2 ℓ2'}
  {φ : SigMor σ τ}
  {Fib : Fibered σ ℓX ℓP} {Fib' : Fibered τ ℓX' ℓP'}
  (h : ReindexOver φ Fib Fib') (o : σ .ops)
  → Type (ℓ-max ℓ2' (ℓ-max ℓX (ℓ-max ℓX' (ℓ-max ℓP ℓP'))))
ReflectsSplitAtOver {σ = σ} {τ} {φ} {Fib} {Fib'} h o =
  (m : Fib .carrier (σ .resultSort o))
  (sp' : Fib' .Split (φ .onOp o) (homAtOf h o m))
  → Σ[ sp ∈ Fib .Split o m ]
      ((b : τ .arities (φ .onOp o))
       → Fib' .parts (φ .onOp o) (homAtOf h o m) sp' b
         Eq.≡ homSlotOf h o b (Fib .parts o m sp (φ .onAr o b)))

-- ==================================================================
-- PRESERVATION AT A POINT.
--
-- `SplitPresAtOver` is a Π of a record; `PresAt` is its fibre.  The two
-- are interderivable by the Π/Σ shuffle below (both round trips `refl`),
-- and the pointwise form is what an INSTANCE decides: `LinLam.presApp?`
-- decides `PresAt` at each application, and the global `SplitPresAtOver`
-- is exactly what fails for a non-linear term.
-- ==================================================================

PresAt : {S : Type ℓS} {S' : Type ℓS'}
         {σ : SortedSig S ℓ ℓ'} {τ : SortedSig S' ℓ2 ℓ2'}
         {φ : SigMor σ τ}
         {Fib : Fibered σ ℓX ℓP} {Fib' : Fibered τ ℓX' ℓP'}
         (h : ReindexOver φ Fib Fib') (o : σ .ops)
         (m : Fib .carrier (σ .resultSort o))
       → Type (ℓ-max ℓ2' (ℓ-max ℓX' (ℓ-max ℓP ℓP')))
PresAt {σ = σ} {τ} {φ} {Fib} {Fib'} h o m =
  (sp : Fib .Split o m)
  → Σ[ sp' ∈ Fib' .Split (φ .onOp o) (homAtOf h o m) ]
      ((b : τ .arities (φ .onOp o))
       → Fib' .parts (φ .onOp o) (homAtOf h o m) sp' b
         Eq.≡ homSlotOf h o b (Fib .parts o m sp (φ .onAr o b)))

module _ {S : Type ℓS} {S' : Type ℓS'}
         {σ : SortedSig S ℓ ℓ'} {τ : SortedSig S' ℓ2 ℓ2'}
         {φ : SigMor σ τ}
         {Fib : Fibered σ ℓX ℓP} {Fib' : Fibered τ ℓX' ℓP'}
         (h : ReindexOver φ Fib Fib') (o : σ .ops) where

  toPres : ((m : Fib .carrier (σ .resultSort o)) → PresAt h o m)
         → SplitPresAtOver h o
  toPres f .homSplitO m sp   = f m sp .fst
  toPres f .homPartsO m sp b = f m sp .snd b

  fromPres : SplitPresAtOver h o
           → (m : Fib .carrier (σ .resultSort o)) → PresAt h o m
  fromPres P m sp = P .homSplitO m sp , P .homPartsO m sp

  presRound : (P : SplitPresAtOver h o) → toPres (fromPres P) ≡ P
  presRound P = refl

  presRound' : (f : (m : Fib .carrier (σ .resultSort o)) → PresAt h o m)
             → fromPres (toPres f) ≡ f
  presRound' f = refl

-- ==================================================================
-- THE IDENTITY PASS preserves and reflects every splitting, with no
-- content: the transported splitting IS the splitting.
-- ==================================================================

module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (Fib : Fibered σ ℓX ℓP) where

  idPres : (o : σ .ops) → SplitPresAtOver (idReindexOver Fib) o
  idPres o .homSplitO m sp   = sp
  idPres o .homPartsO m sp a = Eq.refl

  idReflects : (o : σ .ops) → ReflectsSplitAtOver (idReindexOver Fib) o
  idReflects o m sp' = sp' , λ a → Eq.refl

-- ==================================================================
-- COMPOSITION.  The spine.
-- ==================================================================

module Comp {S : Type ℓS} {S' : Type ℓS'} {S'' : Type ℓS''}
            {σ : SortedSig S ℓ ℓ'} {τ : SortedSig S' ℓ2 ℓ2'}
            {υ : SortedSig S'' ℓ3 ℓ3'}
            {φ : SigMor σ τ} {ψ : SigMor τ υ}
            {Fib : Fibered σ ℓX ℓP} {Fib₁ : Fibered τ ℓX' ℓP'}
            {Fib₂ : Fibered υ ℓX'' ℓP''}
            (h : ReindexOver φ Fib Fib₁) (k : ReindexOver ψ Fib₁ Fib₂) where

  -- THE LEMMA.  `k`'s carrier map commutes with a coercion of its
  -- argument, at the price of `ap` on the sort translation -- which is
  -- exactly the shape the composite's `resEq`/`sortEq` have.  Both
  -- equations are between VARIABLE endpoints, so both `Eq.refl` matches
  -- are legal; that is the whole reason `SigMor` is stated in `Eq`.
  private
    key : {s₁ s₂ : S'} (e : s₁ Eq.≡ s₂) {t : S''} (f : t Eq.≡ ψ .onSort s₁)
          (x : Fib₁ .carrier s₂)
        → coeIx (Fib₂ .carrier) (Eq.sym (f Eq.∙ Eq.ap (ψ .onSort) e))
                (k .homO s₂ x)
          Eq.≡ coeIx (Fib₂ .carrier) (Eq.sym f)
                (k .homO s₁ (coeIx (Fib₁ .carrier) (Eq.sym e) x))
    key Eq.refl Eq.refl x = Eq.refl

  compAt : (o : σ .ops) (m : Fib .carrier (σ .resultSort o))
         → homAtOf (h ⨟r k) o m Eq.≡ homAtOf k (φ .onOp o) (homAtOf h o m)
  compAt o m = key (φ .resEq o) (ψ .resEq (φ .onOp o)) (h .homO _ m)

  compSlot : (o : σ .ops) (c : υ .arities (ψ .onOp (φ .onOp o)))
             (x : Fib .carrier (σ .sortOf o ((φ ⨟σ ψ) .onAr o c)))
           → homSlotOf (h ⨟r k) o c x
             Eq.≡ homSlotOf k (φ .onOp o) c
                    (homSlotOf h o (ψ .onAr (φ .onOp o) c) x)
  compSlot o c x =
    key (φ .sortEq o (ψ .onAr (φ .onOp o) c)) (ψ .sortEq (φ .onOp o) c)
        (h .homO _ x)

  private
    coeSp : {o₂ : υ .ops} {x y : Fib₂ .carrier (υ .resultSort o₂)}
          → x Eq.≡ y → Fib₂ .Split o₂ x → Fib₂ .Split o₂ y
    coeSp Eq.refl s = s

    coePt : {o₂ : υ .ops} {x y : Fib₂ .carrier (υ .resultSort o₂)}
            (e : x Eq.≡ y) (sp : Fib₂ .Split o₂ x) (c : υ .arities o₂)
          → Fib₂ .parts o₂ y (coeSp e sp) c Eq.≡ Fib₂ .parts o₂ x sp c
    coePt Eq.refl sp c = Eq.refl

  -- PRESERVATION COMPOSES.
  presComp : (o : σ .ops)
           → SplitPresAtOver h o → SplitPresAtOver k (φ .onOp o)
           → SplitPresAtOver (h ⨟r k) o
  presComp o P Q .homSplitO m sp =
    coeSp (Eq.sym (compAt o m))
          (Q .homSplitO (homAtOf h o m) (P .homSplitO m sp))
  presComp o P Q .homPartsO m sp c =
      coePt (Eq.sym (compAt o m))
            (Q .homSplitO (homAtOf h o m) (P .homSplitO m sp)) c
    Eq.∙ (Q .homPartsO (homAtOf h o m) (P .homSplitO m sp) c
    Eq.∙ (Eq.ap (homSlotOf k (φ .onOp o) c)
                (P .homPartsO m sp (ψ .onAr (φ .onOp o) c))
    Eq.∙ Eq.sym (compSlot o c (Fib .parts o m sp ((φ ⨟σ ψ) .onAr o c)))))

  -- ... AND SO DOES REFLECTION.  This is the fact that decides whether
  -- "keep enough data to project back to earlier passes" survives a
  -- whole chain or only one link: it does, and the proof is the same
  -- three-step chain run backwards.
  reflComp : (o : σ .ops)
           → ReflectsSplitAtOver h o → ReflectsSplitAtOver k (φ .onOp o)
           → ReflectsSplitAtOver (h ⨟r k) o
  reflComp o R S m sp' =
      R m (S (homAtOf h o m) (coeSp (compAt o m) sp') .fst) .fst
    , λ c →
        Eq.sym (coePt (compAt o m) sp' c)
      Eq.∙ (S (homAtOf h o m) (coeSp (compAt o m) sp') .snd c
      Eq.∙ (Eq.ap (homSlotOf k (φ .onOp o) c)
                  (R m (S (homAtOf h o m) (coeSp (compAt o m) sp') .fst)
                     .snd (ψ .onAr (φ .onOp o) c))
      Eq.∙ Eq.sym (compSlot o c
             (Fib .parts o m
                (R m (S (homAtOf h o m) (coeSp (compAt o m) sp') .fst) .fst)
                ((φ ⨟σ ψ) .onAr o c)))))

open Comp public using (compAt; compSlot; presComp; reflComp)

-- ==================================================================
-- THE SINGLE-SIGNATURE NOTIONS ARE THE φ = id CASE, FIELD FOR FIELD.
--
-- No coercion appears in either translation, and both round trips are
-- `refl` -- which is the statement that the generalisation did not
-- change the definition, only its indexing.  `reflectsSame` is stronger
-- still: the two REFLECTION types are literally equal.
-- ==================================================================

module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
         {Fib : Fibered σ ℓX ℓP} {Fib' : Fibered σ ℓX' ℓP'}
         (h : Reindex Fib Fib') (o : σ .ops) where

  presToOver : SplitPresAt h o → SplitPresAtOver (ofReindex h) o
  presToOver P .homSplitO = P .homSplit
  presToOver P .homPartsO = P .homParts

  presFromOver : SplitPresAtOver (ofReindex h) o → SplitPresAt h o
  presFromOver P .homSplit = P .homSplitO
  presFromOver P .homParts = P .homPartsO

  presOverRound : (P : SplitPresAt h o) → presFromOver (presToOver P) ≡ P
  presOverRound P = refl

  presOverRound' : (P : SplitPresAtOver (ofReindex h) o)
                 → presToOver (presFromOver P) ≡ P
  presOverRound' P = refl

  -- reflection needs no translation at all
  reflectsSame : ReflectsSplitAtOver (ofReindex h) o
               ≡ Along.ReflectsSplitAt h o
  reflectsSame = refl

-- ==================================================================
-- THE ONE GENUINELY NEW OBLIGATION A CHANGE OF SIGNATURE INTRODUCES.
--
-- `onAr` points backwards, so a τ-slot names a σ-slot.  Building a
-- SOURCE tensor out of a target one therefore needs every source slot to
-- be named -- otherwise the source tensor has a payload the target does
-- not carry, and no amount of reflection can invent it.  `ArSection` is
-- that condition, it is invisible at `φ = id` (where it is inhabited by
-- `Eq.refl`), and it composes.
-- ==================================================================

ArSection : {S : Type ℓS} {S' : Type ℓS'}
            {σ : SortedSig S ℓ ℓ'} {τ : SortedSig S' ℓ2 ℓ2'}
            (φ : SigMor σ τ) (o : σ .ops) → Type (ℓ-max ℓ' ℓ2')
ArSection {σ = σ} {τ} φ o =
  (a : σ .arities o) → Σ[ b ∈ τ .arities (φ .onOp o) ] (φ .onAr o b Eq.≡ a)

idArSection : {S : Type ℓS} (σ : SortedSig S ℓ ℓ') (o : σ .ops)
            → ArSection (idSigMor σ) o
idArSection σ o a = a , Eq.refl

compArSection : {S : Type ℓS} {S' : Type ℓS'} {S'' : Type ℓS''}
                {σ : SortedSig S ℓ ℓ'} {τ : SortedSig S' ℓ2 ℓ2'}
                {υ : SortedSig S'' ℓ3 ℓ3'}
                (φ : SigMor σ τ) (ψ : SigMor τ υ) (o : σ .ops)
              → ArSection φ o → ArSection ψ (φ .onOp o)
              → ArSection (φ ⨟σ ψ) o
compArSection φ ψ o s t a =
  t (s a .fst) .fst
  , (Eq.ap (φ .onAr o) (t (s a .fst) .snd) Eq.∙ s a .snd)

-- ==================================================================
-- THE CONNECTIVES.  What phase 2 sees.
-- ==================================================================

module AlongOver {S : Type ℓS} {S' : Type ℓS'}
                 {σ : SortedSig S ℓ ℓ'} {τ : SortedSig S' ℓ2 ℓ2'}
                 {φ : SigMor σ τ}
                 {Fib : Fibered σ ℓX ℓP} {Fib' : Fibered τ ℓX' ℓP'}
                 (h : ReindexOver φ Fib Fib') where

  open FibNotation Fib
  module T = FibNotation Fib'

  -- a grammar over the TARGET theory, reindexed to one over the source
  pullO : {s : S} → T.TheoryTy ℓA (φ .onSort s) → TheoryTy ℓA s
  pullO {s = s} B m = B (h .homO s m)

  -- every derivation reinterprets, with no cost and no hypothesis.  This
  -- is `ChangeOfTheory.reinterpretTerm` and `Along.pullTerm` at once:
  -- crossing a signature costs the multiplicatives something, and costs
  -- the additives NOTHING.
  pullTermO : {s : S} {A : T.TheoryTy ℓA (φ .onSort s)}
              {B : T.TheoryTy ℓB (φ .onSort s)}
            → A T.⊢ B → pullO A ⊢ pullO B
  pullTermO f m x = f _ x

  pullO-⊤ : {s : S} → pullO (T.⊤G {φ .onSort s}) ≡ ⊤G {s}
  pullO-⊤ = refl

  pullO-⊥ : {s : S} → pullO (T.⊥G {φ .onSort s}) ≡ ⊥G {s}
  pullO-⊥ = refl

  pullO-& : {s : S} (A : T.TheoryTy ℓA (φ .onSort s))
            (B : T.TheoryTy ℓB (φ .onSort s))
          → pullO (A T.& B) ≡ (pullO {s = s} A & pullO B)
  pullO-& _ _ = refl

  pullO-⊕ : {s : S} (A : T.TheoryTy ℓA (φ .onSort s))
            (B : T.TheoryTy ℓB (φ .onSort s))
          → pullO (A T.⊕ B) ≡ (pullO {s = s} A ⊕ pullO B)
  pullO-⊕ _ _ = refl

  pullO-⇒ : {s : S} (A : T.TheoryTy ℓA (φ .onSort s))
            (B : T.TheoryTy ℓB (φ .onSort s))
          → pullO (A T.⇒ B) ≡ (pullO {s = s} A ⇒ pullO B)
  pullO-⇒ _ _ = refl

  pullO-⊕ᴰ : {s : S} (Y : Type ℓV) (A : Y → T.TheoryTy ℓA (φ .onSort s))
           → pullO (T.⊕ᴰ Y A) ≡ ⊕ᴰ {s = s} Y (λ y → pullO (A y))
  pullO-⊕ᴰ _ _ = refl

  pullO-&ᴰ : {s : S} (Y : Type ℓV) (A : Y → T.TheoryTy ℓA (φ .onSort s))
           → pullO (T.&ᴰ Y A) ≡ &ᴰ {s = s} Y (λ y → pullO (A y))
  pullO-&ᴰ _ _ = refl

  -- ================================================================
  -- The multiplicative fragment.  Two reindexings are needed and they
  -- are DIFFERENT, which is the honest cost of crossing a signature:
  -- the RESULT is reindexed along `homAt o`, each SLOT along
  -- `homSlot o b` -- and the slots are indexed by TARGET arities, so a
  -- source slot outside the image of `onAr` is simply not addressed.
  -- ================================================================

  pullResO : (o : σ .ops) → T.TheoryTy ℓA (τ .resultSort (φ .onOp o))
           → TheoryTy ℓA (σ .resultSort o)
  pullResO o C m = C (homAtOf h o m)

  pullSlotO : (o : σ .ops) (b : τ .arities (φ .onOp o))
            → T.TheoryTy ℓA (τ .sortOf (φ .onOp o) b)
            → TheoryTy ℓA (σ .sortOf o (φ .onAr o b))
  pullSlotO o b B x = B (homSlotOf h o b x)

  private
    coeTyT : {s : S'} (B : T.TheoryTy ℓA s) {x y : Fib' .carrier s}
           → x Eq.≡ y → B y → B x
    coeTyT B Eq.refl b = b

  -- PUSH.  Given preservation and, at each TARGET slot, a way of turning
  -- the source payload into the target's, the source tensor maps into the
  -- reindexed target tensor.  `tr` is the only extra datum, and it is
  -- forced: with `onAr` not assumed injective or surjective there is no
  -- canonical source slot family to take.
  module _ (o : σ .ops) (P : SplitPresAtOver h o)
           (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
           (B : (b : τ .arities (φ .onOp o))
              → T.TheoryTy ℓB (τ .sortOf (φ .onOp o) b))
           (tr : (b : τ .arities (φ .onOp o))
               → A (φ .onAr o b) ⊢ pullSlotO o b (B b)) where

    push⊗O : ⊗ˢ o A ⊢ pullResO o (T.⊗ˢ (φ .onOp o) B)
    push⊗O m (sp , k) =
        P .homSplitO m sp
      , λ b → coeTyT (B b) (P .homPartsO m sp b)
                     (tr b _ (k (φ .onAr o b)))

  -- ================================================================
  -- PULL.  Reflection inverts `push⊗O` -- but only if every SOURCE slot
  -- is named by some target slot.  That extra condition is invisible in
  -- the single-signature theory (`onAr` is the identity there) and is
  -- the one genuinely new obligation a change of signature introduces:
  -- a pass that FORGETS a slot may still preserve tensors and can never
  -- reflect them, because the source tensor has a payload the target
  -- does not carry.
  -- ================================================================

  private
    -- moving a payload from one slot to a PROVABLY equal slot.  The
    -- coercion is on the ARITY, not on the carrier, so `parts` moves
    -- with it and nothing is left stuck under `Fib .parts`.
    coeAr : (o : σ .ops)
            (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
            (m : Fib .carrier (σ .resultSort o)) (sp : Fib .Split o m)
            {a a' : σ .arities o} → a Eq.≡ a'
          → A a (Fib .parts o m sp a) → A a' (Fib .parts o m sp a')
    coeAr o A m sp Eq.refl x = x

  module _ (o : σ .ops) (R : ReflectsSplitAtOver h o) (sec : ArSection φ o)
           (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
           (B : (b : τ .arities (φ .onOp o))
              → T.TheoryTy ℓB (τ .sortOf (φ .onOp o) b))
           (tr : (b : τ .arities (φ .onOp o))
               → pullSlotO o b (B b) ⊢ A (φ .onAr o b)) where

    pull⊗O : pullResO o (T.⊗ˢ (φ .onOp o) B) ⊢ ⊗ˢ o A
    pull⊗O m (sp' , k) =
        R m sp' .fst
      , λ a → coeAr o A m (R m sp' .fst) (sec a .snd)
                (tr (sec a .fst) _
                   (coeTyT (B (sec a .fst))
                           (Eq.sym (R m sp' .snd (sec a .fst)))
                           (k (sec a .fst))))
