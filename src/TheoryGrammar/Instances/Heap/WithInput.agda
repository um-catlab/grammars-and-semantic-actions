{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{-
  A HEAP ALONGSIDE AN INPUT TAPE: two theories at two DIFFERENT
  signatures on one carrier.

  This is what `Lifting.bothLift` was for, and `Gluing` could not state:
  the factors are a free monoid and a partial commutative monoid, so
  they do not share a signature and no relation between their carriers
  is involved.  The carrier is `String × Heap`, and each theory splits
  ITS OWN component and shares the other -- so `⊗ᵒ` cuts the input with
  the heap untouched, and `∗` splits the heap with the input untouched.

  Both liftings are three trivial lines (`Split↑` is `Unit`, `over` is
  `Eq.refl`), and the interchange law between the two operations is then
  FREE -- compare `Shuffle.mixedRefinable`, a three-clause recursion,
  where the two theories shared the carrier rather than being orthogonal.
  PRIMITIVE: none.
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Heap.WithInput (Char : Type₀) where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.List
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Theories.Monoid
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib
open import TheoryGrammar.Splitting
open import TheoryGrammar.Lifting
open import TheoryGrammar.Refinement
open import TheoryGrammar.Hoare
open import TheoryGrammar.Precision using (coeEq)

import TheoryGrammar.Instances.Strings.Base as StB
module S = StB Char
import TheoryGrammar.Instances.Heap.Base as H
import TheoryGrammar.Instances.Strings.Recompose as Rec
module Rc = Rec Char

-- ==================================================================
-- THE CARRIER, and the two liftings.
-- ==================================================================

State : Unit → Type₀
State _ = S.String × H.Heap

-- input side: cut the string, hand both halves the SAME heap
inputLift : Lifting (splittingOf S.strFib) State (λ _ → fst) ℓ-zero
inputLift .Split↑ o y sp        = Unit
inputLift .parts↑ o y sp l a    = S.strFib .parts o (y .fst) sp a , y .snd
inputLift .over   o y sp l a    = Eq.refl

-- heap side: split the heap disjointly, hand both halves the SAME input
heapLift : Lifting (splittingOf H.heapFib) State (λ _ → snd) ℓ-zero
heapLift .Split↑ o y sp         = Unit
heapLift .parts↑ o y sp l a     = y .fst , H.heapFib .parts o (y .snd) sp a
heapLift .over   o y sp l a     = Eq.refl

stateSpl : Splitting (monoidSig ⊎Sig monoidSig) State ℓ-zero
stateSpl = bothLift inputLift heapLift

stateFib : Fibered (monoidSig ⊎Sig monoidSig) ℓ-zero ℓ-zero
stateFib = ⟪ State , stateSpl ⟫

module M = RulesF stateFib

Gr : Type₁
Gr = M.TheoryTy ℓ-zero tt

-- slot families must be NAMED
pair : Gr → Gr → (a : MonAr appop) → Gr
pair P Q true  = P
pair P Q false = Q

infixr 20 _⊗ᵒ_ _∗_

-- the INPUT tensor: cuts the tape, leaves the heap alone
_⊗ᵒ_ : Gr → Gr → Gr
P ⊗ᵒ Q = M.⊗ˢ (inl appop) (pair P Q)

-- the SEPARATING conjunction: splits the heap, leaves the tape alone
_∗_ : Gr → Gr → Gr
P ∗ Q = M.⊗ˢ (inr appop) (pair P Q)

-- ==================================================================
-- THE INTERCHANGE LAW, for free.
--
-- Each `rowSplit` is the heap splitting it was given and each
-- `colSplit` the input splitting -- neither is recomputed, because the
-- two theories touch different components.  Every cell equation is
-- `Eq.refl`.
-- ==================================================================

module R = Refine stateFib

inpOp : R.HomOp tt
inpOp .R.op⋆    = inl appop
inpOp .R.resH   = Eq.refl
inpOp .R.argH _ = Eq.refl

heapOp : R.HomOp tt
heapOp .R.op⋆    = inr appop
heapOp .R.resH   = Eq.refl
heapOp .R.argH _ = Eq.refl

orthogonal : R.Refinable inpOp heapOp
orthogonal y p q = res
  where
  res : R.Refinement inpOp heapOp y p q
  res .R.cell i j    = S.strFib  .parts appop (y .fst) (p .fst) i
                     , H.heapFib .parts appop (y .snd) (q .fst) j
  res .R.rowSplit _  = q
  res .R.rowCell _ _ = Eq.refl
  res .R.colSplit _  = p
  res .R.colCell _ _ = Eq.refl

-- ==================================================================
-- TESTS.  The input cut leaves the heap alone at BOTH slots, with the
-- heap held abstract -- which is the whole content of `inputLift`.
-- ==================================================================

module _ (x y : Char) (h : H.Heap) where

  private
    w2 : S.String
    w2 = x ∷ y ∷ []

    st : State tt
    st = w2 , h

    cut : stateFib .Split (inl appop) st
    cut = ((x ∷ []) , (y ∷ []) , S.cons S.nil) , tt

  _ : stateFib .parts (inl appop) st cut true ≡ ((x ∷ []) , h)
  _ = refl

  _ : stateFib .parts (inl appop) st cut false ≡ ((y ∷ []) , h)
  _ = refl

-- ==================================================================
-- ONE FRAME RULE, TWO READINGS.
--
-- `Hoare.Frame` is generic in the OPERATION, so over a coproduct theory
-- it instantiates twice: at `inl appop` it frames the unconsumed INPUT,
-- at `inr appop` the untouched HEAP.  Nothing is written twice.
--
-- And the side condition is free in both directions.  `Local` is the
-- work in any frame rule -- a splitting of the input must survive the
-- command -- and here a command touching only one component leaves the
-- OTHER component's splittings alone by construction.  That is
-- `orthogonal` again, now paying at the level of a program logic.
-- ==================================================================

open Hoare stateFib stateFib

module FrameIn = Frame (inl appop)
module FrameHp = Frame (inr appop)

-- a command that rewrites the heap and leaves the tape where it was ...
heapOnly : (H.Heap → H.Heap → Type₀) → Cmd ℓ-zero tt tt
heapOnly ch (w , h) (w′ , h′) = (w′ Eq.≡ w) × ch h h′

-- ... and one that consumes tape and leaves the heap alone
inputOnly : (S.String → S.String → Type₀) → Cmd ℓ-zero tt tt
inputOnly cs (w , h) (w′ , h′) = cs w w′ × (h′ Eq.≡ h)

-- THE SIDE CONDITIONS, both one line: the splitting is handed straight
-- back, because the command never touched the component it splits.
heapFramesOverInput : (ch : H.Heap → H.Heap → Type₀)
                    → FrameIn.Local (heapOnly ch) (λ _ → heapOnly ch)
heapFramesOverInput ch (w , h) sl (w′ , h′) (Eq.refl , st) =
  sl , λ a → Eq.refl , st

inputFramesOverHeap : (cs : S.String → S.String → Type₀)
                    → FrameHp.Local (inputOnly cs) (λ _ → inputOnly cs)
inputFramesOverHeap cs (w , h) sl (w′ , h′) (st , Eq.refl) =
  sl , λ a → st , Eq.refl

-- ... hence both frame rules, each `frame-cmd` at its own operation.

heapFrame : (ch : H.Heap → H.Heap → Type₀)
            {A B : (a : MonAr appop) → Gr}
          → ((a : MonAr appop) → ⟪ A a ⟫ heapOnly ch ⟪ B a ⟫)
          → ⟪ M.⊗ˢ (inl appop) A ⟫ heapOnly ch ⟪ M.⊗ˢ (inl appop) B ⟫
heapFrame ch = FrameIn.frame-cmd (heapOnly ch) (λ _ → heapOnly ch)
                                 (heapFramesOverInput ch)

inputFrame : (cs : S.String → S.String → Type₀)
             {A B : (a : MonAr appop) → Gr}
           → ((a : MonAr appop) → ⟪ A a ⟫ inputOnly cs ⟪ B a ⟫)
           → ⟪ M.⊗ˢ (inr appop) A ⟫ inputOnly cs ⟪ M.⊗ˢ (inr appop) B ⟫
inputFrame cs = FrameHp.frame-cmd (inputOnly cs) (λ _ → inputOnly cs)
                                  (inputFramesOverHeap cs)

-- ==================================================================
-- THE OTHER DISTRIBUTION MODE: SPLIT, not share.
--
-- `inputLift` hands both halves of a tape cut the SAME heap.  The other
-- reading is that cutting the tape also divides the heap -- "parse this
-- prefix owning this fragment" -- and it is the same `Lifting` record
-- with `Split↑` a heap splitting instead of `Unit`.  Both signatures
-- are `monoidSig`, so the operation index is shared and the heap can
-- split along the very same `o`.
--
-- What does NOT transfer is the free frame rule above.  `Local` was one
-- line because a heap command left the tape's splittings untouched; at
-- `⊗ˡ` a heap command moves the component the splitting constrains, so
-- the uniform slot command `λ _ → c` no longer works and the classical
-- `boolΠ c skip` shape is needed.  That is the frame rule doing real
-- work rather than none -- stated here as the reason, not proved.
-- ==================================================================

splitLift : Lifting (splittingOf S.strFib) State (λ _ → fst) ℓ-zero
splitLift .Split↑ o y sp     = H.heapFib .Split o (y .snd)
splitLift .parts↑ o y sp l a = S.strFib  .parts o (y .fst) sp a
                             , H.heapFib .parts o (y .snd) l  a
splitLift .over   o y sp l a = Eq.refl

linSpl : Splitting (monoidSig ⊎Sig monoidSig) State ℓ-zero
linSpl = bothLift splitLift heapLift

linFib : Fibered (monoidSig ⊎Sig monoidSig) ℓ-zero ℓ-zero
linFib = ⟪ State , linSpl ⟫

module ML = RulesF linFib

GrL : Type₁
GrL = ML.TheoryTy ℓ-zero tt

pairL : GrL → GrL → (a : MonAr appop) → GrL
pairL P Q true  = P
pairL P Q false = Q

infixr 20 _⊗ˡ_

-- the LINEAR input tensor: cutting the tape divides the heap too
_⊗ˡ_ : GrL → GrL → GrL
P ⊗ˡ Q = ML.⊗ˢ (inl appop) (pairL P Q)

module _ (x y : Char) (h : H.Heap) where

  private
    w2′ : S.String
    w2′ = x ∷ y ∷ []

    st′ : State tt
    st′ = w2′ , h

    -- cut after one letter, and give the whole heap to the SECOND half
    linCut : linFib .Split (inl appop) st′
    linCut = ((x ∷ []) , (y ∷ []) , S.cons S.nil)
           , ([] , h , H.ilv-nilL h , tt)

  -- the left part owns no heap ...
  _ : linFib .parts (inl appop) st′ linCut true ≡ ((x ∷ []) , [])
  _ = refl

  -- ... and the right part owns all of it.  Contrast `stateFib`, where
  -- both halves of the same cut received `h`.
  _ : linFib .parts (inl appop) st′ linCut false ≡ ((y ∷ []) , h)
  _ = refl

-- ==================================================================
-- ... AND THE REFUTATION, so the paragraph above is a theorem.
--
-- Framing a heap command uniformly across a LINEAR tape cut asks both
-- halves to gain the same new cell.  The two halves must stay disjoint,
-- so they cannot -- and that is `#-self`, the reason separation logic
-- exists, arriving here as the obstruction to a frame rule.  No length
-- argument is needed; disjointness alone does it.
-- ==================================================================

module HoL      = Hoare linFib linFib
module FrameLin = HoL.Frame (inl appop)

module _ (l : H.Loc) (v : H.Val) (x y : Char) where

  private
    alloc : H.Heap → H.Heap → Type₀
    alloc h h′ = h′ Eq.≡ ((l , v) ∷ h)

    m0 : State tt
    m0 = (x ∷ y ∷ []) , []

    -- a linear cut of an EMPTY heap: both halves own nothing
    sl0 : linFib .Split (inl appop) m0
    sl0 = ((x ∷ []) , (y ∷ []) , S.cons S.nil) , ([] , [] , H.nil , tt)

    m1 : State tt
    m1 = (x ∷ y ∷ []) , ((l , v) ∷ [])

  noUniformFrame : FrameLin.Local (heapOnly alloc) (λ _ → heapOnly alloc) → ⊥
  noUniformFrame loc = H.#-self l v (H.#-Eq e₁ e₂ disj)
    where
    got = loc m0 sl0 m1 (Eq.refl , Eq.refl)

    hs : H.HeapSplit appop ((l , v) ∷ [])
    hs = got .fst .snd

    e₁ : hs .fst Eq.≡ H.single l v
    e₁ = got .snd true .snd

    e₂ : hs .snd .fst Eq.≡ H.single l v
    e₂ = got .snd false .snd

    disj : hs .fst H.# hs .snd .fst
    disj = hs .snd .snd .snd

-- ==================================================================
-- PROGRAMS IN `⊗ˡ`.
--
-- Splittings and a refutation are not evidence that a connective is
-- usable.  These are the two terms that eliminate `⊗ˡ` -- one reading
-- only the tape, one only the heap -- and a closed test that the first
-- EVALUATES.  Both are `⊗ˢ-E` at `inl appop` and nothing else.
-- ==================================================================

Tape : S.String → GrL
Tape u (w , h) = w Eq.≡ u

Nil : GrL
Nil (w , h) = H.IsNil h

-- the tape halves concatenate, the heap is not consulted
tapeCat : (u v : S.String) → (Tape u ⊗ˡ Tape v) ML.⊢ Tape (u ++ v)
tapeCat u v = ML.⊗ˢ-E (inl appop) {A = pairL (Tape u) (Tape v)}
                                  {B = Tape (u ++ v)} body
  where
  body : ML.MultiHomˢ (inl appop) (pairL (Tape u) (Tape v)) (Tape (u ++ v))
  body (w , h) ((u₁ , u₂ , p) , hsp) k =
    Rc.recompose p
      Eq.∙ (Eq.ap (λ z → z ++ u₂) (k true)
      Eq.∙ Eq.ap (λ z → u ++ z) (k false))

-- ... and dually, the heap halves: owning nothing on both sides of a
-- LINEAR cut means owning nothing.  Nothing like this is statable at
-- `⊗ᵒ`, where the halves were handed the whole heap.
ownsNil : (Nil ⊗ˡ Nil) ML.⊢ Nil
ownsNil = ML.⊗ˢ-E (inl appop) {A = pairL Nil Nil} {B = Nil} body
  where
  body : ML.MultiHomˢ (inl appop) (pairL Nil Nil) Nil
  body (w , h) (sp , [] , [] , ilv , d) k =
    coeEq H.IsNil (H.ilv-nilL-inv ilv) tt
  body (w , h) (sp , [] , _ ∷ _ , ilv , d) k = E.rec (k false)
  body (w , h) (sp , _ ∷ _ , v₂ , ilv , d) k = E.rec (k true)

module _ (x y : Char) (h : H.Heap) where

  private
    st″ : State tt
    st″ = (x ∷ y ∷ []) , h

    cut″ : linFib .Split (inl appop) st″
    cut″ = ((x ∷ []) , (y ∷ []) , S.cons S.nil)
         , ([] , h , H.ilv-nilL h , tt)

    pay″ : (a : MonAr appop)
         → pairL (Tape (x ∷ [])) (Tape (y ∷ [])) a
             (linFib .parts (inl appop) st″ cut″ a)
    pay″ true  = Eq.refl
    pay″ false = Eq.refl

  -- the term evaluates, and to the canonical proof
  _ : tapeCat (x ∷ []) (y ∷ []) st″ (cut″ , pay″) ≡ Eq.refl
  _ = refl
