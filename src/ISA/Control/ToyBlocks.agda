{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  A STRUCTURED TOY PROGRAM, AND ITS TRIPLE.

  `ISA.Control.Blocks` closes the alphabet under `if` and `while` and
  instantiates `ISA.Program` at the result.  This file writes an actual
  program in that alphabet, over `ISA.Toy`'s instruction set:

      nop ;
      while (rk ≠ 0) {
        if (head = v2) then store 0 v1 else store 0 v0
      }

  as the `Block`

      instr nop ∷ whA busy (ifA isV2 (instr (store 0 v1) ∷ [])
                                     (instr (store 0 v0) ∷ [])
                            ∷ [])
                ∷ []

  and derives its triple.  The point of the file is the SHAPE of that
  derivation:

      progTriple = seq∷ … (atomRule nop …) (whileRuleB … bodyBTriple)

  `seq∷` is `ISA.Interp.seq` at the canonical splitting -- UNCHANGED,
  imported, knowing nothing about control flow.  The `while` enters it as
  a single LETTER.  So the free-monoid Hoare layer and the control-flow
  Hoare layer compose with no glue at all, which is the claim
  `ISA.Control.Blocks` makes and this file is the evidence for.

  The `refl` tests below check that `sem` on this program reduces to the
  command one would have written by hand -- i.e. that the mutual
  `semAtom`/`semBlock` computes, and that `ISA.Program.sem` at the
  enlarged alphabet agrees with it definitionally on a concrete block.
-}
open import Cubical.Foundations.Prelude

module ISA.Control.ToyBlocks where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.List using (List; []; _∷_)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Instances.Heap.Base
  using (Val; v0; v1; v2; Heap; single; heapFib)

open import ISA.Toy
  using (ToyI; nop; alloc; store; Store; toyStep; storeAx)

-- the guards, the variant and the invariant are `ISA.Control.Toy`'s;
-- nothing about them changes when control flow moves into program text
open import ISA.Control.Toy
  using (topV; rkV; rk; nz; eqV2; busy; isV2; Inv; storeI)

open import ISA.Control.Blocks heapFib ToyI toyStep

-- ==================================================================
-- THE PROGRAM.
-- ==================================================================

thenB : Block
thenB = instr (store 0 v1) ∷ []

elseB : Block
elseB = instr (store 0 v0) ∷ []

bodyB : Block
bodyB = ifA isV2 thenB elseB ∷ []

loopB : Block
loopB = whA busy bodyB ∷ []

prog : Block
prog = instr nop ∷ whA busy bodyB ∷ []

-- ==================================================================
-- THE SEMANTICS COMPUTES.  `sem` is `ISA.Program`'s, at the enlarged
-- alphabet; the right-hand sides are what one would have written by
-- hand at the command level.
-- ==================================================================

_ : semBlock thenB ≡ (Store 0 v1 ⨟ skip)
_ = refl

_ : semBlock bodyB ≡ (ifC isV2 (Store 0 v1 ⨟ skip) (Store 0 v0 ⨟ skip) ⨟ skip)
_ = refl

_ : sem loopB ≡ (While busy (semBlock bodyB) ⨟ skip)
_ = refl

_ : sem prog ≡ (skip ⨟ While busy (semBlock bodyB) ⨟ skip)
_ = refl

-- ==================================================================
-- THE TRIPLES.  Every line is a composite of an IMPORTED rule.
-- ==================================================================

-- a one-instruction block: `atomRule` plus the trailing `skip`
storeSkip : (x : Val) → ⟪ Inv ⟫ semBlock (instr (store 0 x) ∷ []) ⟪ Inv ⟫
storeSkip x = seqCmd (Store 0 x) skip (storeI x) (skipRule Inv)

-- the `if` inside the loop, then the block's trailing `skip`
bodyBTriple : ⟪ Inv & Tst busy true ⟫ semBlock bodyB ⟪ Inv ⟫
bodyBTriple =
  seqCmd (ifC isV2 (semBlock thenB) (semBlock elseB)) skip
    (condRule isV2 (semBlock thenB) (semBlock elseB)
       (storeSkip v1 ∘g &-E₁ ∘g &-E₁)
       (storeSkip v0 ∘g &-E₁ ∘g &-E₁))
    (skipRule Inv)

-- the loop, as a one-LETTER program
loopTripleB : ⟪ Inv ⟫ loopB ⟪ Inv & Tst busy false ⟫ᵖ
loopTripleB = whileRuleB Inv busy bodyB bodyBTriple

-- ... and the whole program, sequenced by `ISA.Interp.seq` -- which
-- knows nothing about `if` or `while`.
progTriple : ⟪ Inv ⟫ prog ⟪ Inv & Tst busy false ⟫ᵖ
progTriple =
  seq∷ (instr nop) (whA busy bodyB ∷ [])
    (atomRule nop (skipRule Inv))
    loopTripleB

-- ==================================================================
-- AND IT RUNS.  A concrete execution `[0 ↦ v2] ⇝ [0 ↦ v0]`, two
-- iterations, and the derived triple evaluates on it.
-- ==================================================================

runB : While busy (semBlock bodyB) (single 0 v2) (single 0 v0)
runB =
  wh-step {h₁ = single 0 v1} Eq.refl
    ( single 0 v1
    , ( true , single 0 v2 , (Eq.refl , Eq.refl)
      , single 0 v1 , (v2 , Eq.refl , Eq.refl) , Eq.refl )
    , Eq.refl )
    (wh-step {h₁ = single 0 v0} Eq.refl
      ( single 0 v0
      , ( false , single 0 v1 , (Eq.refl , Eq.refl)
        , single 0 v0 , (v1 , Eq.refl , Eq.refl) , Eq.refl )
      , Eq.refl )
      (wh-stop Eq.refl Eq.refl))

runProg : sem prog (single 0 v2) (single 0 v0)
runProg = single 0 v2 , Eq.refl , single 0 v0 , runB , Eq.refl

-- THE DERIVED TRIPLE COMPUTES, on program TEXT.
_ : progTriple (single 0 v2) (v2 , Eq.refl) (single 0 v0) runProg
    ≡ ((v0 , Eq.refl) , Eq.refl)
_ = refl
