{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  CLOSURE CONVERSION, WITH NUMBERS.

  `Compile/ClosureConv/Convert.agda`'s three clauses plus two, and the
  two new ones are the cheapest in the file:

      nlit  ↦  ilit    no block, no capture, the counter untouched
      nadd  ↦  iadd    the splitting carried over VERBATIM

  `nadd`'s clause is `napp`'s clause with a different head, and that is
  the content of "a base primitive costs nothing in the linearity
  argument": `iadd` wants exactly the `Use⊎ u₁ u₂ u` that `nadd` had, so
  there is nothing to discharge.

  ------------------------------------------------------------------
  WHY THIS IS A DIRECT RECURSION AND NOT A FOLD
  ------------------------------------------------------------------

  `ClosureConv/Convert.agda` routes through `Opt.foldTm`, so that file
  contains no match on `Tm` at all.  `NTm` has no such fold -- building
  one means a new `Fibered λSig` whose `lamOp`'s `parts` is weakening,
  which is the ~150 lines `Compile/Suite/Terms.agda`'s header prices and
  declines.  So this is one PRIMITIVE (phase 1) recursion, marked, in
  the style of `LinToRust/Codegen.compileE`; the index is still
  preserved because the type says so.

  PHASE.  Phase 1, and marked.
-}
open import Cubical.Foundations.Prelude

module Compile.LinNum.Convert where

open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.List using (List; []; _∷_; _++_; length)
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Unit using (Unit; tt)
import Cubical.Data.Equality as Eq

import TheoryGrammar.Instances.LinLam.Syntax as L

open import Compile.LinNum.Syntax public
open import Compile.LinNum.IR      public

-- ==================================================================
-- §1  THE PASS.  PRIMITIVE (phase 1): the ONE recursion over `NTm`.
--
-- `n` is the next free block index; the result is the expression and
-- the blocks it filed, in index order starting at `n`.
-- ==================================================================

convT : ∀ {u} → NTm u → ℕ → IR u × Table
convT (nvar s)      n = ivar s , []
convT (nlit e k)    n = ilit e k , []
convT (napp sp f a) n =
  let rf = convT f n
      ra = convT a (n + length (rf .snd))
  in iapp sp (rf .fst) (ra .fst) , (rf .snd ++ ra .snd)
convT (nadd sp a b) n =
  let ra = convT a n
      rb = convT b (n + length (ra .snd))
  in iadd sp (ra .fst) (rb .fst) , (ra .snd ++ rb .snd)
convT {u} (nlam b)  n =
  let r = convT b (suc n)
  in iclos n (idCap u) , ((u , r .fst) ∷ r .snd)

convert : ∀ {u} → NTm u → IR u
convert t = convT t 0 .fst

tableOf : ∀ {u} → NTm u → Table
tableOf t = convT t 0 .snd

compileP : NTm [] → Prog
compileP t = tableOf t , convert t

-- the whole source-level observation: the number a term computes
obsN : NTm [] → Maybe Val
obsN t = runP 64 (compileP t)

numN : NTm [] → Maybe ℕ
numN t = numOf (obsN t)

-- ==================================================================
-- §2  IT COMPUTES, AND IT COMPUTES NUMBERS.
-- ==================================================================

-- `41` is one `ilit` and no blocks
_ : compileP lit41 Eq.≡ ([] , ilit tt 41)
_ = Eq.refl

_ : numN lit41 Eq.≡ just 41
_ = Eq.refl

_ : numN sum42 Eq.≡ just 42
_ = Eq.refl

-- THE TARGET.  `(λx. x + 1) 41` ⇓ 42
_ : numN incApp Eq.≡ just 42
_ = Eq.refl

-- ... and its block table: one block, shape `[]` (nothing to capture),
-- body `slot0 + 1`
_ : tableOf incApp Eq.≡ (([] , iadd (L.uleft L.unil) (ivar tt) (ilit tt 1)) ∷ [])
_ = Eq.refl

-- `(λx. λy. x + y) 40 2` -- the inner block CAPTURES `x`, so this is a
-- number read back out of a closure environment
_ : numN addApp Eq.≡ just 42
_ = Eq.refl

_ : numN sum143 Eq.≡ just 143
_ = Eq.refl

-- `(λf. f 41) (λx. x + 1)` -- the call goes through a variable
_ : numN applyInc Eq.≡ just 42
_ = Eq.refl

-- A λ IS STILL A CLOSURE, and `numOf` says so by answering `nothing` --
-- which is exactly `Correct.valuesCollapse` no longer applying: the
-- observation now separates `inc` from `incApp`.
_ : obsN inc Eq.≡ just (clos 0 [])
_ = Eq.refl

_ : numN inc Eq.≡ nothing
_ = Eq.refl

-- ... and the OLD language embeds with its old answer
_ : obsN (fromTm L.idLin) Eq.≡ just (clos 0 [])
_ = Eq.refl

_ : obsN (fromTm L.selfApp) Eq.≡ just (clos 1 [])
_ = Eq.refl
