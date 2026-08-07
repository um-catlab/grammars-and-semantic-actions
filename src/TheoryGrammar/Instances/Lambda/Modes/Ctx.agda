{-
  THE SIGNATURE OF CONTEXTS: one sort, one binary operation.

  DENOTES: the shape of "a context is consumed by a node".  A
  substructural MODE is a promodel over this signature -- a choice of
  which decompositions count -- and nothing else.  The four modes share
  this signature and differ only in `Split` (and, for affine, in one
  leaf modality).

    CtxOp   the operations: `mul`, "consume a context in two parts"
    CtxAr   its arity, `Bool`: the two parts, named `true` and `false`
    ctxSig  the two, packaged one-sorted
-}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Instances.Lambda.Modes.Ctx where

open import Cubical.Data.Bool using (Bool)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Foundations.Prelude

open import TheoryGrammar.Base

data CtxOp : Type₀ where
  mul : CtxOp

CtxAr : CtxOp → Type₀
CtxAr mul = Bool

ctxSig : SortedSig Unit ℓ-zero ℓ-zero
ctxSig .ops          = CtxOp
ctxSig .arities      = CtxAr
ctxSig .sortOf _ _   = tt
ctxSig .resultSort _ = tt
