{-
  THE SIGNATURE OF CONTEXTS: one sort, one binary operation.

  A substructural MODE is a promodel over this signature -- i.e. a choice
  of how a context splits when a node consumes it -- and nothing else.
  The four modes below share this signature and differ only in `Split`
  (and, for affine, in one leaf modality).
-}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Instances.Lambda.Modes.Ctx where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool
open import Cubical.Data.Unit

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
