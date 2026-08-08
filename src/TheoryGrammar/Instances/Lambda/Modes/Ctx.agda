{- THE SIGNATURE OF CONTEXTS: one sort, one binary operation. -}
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
