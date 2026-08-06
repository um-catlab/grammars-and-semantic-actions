{-
  The signature of annotated lambda ASTs: THREE sorts, six operations.

  `nm` and `tm` are as in the two-sorted Lambda instance; `ty` is new,
  and the types get their OWN operations (`baseOp`, `arrOp`) in the SAME
  signature rather than living outside the theory.  Two things are new
  as a result:

    * `annOp` has slots in DIFFERENT sorts that are neither `nm` nor a
      binder -- `tm` and `ty` -- so `sortOf` is non-constant for a reason
      unrelated to binding;
    * `baseOp` has EMPTY arity, so `⊗ˢ baseOp` is the representable
      `⌈ base ⌉` up to iso, and `decSlots` at it is vacuous.
-}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Instances.SimplyTyped.Signature where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥)

open import TheoryGrammar.Base

data TSort : Type₀ where
  nm tm ty : TSort

data TOp : Type₀ where
  varOp appOp lamOp annOp baseOp arrOp : TOp

TAr : TOp → Type₀
TAr varOp  = Unit
TAr appOp  = Bool
TAr lamOp  = Bool
TAr annOp  = Bool
TAr baseOp = ⊥
TAr arrOp  = Bool

-- `lamOp` mixes nm/tm (binding); `annOp` mixes tm/ty (the direction
-- switch); `arrOp` stays inside ty.
TSortOf : (o : TOp) → TAr o → TSort
TSortOf varOp  _     = nm
TSortOf appOp  _     = tm
TSortOf lamOp  true  = nm
TSortOf lamOp  false = tm
TSortOf annOp  true  = tm
TSortOf annOp  false = ty
TSortOf baseOp ()
TSortOf arrOp  _     = ty

TResult : TOp → TSort
TResult varOp  = tm
TResult appOp  = tm
TResult lamOp  = tm
TResult annOp  = tm
TResult baseOp = ty
TResult arrOp  = ty

stlcSig : SortedSig TSort ℓ-zero ℓ-zero
stlcSig .ops        = TOp
stlcSig .arities    = TAr
stlcSig .sortOf     = TSortOf
stlcSig .resultSort = TResult
