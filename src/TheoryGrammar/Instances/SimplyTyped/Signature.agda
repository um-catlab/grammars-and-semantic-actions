{- The signature of annotated lambda ASTs: THREE sorts, six operations. -}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Instances.SimplyTyped.Signature where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Unit using (Unit)

open import TheoryGrammar.Base

-- `TSort` denotes the three kinds of thing this syntax talks about: a
-- name, a term, a type.
data TSort : Type₀ where
  nm tm ty : TSort

-- `TOp` denotes the node labels of the abstract syntax -- four term
-- constructors and two type constructors.
data TOp : Type₀ where
  varOp appOp lamOp annOp baseOp arrOp : TOp

-- `TAr o` denotes the SLOTS of an `o`-node, as an index type.
TAr : TOp → Type₀
TAr varOp  = Unit
TAr appOp  = Bool
TAr lamOp  = Bool
TAr annOp  = Bool
TAr baseOp = ⊥
TAr arrOp  = Bool

-- `TSortOf o a` denotes the sort that slot `a` of an `o`-node holds.
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

-- `TResult o` denotes the sort an `o`-node itself lands at.
TResult : TOp → TSort
TResult varOp  = tm
TResult appOp  = tm
TResult lamOp  = tm
TResult annOp  = tm
TResult baseOp = ty
TResult arrOp  = ty

-- the four tables above, packaged as the calculus' notion of signature
stlcSig : SortedSig TSort ℓ-zero ℓ-zero
stlcSig .ops        = TOp
stlcSig .arities    = TAr
stlcSig .sortOf     = TSortOf
stlcSig .resultSort = TResult
