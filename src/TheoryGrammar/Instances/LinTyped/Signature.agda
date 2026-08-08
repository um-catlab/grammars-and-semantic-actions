{- The signature of LINEARLY typed lambda ASTs: THREE sorts, six
   operations. -}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Instances.LinTyped.Signature where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Unit using (Unit)

open import TheoryGrammar.Base

-- `TSort` denotes the three kinds of thing this syntax talks about: a
-- de Bruijn index, a term, a type.
data TSort : Type₀ where
  nm tm ty : TSort

-- `TOp` denotes the node labels of the abstract syntax -- four term
-- constructors and two type constructors.
data TOp : Type₀ where
  varOp appOp lamOp annOp baseOp lolOp : TOp

-- `TAr o` denotes the SLOTS of an `o`-node, as an index type.  Note
-- `lamOp` is unary: a de Bruijn binder has a body and nothing else.
TAr : TOp → Type₀
TAr varOp  = Unit
TAr appOp  = Bool
TAr lamOp  = Unit
TAr annOp  = Bool
TAr baseOp = ⊥
TAr lolOp  = Bool

-- `TSortOf o a` denotes the sort that slot `a` of an `o`-node holds.
TSortOf : (o : TOp) → TAr o → TSort
TSortOf varOp  _     = nm
TSortOf appOp  _     = tm
TSortOf lamOp  _     = tm
TSortOf annOp  true  = tm
TSortOf annOp  false = ty
TSortOf baseOp ()
TSortOf lolOp  _     = ty

-- `TResult o` denotes the sort an `o`-node itself lands at.
TResult : TOp → TSort
TResult varOp  = tm
TResult appOp  = tm
TResult lamOp  = tm
TResult annOp  = tm
TResult baseOp = ty
TResult lolOp  = ty

-- the four tables above, packaged as the calculus' notion of signature
linSig : SortedSig TSort ℓ-zero ℓ-zero
linSig .ops        = TOp
linSig .arities    = TAr
linSig .sortOf     = TSortOf
linSig .resultSort = TResult
