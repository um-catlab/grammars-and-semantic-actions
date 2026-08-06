{-
  The signature of a SEMIMODULE: scalars acting on elements.

  Two sorts, four operations.  `actOp` is the point of the exercise --
  its two slots have DIFFERENT sorts (`sortOf actOp true = scl`,
  `sortOf actOp false = elt`), exactly as `lamOp` does in the lambda
  instance, so the many-sorted machinery is genuinely exercised and
  `if_then_else_` cannot express the arity family.

  Why these four and no more:

    oneOp  : ()        → scl   the unit of the scalar monoid
    mulOp  : scl,scl   → scl   the scalar monoid
    actOp  : scl,elt   → elt   THE ACTION -- this is `!`
    catOp  : elt,elt   → elt   the monoid of elements

  Three would suffice for the action itself, and the task of this
  instance is the action.  `catOp` is here for one reason: the
  NON-LINEAR laws of the graded modality are statements about a tensor
  of elements, and a law you cannot even state is a law you cannot
  refute.  With `catOp` present, `!ᵣ(A ⊗ B) ⊢ !ᵣA ⊗ !ᵣB` and
  `!_{r+s}A ⊢ !ᵣA ⊗ !ₛA` are both well-formed types, and the file
  `Graded.agda` can say precisely which of them holds and why.

  There is deliberately NO addition on scalars.  Grades `r` enter as
  metalanguage naturals through the representable `⌈ r ⌉`, so `r + s`
  is available in a type without being an operation of the signature.
  That is the standard "theory with parameters" move, and it is what
  keeps the variable context of every equation below down to ONE
  variable -- which matters more than it looks, see `Graded.agda`.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Semimodule.Signature where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Empty using (⊥)

open import TheoryGrammar.Base

data MSort : Type₀ where
  scl elt : MSort

data MOp : Type₀ where
  oneOp mulOp catOp actOp : MOp

MAr : MOp → Type₀
MAr oneOp = ⊥
MAr mulOp = Bool
MAr catOp = Bool
MAr actOp = Bool

-- `actOp` is the non-constant `sortOf`: a scalar in slot `true`, an
-- element in slot `false`.
MSortOf : (o : MOp) → MAr o → MSort
MSortOf oneOp ()
MSortOf mulOp _     = scl
MSortOf catOp _     = elt
MSortOf actOp true  = scl
MSortOf actOp false = elt

MResult : MOp → MSort
MResult oneOp = scl
MResult mulOp = scl
MResult catOp = elt
MResult actOp = elt

semiSig : SortedSig MSort ℓ-zero ℓ-zero
semiSig .ops        = MOp
semiSig .arities    = MAr
semiSig .sortOf     = MSortOf
semiSig .resultSort = MResult
