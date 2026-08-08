{-# OPTIONS --lossy-unification #-}
{-
  AN ISA IS A TWO-SORTED ALGEBRAIC THEORY.

  `ISA.Machine`'s header reads an instruction-set architecture off two
  monoids -- program text, and machine resource -- and then keeps them in
  two separate `Fibered`s over `monoidSig`, linked in the metalanguage by
  a function `sem : Program -> Cmd`.  That is one theory too many and one
  operation too few.

  This file says instead:

      an ISA is ONE signature with TWO SORTS and THREE OPERATIONS.

      prog                          the sort of program text
      res                           the sort of machine resource

      seqop : prog, prog -> prog    sequencing            (TEMPORAL)
      sepop : res , res  -> res     disjoint union        (SPATIAL)
      runop : prog, res  -> res     execution             (THE LINK)

  The first two are the two monoids, now genuinely in one signature
  rather than in two copies of `monoidSig`.  The third is what is new,
  and it is the whole point of the file:

      `Split runop h'`  is the STEP RELATION.

  A splitting of a resource `h'` at `runop` is a way of seeing `h'` as
  "what you get by running some program `p` on some resource `h`" -- so
  the machine's operational semantics is not a semantic action, not an
  external interpreter, and not a hypothesis of the framework.  It is the
  splitting data of one operation of the theory, exactly as concatenation
  is the splitting data of `appop` for strings.

  Everything Hoare-shaped is then a CONNECTIVE rather than a definition:

      A * B          = ⊗ˢ sepop        separating conjunction
      P · Q          = ⊗ˢ seqop        program-text composition
      sp P A         = ⊗ˢ runop (P,A)  strongest postcondition
      wp P B         = ⊸ˢ runop @res   weakest precondition
      {A} P {B}      = A ⊢ wp P B      the Hoare triple

  and `sp ⊣ wp` is `TheoryGrammar.Fibered.⊸ˢ-app`, which is already
  proved, generically, for every operation of every signature.

  WHY THE ARITIES ARE ALL `Bool`

  All three operations are binary, so `arities o = Bool` uniformly and
  the arity eliminator `boolΠ` is the only thing that ever matches on a
  slot.  `sortOf` is where the two-sortedness lives, and it is
  nonconstant at exactly one operation -- `runop`, whose left slot is a
  program and whose right slot is a resource.  That single nonconstancy
  is what makes this a two-sorted theory rather than two one-sorted ones.
-}
module TheoryGrammar.Machine.Signature where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool; true; false)

open import TheoryGrammar.Base

-- Sorts.

data ISort : Type₀ where
  prog res : ISort

-- Operations.

data ISAOp : Type₀ where
  seqop sepop runop : ISAOp

-- Every operation is binary.  `boolΠ` below is the only eliminator any
-- file needs, and it is the standard one (a NAMED function, never an
-- extended lambda -- Agda identifies those nominally).
ISAAr : ISAOp → Type₀
ISAAr _ = Bool

-- `boolΠ` (Bool's dependent eliminator, = the binary arity's) now
-- comes from `TheoryGrammar.Theories.Monoid`, where the arity is.

-- The two-sortedness, concentrated in one line: `runop`'s left slot is a
-- PROGRAM and its right slot is a RESOURCE.
ISASortOf : (o : ISAOp) → ISAAr o → ISort
ISASortOf seqop _     = prog
ISASortOf sepop _     = res
ISASortOf runop true  = prog
ISASortOf runop false = res

ISAResult : ISAOp → ISort
ISAResult seqop = prog
ISAResult sepop = res
ISAResult runop = res

isaSig : SortedSig ISort ℓ-zero ℓ-zero
isaSig .ops          = ISAOp
isaSig .arities      = ISAAr
isaSig .sortOf       = ISASortOf
isaSig .resultSort   = ISAResult

-- Named slots, so that no downstream file writes `true`/`false` and has
-- to be read twice.
pslot : ISAAr runop
pslot = true

rslot : ISAAr runop
rslot = false
