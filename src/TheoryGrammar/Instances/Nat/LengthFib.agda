{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{-
  `length` AS A REINDEXING OF PROMODELS, both halves.

  `Nat/Length.agda` states the same thing at the level of MODELS, where
  preservation is `homOp` (needing `lengthApp`) and reflection is `cut`
  (needing its two length equations proved alongside).  At the promodel
  level both are direct recursions on the SPLITTING: erase the character
  at each `cons` and a string decomposition is an addition; conversely,
  recurse on the `Add3` and the cut falls out with its equations.

  Split out of `Nat/Glue.agda` because the aligned-pairs instance needs
  it at TWO alphabets, and reflection -- the discrete Conduché half --
  is what a non-trivial right leg of a comma object requires.
  PRIMITIVE: `lenSplit3`, `lenNil`, `cutS`, `zeroLenS`.
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Nat.LengthFib (Char : Type₀) where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.List
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Theories.Monoid
open import TheoryGrammar.Fibered
open import TheoryGrammar.CarrierMap

import TheoryGrammar.Instances.Strings.Base as StB
module St = StB Char
import TheoryGrammar.Instances.Nat.Base as Nt

lenIx : Reindex St.strFib Nt.natFib
lenIx .hom _ = length

-- ==================================================================
-- PRESERVATION.
-- ==================================================================

-- PRIMITIVE.  Erase the character at each `cons`: a string decomposition
-- IS an addition, with no equation left over.
lenSplit3 : {u v w : St.String} → St.Split3 u v w
          → Nt.Add3 (length u) (length v) (length w)
lenSplit3 St.nil      = Nt.z
lenSplit3 (St.cons p) = Nt.s (lenSplit3 p)

-- PRIMITIVE.  The nullary case.
lenNil : (w : St.String) → St.IsNil w → Nt.IsZero (length w)
lenNil [] _ = tt

lenPres : (o : MonOp) → SplitPresAt lenIx o
lenPres nilop .homSplit w sp          = lenNil w sp
lenPres nilop .homParts w sp          ()
lenPres appop .homSplit w (u , v , p) = length u , length v , lenSplit3 p
lenPres appop .homParts w (u , v , p) true  = Eq.refl
lenPres appop .homParts w (u , v , p) false = Eq.refl

-- ==================================================================
-- REFLECTION -- the discrete Conduché half.
-- ==================================================================

-- PRIMITIVE.  THE CUT, by recursion on the ADDITION rather than on the
-- number: the string is consumed in step with the `Add3`, so the two
-- length equations are `Eq.refl` and `Eq.ap suc` rather than a separate
-- induction.  Compare `Nat/Length.cut`, which recurses on `i` and has to
-- carry `i + j Eq.≡ length w` through every step.
cutS : {i j : ℕ} (w : St.String) → Nt.Add3 i j (length w)
     → Σ[ u ∈ St.String ] Σ[ v ∈ St.String ]
         (St.Split3 u v w × (i Eq.≡ length u) × (j Eq.≡ length v))
cutS []      Nt.z     = [] , [] , St.nil , Eq.refl , Eq.refl
cutS (c ∷ w) Nt.z     = [] , c ∷ w , St.nil , Eq.refl , Eq.refl
cutS (c ∷ w) (Nt.s p) =
  let (u , v , q , eu , ev) = cutS w p
  in c ∷ u , v , St.cons q , Eq.ap suc eu , ev

-- PRIMITIVE.  Its nullary counterpart.
zeroLenS : (w : St.String) → Nt.IsZero (length w) → St.IsNil w
zeroLenS [] _ = tt

lenReflects : (o : MonOp) → Along.ReflectsSplitAt lenIx o
lenReflects nilop w sp = zeroLenS w sp , λ ()
lenReflects appop w (i , j , add) =
  let (u , v , q , eu , ev) = cutS w add
  in (u , v , q) , λ { true → eu ; false → ev }
