{- A GRADING OF THE LEFT FACTOR GRADES THE GLUE. `Grading` asks for a
   degree on the carrier, a properness predicate on splittings, and the two
   monotonicity laws. -}
module TheoryGrammar.Gluing.Graded where

open import Cubical.Foundations.Prelude

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Grading
open import TheoryGrammar.Gluing

module GradeGlue
  {ℓS ℓ ℓ' ℓX ℓX' ℓP ℓP' ℓR : Level}
  {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
  (Fib : Fibered σ ℓX ℓP) (Fib' : Fibered σ ℓX' ℓP') (R : Corr Fib Fib' ℓR)
  where

  open Glue Fib Fib' R

  -- `Proper` is the only field needing a `Lift`, and only because the
  -- glue's splittings sit at a bigger level.  It is a hypothesis, never
  -- compared, so the `Lift` costs nothing that the file measures.
  gradeLeft : Grading Fib → Grading glue
  gradeLeft Gr .deg s g          = Gr .deg s (g .fst)
  gradeLeft Gr .Proper o g sq a  =
    Lift (ℓ-max ℓP' (ℓ-max ℓ' ℓR)) (Gr .Proper o (g .fst) (sq .fst) a)
  gradeLeft Gr .deg≤ o g sq a    = Gr .deg≤ o (g .fst) (sq .fst) a
  gradeLeft Gr .deg< o g sq a pr = Gr .deg< o (g .fst) (sq .fst) a (pr .lower)

  gradedGlue : Grading Fib → GradedFib σ (ℓ-max ℓX (ℓ-max ℓX' ℓR))
                                         (ℓ-max ℓP (ℓ-max ℓP' (ℓ-max ℓ' ℓR)))
  gradedGlue Gr = graded glue (gradeLeft Gr)
