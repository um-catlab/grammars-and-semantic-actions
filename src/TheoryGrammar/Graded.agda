{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- ASSEMBLY POINT.  This file used to carry four unrelated jobs at once:
   the later modality, the grading structure, guardedness, the
   hylomorphism, and automata.  They now live in named files and this
   one only re-exports them, so `open import TheoryGrammar.Graded` and
   `open Guard GS ...` keep working unchanged at every instance.

     TheoryGrammar.Later      -- ▷/next/löb over any well-founded order
     TheoryGrammar.Grading    -- GradedFib, and guardedness of a description
     TheoryGrammar.Hylo       -- the strength, hylo, and fused hyloC
     TheoryGrammar.Automaton  -- automata as algebras; exports `Guard`
-}
module TheoryGrammar.Graded where

open import TheoryGrammar.Later public
open import TheoryGrammar.Grading public
open import TheoryGrammar.Hylo public
open import TheoryGrammar.Automaton public
