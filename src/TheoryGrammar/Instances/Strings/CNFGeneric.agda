{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- DO THE TWO GENERIC LAYERS COMPOSE? `ChomskyNormal.CNF.Desc` is the CNF
   description written once, with the right-hand side indexed by the arity
   rather than being a pair. -}
open import Cubical.Foundations.Prelude
open import Cubical.Data.List
open import TheoryGrammar.Enumerable using (_∈L_)

module TheoryGrammar.Instances.Strings.CNFGeneric (Char : Type₀) where

open import TheoryGrammar.ChomskyNormal using (module CNF)
open import TheoryGrammar.Decidable.Chart using (module DecChart)
open import TheoryGrammar.Instances.Strings.CYK Char

module _ (V : Type₀)
         (unitR : V → Char → Type₀)
         -- the arity-indexed right-hand side: no `Q`, no `T`, no Bool
         (binR  : V → ((a : MonAr appop) → V) → Type₀) where

  module C = CNF strGraded
  module D = C.Desc appop V Char (λ c → ⌈ c ∷ [] ⌉) NonTrivial unitR binR

  module _ (allRules    : (P : V) → List (D.Rule P))
           (allComplete : (P : V) (r : D.Rule P) → r ∈L allRules P) where

    module GC = DecChart strGraded
    module GR = GC.Rows V D.Rule D.Deriv D.RuleG D.rollD D.unrollD
                        allRules allComplete

    -- THE MEASUREMENT: these two names existing at these two types is
    -- the whole claim.  The description's `Rule`/`Deriv`/`RuleG` and its
    -- roll/unroll pair are accepted by the chart unchanged.
    Chart : Gr
    Chart = GR.Chart

    chartAt : (P : V) → Chart ⊢ Dec⟨ D.Deriv P ⟩
    chartAt = GR.chartAt
