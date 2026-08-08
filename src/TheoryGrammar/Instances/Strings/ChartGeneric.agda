{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- SUBSUMPTION CHECK for `Decidable/Chart.agda`. -}
open import Cubical.Foundations.Prelude

open import Cubical.Data.List
open import TheoryGrammar.Enumerable using (_∈L_)

module TheoryGrammar.Instances.Strings.ChartGeneric (Char : Type₀) where

open import TheoryGrammar.Decidable.Chart using (module DecChart)
open import TheoryGrammar.Instances.Strings.CYK Char

module _ (V : Type₀)
         (unitR : V → Char → Type₀)
         (binR  : V → V → V → Type₀) where

  open Parser V unitR binR

  module _ (allRules    : (P : V) → List (Rule P))
           (allComplete : (P : V) (r : Rule P) → r ∈L allRules P)
           (litProbe    : (c : Char) → Probe ⌈ c ∷ [] ⌉) where

    -- the hand-written one ...
    module D = Decide allRules allComplete litProbe

    -- ... and the generic one, fed D's rule decider and nothing else.
    -- `Layer P` is passed where `⊕ᴰ (Rule P) (RuleG P)` is asked for,
    -- and it typechecks because the description IS the connective.
    module GC  = DecChart strGraded
    module GR  = GC.Rows V Rule Deriv RuleG rollD unrollD
                         allRules allComplete
    module GSt = GR.Step D.decRule

    -- THE MEASUREMENT.  Same chart, same probe, same parser -- by
    -- `refl`, not by an isomorphism.
    same-chart : GR.Chart ≡ D.Chart
    same-chart = refl

    same-step : GSt.chart ≡ D.chart
    same-step = refl

    same-derives : (P : V) → GSt.derives? P ≡ D.derives? P
    same-derives P = refl

    same-parse : (P : V) → GSt.parse P ≡ D.parse P
    same-parse P = refl
