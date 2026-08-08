{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- THE CHART, GENERICALLY -- at ONE SORT. `Strings/CYK.Decide`,
   `Spans/CYK.Decide` and `Traces/ProtocolTests`'s `module CYK` carry the
   same `decRow`/`step`/`chart`/`derives?`/`parse`. -}
module TheoryGrammar.Decidable.Chart where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit
open import Cubical.Data.List

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Grading
open import TheoryGrammar.Enumerable using (_∈L_)
open import TheoryGrammar.Decidable.Tensor using (module DecFib)
open import TheoryGrammar.Decidable.Guarded using (module DecGuard)
open import TheoryGrammar.View using (module CompleteViews)

private variable ℓ ℓ' ℓX ℓP ℓV ℓR ℓA : Level

-- The signature is over `Unit`: see the header.  This is a restriction
-- on the THEORY, not on the grammar -- `V` below is arbitrary.
module DecChart {σ : SortedSig Unit ℓ ℓ'} (GS : GradedFib σ ℓX ℓP) where

  open DecFib (GS .fib) public
  open DecGuard GS public
    using (SortFam; ▷ᴬ; ▷ᴾ; ▷ᴬ→▷ᴾ; löbᵍ; World; module Tab; module TabΠ)
  open CompleteViews (GS .fib .carrier) using (Cover; Probe)

  -- The CFG layer, as it is presented by a description module: the non-
  -- terminals, their rules, the parse-tree grammar, and the fixed point as
  -- a pair of maps.

  module Rows (V : Type ℓV) (Rule : V → Type ℓR)
              (Deriv : V → TheoryTy ℓA tt)
              (RuleG : (P : V) → Rule P → TheoryTy ℓA tt)
              (rollD   : (P : V) → ⊕ᴰ (Rule P) (RuleG P) ⊢ Deriv P)
              (unrollD : (P : V) → Deriv P ⊢ ⊕ᴰ (Rule P) (RuleG P))
              (allRules    : (P : V) → List (Rule P))
              (allComplete : (P : V) (r : Rule P) → r ∈L allRules P)
              where

    -- ONE GRAMMAR holding the decision for every non-terminal at the
    -- current world.
    Chart : TheoryTy (ℓ-max ℓV ℓA) tt
    Chart = &ᴰ V (λ P → Dec⟨ Deriv P ⟩)

    -- ... and this is the line the many-sorted case cannot write.
    ChartF : SortFam (ℓ-max ℓV ℓA)
    ChartF _ = Chart

    chartAt : (P : V) → Chart ⊢ Dec⟨ Deriv P ⟩
    chartAt P = &ᴰ-E V {B = λ Q → Dec⟨ Deriv Q ⟩} P

    -- Given a decision for each RULE -- the part that knows the shape
    -- of the grammar's productions -- the rest is uniform.

    -- The rule decider sits at `▷ᴾ`, the DEPENDENCY-order later, not at
    -- the degree-order `▷ᴬ`: `▷ᴾ` is what the recursion actually consults
    -- and is finitely many worlds, hence schedulable.
    module Step (decRule : (P : V) (r : Rule P)
                         → ▷ᴾ ChartF {tt} ⊢ Dec⟨ RuleG P r ⟩) where

      decRow : (P : V) → ▷ᴾ ChartF {tt} ⊢ Dec⟨ Deriv P ⟩
      decRow P =
        dec-map (⊕ᴰ (Rule P) (RuleG P)) (Deriv P) (rollD P) (unrollD P)
        ∘g dec-⊕ᴰ (Rule P) (RuleG P) (allRules P) (allComplete P)
        ∘g &ᴰ-I {B = λ r → Dec⟨ RuleG P r ⟩} (decRule P)

      -- THE LÖB STEP, a term.  No index matched, no Agda function fed
      -- to `löb`, no element where a map belongs.
      step : ▷ᴾ ChartF {tt} ⊢ Chart
      step = &ᴰ-I {B = λ P → Dec⟨ Deriv P ⟩} decRow

      chart : Cover Chart
      chart = löbᵍ ChartF (λ _ → step ∘g ▷ᴬ→▷ᴾ ChartF) tt

      derives? : (P : V) → Probe (Deriv P)
      derives? P = chartAt P ∘g chart

      -- the exclusion is free, so it packages as a `Decision`
      derivesDec : (P : V) → Decision (Deriv P) (¬G (Deriv P))
      derivesDec P = decDefault (Deriv P) (derives? P)

      -- ... and the parser is the decision, FORGOTTEN: `Dec⟨ A ⟩` is
      -- `Result (¬G A) A` and `MaybeG A` is `Result ⊤G A`, so `toMaybe`
      -- is the whole of it.
      parse : (P : V) → Cover (MaybeG (Deriv P))
      parse P = toMaybe (Deriv P) ∘g derives? P

      -- ... AND THE SAME CHART, TABULATED.

      private module T = Tab ChartF

      module Tabulated (allV : List V) (allVComplete : (P : V) → P ∈L allV)
                       where

        private module TΠ = TabΠ V (λ P _ → Dec⟨ Deriv P ⟩) allV allVComplete

        module Sched (schedΠ : (w : World) → T.SchedQ w)
                     (schedD : (w : World) → TΠ.SchedQ w) where

          -- the table with a Π cell: the schedule doing its job and the
          -- cell undoing it (see `TheoryGrammar.ShareProbe`, which
          -- measures exactly this difference on plain Fibonacci)
          chartΠ : Cover Chart
          chartΠ = T.löbᵀQ (λ _ → step) schedΠ tt

          -- ... and with the non-terminal in the data too.  THE ONE TO
          -- USE.
          chartD : Cover Chart
          chartD = TΠ.löbᴰ (λ _ → step) schedD tt

          -- and it is the same chart: `TabΠ.löbᴰ≡` and `Tab.löbᵀQ≡`,
          -- both of which are `DP.buildQ-correct` plus `löb-unique`.
          chartD≡ : (m : GS .fib .carrier tt) (u : ⊤G {tt} m)
                  → chartD m u ≡ chartΠ m u
          chartD≡ m u =
              TΠ.löbᴰ≡ (λ _ → step) schedD tt m
            ∙ sym (T.löbᵀQ≡ (λ _ → step) schedΠ tt m)

          -- the three observations again, over the shared chart.  They
          -- are NOT `Step`'s -- `Step`'s run on `löbᵍ` -- so they carry
          -- their own names and `derivesD?≡` relates them.
          derivesD? derivesΠ? : (P : V) → Probe (Deriv P)
          derivesD? P = chartAt P ∘g chartD
          derivesΠ? P = chartAt P ∘g chartΠ

          derivesD?≡ : (P : V) (m : GS .fib .carrier tt) (u : ⊤G {tt} m)
                     → derivesD? P m u ≡ derivesΠ? P m u
          derivesD?≡ P m u = cong (chartAt P m) (chartD≡ m u)

          derivesDecD : (P : V) → Decision (Deriv P) (¬G (Deriv P))
          derivesDecD P = decDefault (Deriv P) (derivesD? P)

          parseD : (P : V) → Cover (MaybeG (Deriv P))
          parseD P = toMaybe (Deriv P) ∘g derivesD? P
