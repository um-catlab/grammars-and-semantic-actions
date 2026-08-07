{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  CYK, IN THE THEORY OF SPANS -- the description, and the PROGRAM.

  The same description as `Instances.Strings.CYK`, but over `spanFib`
  instead of `strFib`.  Two things change, and both are the point:

  (1) `⊗e cat` really is "this span cuts into two adjacent spans", so
      the tensor of the calculus IS the CYK recurrence.  In the string
      theory `⊗e appop` splits a string into two strings, and the
      ambient word had to be carried by hand.

  (2) `deg (i , n) = n`, so guardedness descends on SPAN LENGTH.  A
      derivation at a span of length n recurses only at strictly shorter
      spans, which is precisely "fill the chart by increasing span
      length".  `▷ Deriv P` at a span IS the filled sub-chart, and it is
      a connective, not a data structure.

  The ambient word enters ONLY through `unitR : V → ℕ → Type₀`, read as
  "nonterminal P derives the terminal at position j".  Nothing else in
  the file knows there is a word.

  CNF's ban on ε-productions appears as `NEslot`: every recursive slot
  is paired with `⌜ NonEmpty ⌝`, and requiring BOTH slots non-empty is
  what makes BOTH proper -- because properness of a slot is non-emptiness
  of its COMPLEMENT (`Spans.Graded.SpanProper`).

  ==================================================================
  THE PROGRAM, and where its parts come from.

  `derives? : (P : V) → Probe (Deriv P)` is `löb` applied to a NAMED term
  `step : ▷ DecMot ⊢ᴵ DecMot`, and every layer of that term is a
  combinator:

      dec-map   (Layer P) (Deriv P) (rollD P) (unrollD P)
        ∘ dec-⊕ᴰ  (Rule P)  -- search the rules      (Decidable.Listable)
            ∘ per rule:
                dec-map … ∘ termProbe P              -- the terminal
                dec-⊗-cuts cat …                     -- search the cuts
                  ∘ per cut: dec-elim probe-NE …     -- the resource test
                      ∘ dec-&ᴰ                       -- the two components
                                                     --   of a slot

  Three things are NOT combinators, and each is named and typed with
  `⊢`:

      rollD / unrollD  -- the description's fixed point, as maps of the
                          calculus.  `Inductive`'s header says these must
                          be defined per instance, because `⟦_⟧c` and `μ`
                          sit at different levels generically; here they
                          are one line each.
      neOf             -- `SlotG Q ⊢ NonEmpty`, the resource certificate
                          a slot carries, read off by `&ᴰ-E`.  A TERM.
      neOfSh           -- the same certificate read off a SHAPE, which is
                          what the guardedness proof needs.  Phase 1, and
                          the only place a `Sh` is looked at.

  The search over cuts is `dec-⊗-cuts`, which is `Enumerable.decΣ` and
  is the SAME combinator as `dec-⊕ᴰ`: `⊗ˢ` over the splittings and `⊕ᴰ`
  over the rules are both `Σ`s, and both are decided by walking a
  complete list.  The list of cuts (`Spans.Base.allCuts`) is the one
  external residue, and it is an induction on a NUMBER.

  WHY THE RECURSION GOES THROUGH.  `dec-⊗-cuts` asks for a decision of
  each cut AS A WHOLE, not of each slot separately -- and that is what
  makes the guarded call legal.  At a cut with an empty side, the cut is
  refuted outright, because `neOf` says every slot certifies its own span
  to be non-empty; at a cut with neither side empty, `cutL<` / `cutR<`
  say both sides are strictly shorter, so `rec` applies.  A slotwise
  decision (`DecEnumerable.decAt`) could do neither: it would have to
  decide the left slot at a cut where the left slot is the whole span.
  "CNF has no ε-productions, therefore CYK terminates" is exactly this
  paragraph.
-}
module TheoryGrammar.Instances.Spans.CYK where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Unit
open import Cubical.Data.List

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded
open import TheoryGrammar.Enumerable
open import TheoryGrammar.Decidable.Enumerated
open import TheoryGrammar.Decidable.Guarded

open import TheoryGrammar.Instances.Spans.Enumeration public
open import TheoryGrammar.Instances.Spans.Schedule using (spanSched)

-- the cut search, and the two abbreviations its hypothesis is stated in
open DecEnum  spanFib    using (⊗at; Refutes; dec-⊗-cuts; slotMiss)
open DecGuard spanGraded
  using (SortFam; ▷ᴬ; ▷ᴾ; ▷ᴬ→▷ᴾ; löbᵍ; dec-⊗▷ᴾ; resourceOf; module Tab)

module CYK (V : Type₀)
           (unitR : V → ℕ → Type₀)          -- P derives the terminal at j
           (binR  : V → V → V → Type₀) where -- P → Q T

  -- the descriptions are indexed by the CFG's own non-terminals
  module G = Guard spanGraded ℓ-zero V (λ _ → tt)

  -- The terminal alternative, as a grammar: this span is a UNIT span at
  -- some position, and P derives the terminal sitting there.
  UnitG : V → SpanG
  UnitG P = ⊕ᴰ ℕ (λ j → ⌈ (j , 1) ⌉ & (λ _ → unitR P j))

  Rule : V → Type₀
  Rule P = Unit ⊎ (Σ[ Q ∈ V ] Σ[ T ∈ V ] binR P Q T)

  -- A recursive occurrence together with a proof its span is non-empty.
  -- That proof is what makes the SIBLING slot proper, and CNF's ban on
  -- ε-productions is exactly what supplies it.
  NEslot : V → Bool → G.Functor tt
  NEslot Q true  = G.Var Q
  NEslot Q false = G.⌜ NonEmpty ⌝

  NEvar : V → G.Functor tt
  NEvar Q = G.&e Bool (NEslot Q)

  binSlot : V → V → Bool → G.Functor tt
  binSlot Q T true  = NEvar Q
  binSlot Q T false = NEvar T

  ruleF : (P : V) → Rule P → G.Functor tt
  ruleF P (inl _)           = G.⌜ UnitG P ⌝
  ruleF P (inr (Q , T , _)) = G.⊗e cat (binSlot Q T)

  CYKF : (P : V) → G.Functor tt
  CYKF P = G.⊕e (Rule P) (ruleF P)

  -- THE PARSE TREES of a span from P, as a grammar over SPANS.
  Deriv : V → SpanG
  Deriv P s = G.μ CYKF (P , s)

  Der : G.Ix → Type₀
  Der = G.μ CYKF

  -- ================================================================
  -- THE DESCRIPTION, READ AS CONNECTIVES.
  --
  -- `⟦_⟧c` (Inductive) is the description spelled in the connectives:
  -- `⊕e` IS `⊕ᴰ`, `&e` IS `&ᴰ`, `⊗e` IS `⊗ˢ`, `⌜_⌝` IS `Liftg`, all
  -- DEFINITIONALLY.  So the three abbreviations below are grammars, and
  -- the equations
  --
  --     Layer P        ≡ ⊕ᴰ (Rule P) (RuleG P)
  --     RuleG P (inl _) ≡ Liftg (UnitG P)
  --     RuleG P (inr _) ≡ SlotG Q ⊗ᶜ SlotG T
  --     SlotG Q        ≡ &ᴰ Bool (λ b → …)   -- Deriv Q, and its resource
  --
  -- hold on the nose.  That is what lets `dec-⊕ᴰ` / `dec-⊗-cuts` /
  -- `dec-&ᴰ` be applied to a DESCRIPTION with no coercion anywhere.
  -- ================================================================

  Layer : V → SpanG
  Layer P = G.⟦ CYKF P ⟧c Der

  RuleG : (P : V) → Rule P → SpanG
  RuleG P r = G.⟦ ruleF P r ⟧c Der

  SlotG : V → SpanG
  SlotG Q = G.⟦ NEvar Q ⟧c Der

  binSlots : V → V → Bool → SpanG
  binSlots Q T a = G.⟦ binSlot Q T a ⟧c Der

  -- ================================================================
  -- THE FIXED POINT, as maps of the calculus.
  --
  -- `Inductive` explains why `rollg`/`unrollg` cannot be stated
  -- generically (a level stratification, not a mathematical
  -- obstruction) and says to define them per instance, where the levels
  -- are concrete.  Here `ℓμ = ℓSh = ℓ-zero`, so they are one line each,
  -- and they are the ONLY place `sup` / `toC` / `fromC` appear.
  -- ================================================================

  unrollD : (P : V) → Deriv P ⊢ Layer P
  unrollD P s t = G.toC (CYKF P) s (G.unroll t)

  rollD : (P : V) → Layer P ⊢ Deriv P
  rollD P s t = G.roll (G.fromC (CYKF P) s t)

  -- ================================================================
  -- THE RESOURCE CERTIFICATE A SLOT CARRIES -- a term.
  --
  -- `NEslot Q false = ⌜ NonEmpty ⌝`, so projecting the `false` component
  -- of a slot and discharging the constant former's `Lift` says: a slot
  -- of a binary rule certifies ITS OWN span to be non-empty.  This one
  -- term is the whole content of "CNF has no ε-productions", and it is
  -- `&ᴰ-E` followed by `lowerg`.
  -- ================================================================

  neOf : (Q : V) → SlotG Q ⊢ NonEmpty
  neOf Q = lowerg ∘g &ᴰ-E Bool {B = λ b → G.⟦ NEslot Q b ⟧c Der} false

  derOf : (Q : V) → SlotG Q ⊢ Deriv Q
  derOf Q = &ᴰ-E Bool {B = λ b → G.⟦ NEslot Q b ⟧c Der} true

  -- ================================================================
  -- Guardedness -- i.e. the chart is filled by increasing span length.
  --
  -- PRIMITIVE (phase 1): `neOfSh` is `neOf` at the level of SHAPES,
  -- which is where guardedness lives (`Guarded` is stated with
  -- `Sh`/`Pos`/`nx`).  It is the only place in the file a shape is
  -- looked at, and it is the shape analogue of a term that already
  -- exists -- not an extra assumption.
  -- ================================================================

  neOfSh : (Q : V) (s : Span) → G.Sh (NEvar Q) s → NonEmpty s
  neOfSh Q s sh = lower (sh false)

  ≤NEslot : (Q : V) (b : Bool) → G.Guarded≤ (NEslot Q b)
  ≤NEslot Q true  = G.≤Var Q
  ≤NEslot Q false = G.≤⌜⌝ NonEmpty

  ≤binSlot : (Q T : V) (b : Bool) → G.Guarded≤ (binSlot Q T b)
  ≤binSlot Q T true  = G.≤&e Bool (NEslot Q) (≤NEslot Q)
  ≤binSlot Q T false = G.≤&e Bool (NEslot T) (≤NEslot T)

  cykGuarded : (P : V) → G.Guarded (CYKF P)
  cykGuarded P = G.<⊕e (Rule P) (ruleF P) alt
    where
      -- properness of a slot is non-emptiness of its COMPLEMENT, so each
      -- slot's certificate comes from its SIBLING's `NonEmpty` component
      pr : (Q T : V) (s : Span) (c : SpanSplit cat s)
           (sh : (a : Bool) → G.Sh (binSlot Q T a) (SpanParts cat s c a))
           (a : Bool) → G.Pos (binSlot Q T a) _ (sh a) → SpanProper cat s c a
      pr Q T s c sh true  p = neOfSh T (SpanParts cat s c false) (sh false)
      pr Q T s c sh false p = neOfSh Q (SpanParts cat s c true)  (sh true)

      alt : (r : Rule P) → G.Guarded (ruleF P r)
      alt (inl _)           = G.<⌜⌝ (UnitG P)
      alt (inr (Q , T , _)) =
        G.<⊗e cat (binSlot Q T) (≤binSlot Q T) (pr Q T)

  -- ================================================================
  -- THE DECISION PROCEDURE.
  --
  -- `allRules` / `allComplete` say the grammar is finite; `termProbe`
  -- is the lexical table, and it is given as an INTERNAL probe --
  -- `⊤G ⊢ Dec⟨ UnitG P ⟩` -- not as a metalanguage `Dec`.  That is the
  -- same discipline as `Strings.Examples.decEqS`: external decidability
  -- enters once, at a named place, to build an internal map.
  -- ================================================================

  module Decide (allRules    : (P : V) → List (Rule P))
                (allComplete : (P : V) (r : Rule P) → r ∈L allRules P)
                (termProbe   : (P : V) → Probe (UnitG P)) where

    -- ================================================================
    -- THE CHART, AS A GRAMMAR.
    --
    -- The motive is `&ᴰ V (λ P → Dec⟨ Deriv P ⟩)` -- one grammar holding
    -- the decision for EVERY nonterminal at the current span.  That is
    -- the whole trick: an `Ix`-family (`V × Span → Type`) is not a
    -- grammar and has no combinators, so a step written against one is
    -- forced to be pointful.  A `&ᴰ` over the nonterminals IS a grammar,
    -- so `▷ᴾ Chart ⊢ Chart` is a map of the calculus and every layer
    -- below composes with `∘g`.
    -- ================================================================

    Chart : SpanG
    Chart = &ᴰ V (λ P → Dec⟨ Deriv P ⟩)

    ChartF : SortFam ℓ-zero
    ChartF _ = Chart

    -- reading one nonterminal out of the chart
    chartAt : (P : V) → Chart ⊢ Dec⟨ Deriv P ⟩
    chartAt P = &ᴰ-E V {B = λ Q → Dec⟨ Deriv Q ⟩} P

    -- the terminal alternative.  `Liftg` is the constant former's
    -- coercion and `dec-map` transports the decision across it.
    decUnit : (P : V) → Probe (Liftg (UnitG P))
    decUnit P = dec-map (UnitG P) (Liftg (UnitG P)) liftg lowerg ∘g termProbe P

    -- ONE SLOT, from the chart at that slot.  A slot is a `&ᴰ Bool` of
    -- the nonterminal and its resource certificate, so `dec-&ᴰ` decides
    -- it from the two components -- the chart for the first, `probe-NE`
    -- for the second.  A map, not an element.
    decSlot : (Q : V) → Chart ⊢ Dec⟨ SlotG Q ⟩
    decSlot Q =
      dec-&ᴰ (λ b → G.⟦ NEslot Q b ⟧c Der)
      ∘g &ᴰ-I {B = λ b → Dec⟨ G.⟦ NEslot Q b ⟧c Der ⟩}
               λ { true  → chartAt Q
                 ; false → dec-map NonEmpty (Liftg NonEmpty) liftg lowerg
                           ∘g probe-NE ∘g ⊤-I }

    -- ================================================================
    -- ... AND EVERYTHING BELOW IS A MAP.
    --
    -- The cut's resource test used to be written here by hand, as the
    -- file's one non-`⊢` definition.  It is now DERIVED by
    -- `resourceOf` from three inputs: `probe-NE` and `neOf`, which are
    -- terms, and `neProper`, which is a law of the grading (`Spans.
    -- Graded`) of the same kind as `deg<`.  Nothing in this module
    -- mentions a cut.
    -- ================================================================

    -- a binary rule: scan the cuts, with the chart available LATER
    decBin : (Q T : V) → ▷ᴾ ChartF ⊢ Dec⟨ ⊗ˢ cat (binSlots Q T) ⟩
    decBin Q T =
      dec-⊗▷ᴾ cat (binSlots Q T) ChartF
             (λ s → allCuts (s .snd)) (λ s → allCutsComplete (s .snd))
             (resourceOf cat (binSlots Q T) (λ _ → NonEmpty) (λ _ → probe-NE)
                         (λ { true → neOf Q ; false → neOf T })
                         neProper catAr catArComplete)
             (spanDecAt cat (binSlots Q T))
             λ { true → decSlot Q ; false → decSlot T }

    decRule : (P : V) (r : Rule P) → ▷ᴾ ChartF ⊢ Dec⟨ RuleG P r ⟩
    decRule P (inl _)           = decUnit P ∘g ⊤-I
    decRule P (inr (Q , T , _)) = decBin Q T

    -- one nonterminal's row: search the rules with `dec-⊕ᴰ`, then
    -- transport the decision across the fixed point with `dec-map`
    decNT : (P : V) → ▷ᴾ ChartF ⊢ Dec⟨ Deriv P ⟩
    decNT P =
      dec-map (Layer P) (Deriv P) (rollD P) (unrollD P)
      ∘g dec-⊕ᴰ (Rule P) (RuleG P) (allRules P) (allComplete P)
      ∘g &ᴰ-I {B = λ r → Dec⟨ RuleG P r ⟩} (decRule P)

    -- THE LÖB STEP, a term of the calculus.  No index is matched, no
    -- Agda function is handed to `löb`, and nothing below `decUnit` /
    -- `spanResource` is an element rather than a map.
    step : ▷ᴾ ChartF ⊢ Chart
    step = &ᴰ-I {B = λ P → Dec⟨ Deriv P ⟩} decNT

    -- ================================================================
    -- ... AND THE CHART IS TABULATED.
    --
    -- `löbᵀ` is `löbᵍ` with the `later` supplied by a `DP.Chain` rather
    -- than by re-descent: the same `step` above, solved against
    -- `Spans.Schedule`'s enumeration of the subspans of the root.  The
    -- ONLY thing that changes is that the answers so far are DATA --
    -- forced once and projected -- so a long span consulting a short
    -- one costs an address rather than a recomputation.
    --
    -- `DecGuard.löbᵀ≡` (via `DP.solveAt≡`) proves this is the same
    -- answer `löbᵍ` gave, so no pinned test in `Tests` / `Bench` is a
    -- check on semantics; they check the WIRING.
    -- ================================================================

    private module T = Tab ChartF

    chart : Cover Chart
    chart = T.löbᵀ (λ _ → step) (spanSched T.Motive) tt

    -- THE UNTABULATED REFERENCE, kept for measurement and for reading.
    -- `löbᵍ` solves the SAME `step`; `▷ᴬ→▷ᴾ` is the only glue, because
    -- the degree later is the stronger one.  So the difference between
    -- this and `chart` above is EXACTLY the representative of the
    -- `later` -- a Π versus a table -- and nothing else, which is the
    -- claim `DP`'s header makes and this pair of lines exhibits.
    chartLöb : Cover Chart
    chartLöb = löbᵍ ChartF (λ _ → step ∘g ▷ᴬ→▷ᴾ ChartF) tt

    -- THE PROCEDURE: at every span, a parse tree from P or a refutation
    -- of every parse tree from P.  A composite of two terms.
    derives? : (P : V) → Probe (Deriv P)
    derives? P = chartAt P ∘g chart

    -- and it composes with the rest of the probe family, because it IS
    -- one of them -- e.g. "this span is a P or a Q"
    private
      _ : (P Q : V) → Probe (Deriv P ⊕ Deriv Q)
      _ = λ P Q → probe-⊕ (Deriv P) (Deriv Q) (derives? P) (derives? Q)
