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

open import TheoryGrammar.Instances.Spans.Graded public

-- the cut search, and the two abbreviations its hypothesis is stated in
open DecEnum spanFib using (⊗at; Refutes; dec-⊗-cuts; slotMiss)

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

    DecMot : G.Ix → Type₀
    DecMot i = Dec⟨ Deriv (i .fst) ⟩ (i .snd)

    -- the terminal alternative, decided.  `Liftg` is the constant
    -- former's coercion and `dec-map` transports the decision across it,
    -- so this is a composite of terms.
    decUnit : (P : V) → Probe (Liftg (UnitG P))
    decUnit P = dec-map (UnitG P) (Liftg (UnitG P)) liftg lowerg ∘g termProbe P

    module _ (P : V) (i n : ℕ)
             (rec : (j : G.Ix) → G.degIx j < n → DecMot j) where

      private
        s : Span
        s = i , n

      module _ (Q T : V) (c : Cut n) where

        private
          sL sR : Span
          sL = SpanParts cat s c true
          sR = SpanParts cat s c false

          CutDec : Type₀
          CutDec = ⊗at cat (binSlots Q T) s c
                 ⊎ Refutes cat (binSlots Q T) s c

          -- an empty side refutes the cut, because `neOf` says the slot
          -- sitting there certifies its own span to be non-empty.
          -- `slotMiss` is the generic "a slot refuted refutes the cut";
          -- its only argument is the term `neOf`, so nothing pointful is
          -- written here.
          missL : (¬G NonEmpty) sL → Refutes cat (binSlots Q T) s c
          missL = slotMiss cat (binSlots Q T) s c true  NonEmpty (neOf Q)

          missR : (¬G NonEmpty) sR → Refutes cat (binSlots Q T) s c
          missR = slotMiss cat (binSlots Q T) s c false NonEmpty (neOf T)

          -- neither side empty: each side is then a PROPER part, and
          -- `deg<` -- the grading's own field -- says a proper part is
          -- strictly smaller, which is exactly what `▷` demands.  So
          -- nothing here knows what a cut is; `cutL<` / `cutR<` / `neLen`
          -- are used only to BUILD `spanGraded`, never to use it.  Each
          -- slot is a `&ᴰ` of its nonterminal and its certificate,
          -- decided by `dec-&ᴰ`.
          slotDec : (R : V) (t : Span) → G.degIx (R , t) < n → NonEmpty t
                  → Dec⟨ SlotG R ⟩ t
          slotDec R t shorter ne =
            dec-&ᴰ (λ b → G.⟦ NEslot R b ⟧c Der) t
              λ { true  → rec (R , t) shorter
                ; false → dec-yes (Liftg NonEmpty) t (liftg {A = NonEmpty} t ne) }

          -- `decΠBool` is the arity-finiteness concession, the same one
          -- `DecEnumerable.decAt` makes: the two slots sit at DIFFERENT
          -- spans, so combining them is not a `&ᴰ` of the calculus.
          both : NonEmpty sL → NonEmpty sR → CutDec
          both neL neR =
            decΠBool {B = λ a → binSlots Q T a (SpanParts cat s c a)}
              (slotDec Q sL (spanGraded .deg< cat s c true  neR) neL)
              (slotDec T sR (spanGraded .deg< cat s c false neL) neR)

        -- THE CUT, decided.  Two nested `dec-elim`s on the resource
        -- probe -- an instance never matches a sum, it eliminates one.
        decCut : CutDec
        decCut =
          dec-elim NonEmpty sL
            (λ neL → dec-elim NonEmpty sR
                       (λ neR → both neL neR)
                       (λ k → inr (missR k))
                       (probe-NE sR tt))
            (λ k → inr (missL k))
            (probe-NE sL tt)

      -- one rule, decided: the terminal alternative, or a search over
      -- the cuts.  `allCuts` / `allCutsComplete` are the file's only
      -- external residue, and they are an induction on a NUMBER.
      decRule : (r : Rule P) → Dec⟨ RuleG P r ⟩ s
      decRule (inl _)           = decUnit P s tt
      decRule (inr (Q , T , _)) =
        dec-⊗-cuts cat (binSlots Q T) s (allCuts n) (allCutsComplete n)
                   (decCut Q T)

      -- ... and the whole layer: search the rules with `dec-⊕ᴰ`, then
      -- transport the decision across the fixed point with `dec-map`.
      decStep : DecMot (P , s)
      decStep =
        dec-map (Layer P) (Deriv P) (rollD P) (unrollD P) s
          (dec-⊕ᴰ (Rule P) (RuleG P) (allRules P) (allComplete P) s decRule)

    -- THE LÖB STEP, as a named `▷ … ⊢ᴵ …` term: projections only, no
    -- match on the index, and no Agda function smuggled into `löb`.
    step : G.▷ DecMot G.⊢ᴵ DecMot
    step i rec = decStep (i .fst) (i .snd .fst) (i .snd .snd) rec

    decIx : (i : G.Ix) → DecMot i
    decIx = G.löb step

    -- THE PROCEDURE, as a term of the calculus: at every span, a parse
    -- tree from P or a refutation of every parse tree from P.
    derives? : (P : V) → Probe (Deriv P)
    derives? P s _ = decIx (P , s)

    -- and it composes with the rest of the probe family, because it IS
    -- one of them -- e.g. "this span is a P or a Q"
    private
      _ : (P Q : V) → Probe (Deriv P ⊕ Deriv Q)
      _ = λ P Q → probe-⊕ (Deriv P) (Deriv Q) (derives? P) (derives? Q)
