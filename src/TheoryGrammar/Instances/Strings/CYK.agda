{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- A context-free grammar in Chomsky normal form IS a description, with
   the non-terminals as the description's non-terminals.  So `Deriv P` --
   the parse trees of `w` from `P` -- is the generic `μ`, a grammar, and
   not a `List` of non-terminal names. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Strings.CYK (Char : Type₀) where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.List
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded

open import TheoryGrammar.Enumerable
open import TheoryGrammar.Decidable.Guarded
import TheoryGrammar.Decidable.Enumerated as DE
open DE using (module DecEnum)
open import TheoryGrammar.Instances.Strings.Enumeration Char public

-- the cut search, and the two abbreviations its hypothesis is stated in
open DecEnum  strFib    using (⊗at; Refutes; dec-⊗-cuts; slotMiss)
open DecGuard strGraded using (SortFam; ▷ᴬ; löbᵍ; dec-⊗▷; resourceOf)

-- `¬G_` and `Dec⟨_⟩` are the generic ones (`Decidable.Additive`, via
-- `DecFib` in `Strings.Base`); this instance defines neither.

module CYK (V : Type₀)
           (unitR : V → Char → Type₀)          -- P → c
           (binR  : V → V → V → Type₀) where   -- P → Q T

  -- the descriptions are indexed by the CFG's own non-terminals
  module G = Guard strGraded ℓ-zero V (λ _ → tt)

  Rule : V → Type₀
  Rule P = (Σ[ c ∈ Char ] unitR P c) ⊎ (Σ[ Q ∈ V ] Σ[ T ∈ V ] binR P Q T)

  -- A recursive occurrence together with a proof its part is non-empty.
  -- That proof is what makes the splitting proper, and CNF's ban on
  -- ε-productions is exactly what supplies it.
  NEslot : V → Bool → G.Functor tt
  NEslot Q true  = G.Var Q
  NEslot Q false = G.⌜ NonTrivial ⌝

  NEvar : V → G.Functor tt
  NEvar Q = G.&e Bool (NEslot Q)

  binSlot : V → V → Bool → G.Functor tt
  binSlot Q T true  = NEvar Q
  binSlot Q T false = NEvar T

  ruleF : (P : V) → Rule P → G.Functor tt
  ruleF P (inl (c , _))     = G.⌜ ⌈ c ∷ [] ⌉ ⌝
  ruleF P (inr (Q , T , _)) = G.⊗e appop (binSlot Q T)

  CYKF : (P : V) → G.Functor tt
  CYKF P = G.⊕e (Rule P) (ruleF P)

  -- THE PARSE TREES of `w` from `P`, as a grammar
  Deriv : V → Gr
  Deriv P w = G.μ CYKF (P , w)

  Der : G.Ix → Type₀
  Der = G.μ CYKF

  -- ================================================================
  -- THE DESCRIPTION, READ AS CONNECTIVES.
  --
  -- `⟦_⟧c` (Inductive) is the description spelled in the connectives:
  -- `⊕e` IS `⊕ᴰ`, `&e` IS `&ᴰ`, `⊗e` IS `⊗ˢ`, `⌜_⌝` IS `Liftg`, all
  -- DEFINITIONALLY.  So the abbreviations below are grammars, and
  --
  --     Layer P         ≡ ⊕ᴰ (Rule P) (RuleG P)
  --     RuleG P (inl _) ≡ Liftg ⌈ c ∷ [] ⌉
  --     RuleG P (inr _) ≡ SlotG Q ⊗' SlotG T
  --     SlotG Q         ≡ &ᴰ Bool (λ b → …)   -- Deriv Q, and its resource
  --
  -- hold on the nose.  That is what lets the generic `dec-⊕ᴰ` /
  -- `dec-⊗-cuts` / `dec-&ᴰ` be applied to a DESCRIPTION with no
  -- coercion anywhere.
  -- ================================================================

  Layer : V → Gr
  Layer P = G.⟦ CYKF P ⟧c Der

  RuleG : (P : V) → Rule P → Gr
  RuleG P r = G.⟦ ruleF P r ⟧c Der

  SlotG : V → Gr
  SlotG Q = G.⟦ NEvar Q ⟧c Der

  binSlots : V → V → Bool → Gr
  binSlots Q T a = G.⟦ binSlot Q T a ⟧c Der

  -- ================================================================
  -- THE FIXED POINT, as maps of the calculus.  `Inductive` explains why
  -- `rollg`/`unrollg` cannot be stated generically (a level
  -- stratification, not a mathematical obstruction) and says to define
  -- them per instance, where the levels are concrete.  These are the
  -- only place `sup` / `toC` / `fromC` appear outside `leaf` / `node`.
  -- ================================================================

  unrollD : (P : V) → Deriv P ⊢ Layer P
  unrollD P w t = G.toC (CYKF P) w (G.unroll t)

  rollD : (P : V) → Layer P ⊢ Deriv P
  rollD P w t = G.roll (G.fromC (CYKF P) w t)

  -- ================================================================
  -- THE RESOURCE CERTIFICATE A SLOT CARRIES -- a term.
  --
  -- `NEslot Q false = ⌜ NonTrivial ⌝`, so projecting the `false`
  -- component of a slot and discharging the constant former's `Lift`
  -- says: a slot of a binary rule certifies ITS OWN part to be
  -- non-trivial.  This one term is the whole content of "CNF has no
  -- ε-productions", and it is `&ᴰ-E` followed by `lowerg`.
  -- ================================================================

  neOf : (Q : V) → SlotG Q ⊢ NonTrivial
  neOf Q = lowerg ∘g &ᴰ-E Bool {B = λ b → G.⟦ NEslot Q b ⟧c Der} false

  derOf : (Q : V) → SlotG Q ⊢ Deriv Q
  derOf Q = &ᴰ-E Bool {B = λ b → G.⟦ NEslot Q b ⟧c Der} true

  -- ================================================================
  -- Guardedness.  Both slots of a binary rule are proper parts, so this
  -- is the uniform rule -- CNF is precisely the shape that makes it so.
  --
  -- PRIMITIVE (phase 1): `neOfSh` is `neOf` at the level of SHAPES,
  -- which is where guardedness lives (`Guarded` is stated with
  -- `Sh`/`Pos`/`nx`).  It is the only place a shape is looked at, and it
  -- is the shape analogue of a term that already exists.
  -- ================================================================

  neOfSh : (Q : V) (w : String) → G.Sh (NEvar Q) w → NonTrivial w
  neOfSh Q w sh = lower (sh false)

  ≤NEslot : (Q : V) (b : Bool) → G.Guarded≤ (NEslot Q b)
  ≤NEslot Q true  = G.≤Var Q
  ≤NEslot Q false = G.≤⌜⌝ NonTrivial

  ≤binSlot : (Q T : V) (b : Bool) → G.Guarded≤ (binSlot Q T b)
  ≤binSlot Q T true  = G.≤&e Bool (NEslot Q) (≤NEslot Q)
  ≤binSlot Q T false = G.≤&e Bool (NEslot T) (≤NEslot T)

  cykGuarded : (P : V) → G.Guarded (CYKF P)
  cykGuarded P = G.<⊕e (Rule P) (ruleF P) alt
    where
      pr : (Q T : V) (m : String) (sp : MonSplit appop m)
           (sh : (a : Bool) → G.Sh (binSlot Q T a) (MonParts appop m sp a))
           (a : Bool) → G.Pos (binSlot Q T a) _ (sh a) → StrProper appop m sp a
      pr Q T m sp sh true  p = neOfSh T (MonParts appop m sp false) (sh false)
      pr Q T m sp sh false p = neOfSh Q (MonParts appop m sp true)  (sh true)

      alt : (r : Rule P) → G.Guarded (ruleF P r)
      alt (inl (c , _))     = G.<⌜⌝ ⌈ c ∷ [] ⌉
      alt (inr (Q , T , _)) =
        G.<⊗e appop (binSlot Q T) (≤binSlot Q T) (pr Q T)

-- Every word is trivial or not.  This IS the decomposition axiom with
-- its branches swapped -- no argument left to make, because the
-- resource predicate is defined as the non-trivial branch.
--
-- `caseOf` is `withView` at `B = ⊤G`, where the payload is vacuous and
-- the `with` degenerates to `_∘g_`.  Every view used at `⊤` has this
-- shape; see `TheoryGrammar.View`.
decNT : Cover (NonTrivial ⊕ ⌈ [] ⌉)
decNT = caseOf charCase ⊕-I₂ ⊕-I₁

-- PRIMITIVE (phase 1): the empty word is trivial.  The only fact about
-- the resource predicate that is not already a term.
¬NT[] : No (NonTrivial [])
¬NT[] (c , (u , v , s) , h) = go (h true) s
  where go : u Eq.≡ c ∷ [] → Split3 u v [] → E.⊥* {ℓ-zero}
        go Eq.refl ()

-- ... so non-triviality is DECIDED, as an internal probe: the cover
-- `decNT` says every word is trivial or not, and `¬NT[]` turns the
-- trivial branch into a refutation.  `⌈⌉-E` is what carries a fact
-- known at ONE world to a map out of that world's representable, so
-- this is a composite of combinators and one primitive.
probe-NT : Probe NonTrivial
probe-NT = caseOf decNT
             (dec-yes NonTrivial)
             (⌈⌉-E {a = []} {B = Dec⟨ NonTrivial ⟩} (dec-no NonTrivial [] ¬NT[]))

module Parser (V : Type₀)
              (unitR : V → Char → Type₀)
              (binR  : V → V → V → Type₀) where

  open CYK V unitR binR public

  -- the two constructors of a parse tree, as terms
  leaf : {P : V} {w : String} (c : Char) → unitR P c
       → w Eq.≡ c ∷ [] → Deriv P w
  leaf c pf q = G.sup (inl (c , pf) , lift q) λ ()

  node : {P Q T : V} {w u v : String} → binR P Q T → Split3 u v w
       → NonTrivial u → NonTrivial v → Deriv Q u → Deriv T v → Deriv P w
  node {Q = Q} {T} {u = u} {v} pf s neu nev tq tT =
    G.sup ( inr (Q , T , pf)
          , ((u , v , s) , λ { true  → λ { true → tt* ; false → lift neu }
                             ; false → λ { true → tt* ; false → lift nev } }) )
          λ { (true  , (true  , _)) → tq
            ; (false , (true  , _)) → tT
            ; (true  , (false , ()))
            ; (false , (false , ())) }

  -- ================================================================
  -- THE PARSER.  The SAME term as `Decide` below, at the error grammar
  -- `⊤G` instead of `¬G _`, and with every completeness hypothesis
  -- deleted:
  --
  --     mapR ⊤G (Deriv P) (rollD P)
  --       ∘ maybe-⊕ᴰ (Rule P) …          -- search the rules   (Result)
  --           ∘ per rule:
  --               mapR … ∘ matchLit c            -- the terminal
  --               findΣ (cuts w) …               -- search the cuts
  --                 ∘ per cut: dec-elim probe-NT …
  --                     ∘ findΠBool               -- the two slots
  --
  -- `findΣ` / `findΠBool` are `decΣ` / `decΠBool` with the refutations
  -- dropped (`TheoryGrammar.Enumerable`), and `maybe-⊕ᴰ` is `dec-⊕ᴰ`
  -- with the completeness proof dropped.  A parser may drop them
  -- because it claims nothing when it fails; a decision may not.  That
  -- is the entire difference between `parse` and `derives?`, and it now
  -- shows up in which arguments the two take.
  --
  -- `allRules` says the grammar is finite; `matchLit` is the literal
  -- matcher, itself a term of the calculus.
  -- ================================================================

  -- ================================================================
  -- THE DECISION, as maps of the calculus.
  --
  -- The motive is `&ᴰ V (λ P → Dec⟨ Deriv P ⟩)` -- ONE GRAMMAR holding
  -- the decision for every nonterminal at the current word.  An
  -- `Ix`-family (`V × String → Type`) is not a grammar and has no
  -- combinators, so a step written against one is forced to be
  -- pointful; a `&ᴰ` over the nonterminals IS a grammar, so
  -- `▷ᴬ Chart ⊢ Chart` is a term and every layer composes with `∘g`.
  --
  -- This is `Instances.Spans.CYK.Decide` verbatim with `appop` for
  -- `cat` and `NonTrivial` for `NonEmpty`; that the two are the same
  -- term over two different theories is the point of the exercise.
  -- ================================================================

  module Decide (allRules    : (P : V) → List (Rule P))
                (allComplete : (P : V) (r : Rule P) → r ∈L allRules P)
                (litProbe    : (c : Char) → Probe ⌈ c ∷ [] ⌉) where

    Chart : Gr
    Chart = &ᴰ V (λ P → Dec⟨ Deriv P ⟩)

    ChartF : SortFam ℓ-zero
    ChartF _ = Chart

    chartAt : (P : V) → Chart ⊢ Dec⟨ Deriv P ⟩
    chartAt P = &ᴰ-E V {B = λ Q → Dec⟨ Deriv Q ⟩} P

    -- the terminal alternative; `Liftg` is the constant former's coercion
    decLit : (c : Char) → Probe (Liftg ⌈ c ∷ [] ⌉)
    decLit c = dec-map ⌈ c ∷ [] ⌉ (Liftg ⌈ c ∷ [] ⌉) liftg lowerg ∘g litProbe c

    -- ONE SLOT: a `&ᴰ Bool` of the nonterminal and its resource
    -- certificate, decided from the chart and `probe-NT`.
    decSlot : (Q : V) → Chart ⊢ Dec⟨ SlotG Q ⟩
    decSlot Q =
      dec-&ᴰ (λ b → G.⟦ NEslot Q b ⟧c Der)
      ∘g &ᴰ-I {B = λ b → Dec⟨ G.⟦ NEslot Q b ⟧c Der ⟩}
               λ { true  → chartAt Q
                 ; false → dec-map NonTrivial (Liftg NonTrivial) liftg lowerg
                           ∘g probe-NT ∘g ⊤-I }

    -- a binary rule: scan the cuts, chart available LATER.  The cut's
    -- resource test is DERIVED by `resourceOf` from `probe-NT` and
    -- `neOf` (terms) plus `ntProper` (a law of the grading, like
    -- `deg<`), so nothing here mentions a cut.
    decBin : (Q T : V) → ▷ᴬ ChartF ⊢ Dec⟨ ⊗ˢ appop (binSlots Q T) ⟩
    decBin Q T =
      dec-⊗▷ appop (binSlots Q T) ChartF
             cuts (enumComplete appop)
             (resourceOf appop (binSlots Q T) (λ _ → NonTrivial) (λ _ → probe-NT)
                         (λ { true → neOf Q ; false → neOf T })
                         ntProper appAr appArComplete)
             (λ m sp d → decΠBool (d true) (d false))   -- arity is finite
             λ { true → decSlot Q ; false → decSlot T }

    decRule : (P : V) (r : Rule P) → ▷ᴬ ChartF ⊢ Dec⟨ RuleG P r ⟩
    decRule P (inl (c , _))     = decLit c ∘g ⊤-I
    decRule P (inr (Q , T , _)) = decBin Q T

    decRow : (P : V) → ▷ᴬ ChartF ⊢ Dec⟨ Deriv P ⟩
    decRow P =
      dec-map (Layer P) (Deriv P) (rollD P) (unrollD P)
      ∘g dec-⊕ᴰ (Rule P) (RuleG P) (allRules P) (allComplete P)
      ∘g &ᴰ-I {B = λ r → Dec⟨ RuleG P r ⟩} (decRule P)

    -- THE LÖB STEP, a term.  No index matched, no Agda function fed to
    -- `löb`, no element where a map belongs.
    step : ▷ᴬ ChartF ⊢ Chart
    step = &ᴰ-I {B = λ P → Dec⟨ Deriv P ⟩} decRow

    chart : Cover Chart
    chart = löbᵍ ChartF (λ _ → step) tt

    derives? : (P : V) → Probe (Deriv P)
    derives? P = chartAt P ∘g chart

    -- ... and the exclusion is free, so it packages as a `Decision`
    derivesDec : (P : V) → Decision (Deriv P) (¬G (Deriv P))
    derivesDec P = decDefault (Deriv P) (derives? P)

    -- ================================================================
    -- THE PARSER is the decision, FORGOTTEN.
    --
    -- `Dec⟨ A ⟩` is `Result (¬G A) A` and `MaybeG A` is `Result ⊤G A`,
    -- so `toMaybe` -- `mapE ⊤-I`, uniform in the error grammar -- is the
    -- whole of it.  The old `Search` module reimplemented the recursion
    -- at `MaybeG`; it was pointful, and it was also redundant.
    --
    -- What is genuinely lost is that a parser needs no completeness
    -- proof (`Result.maybe-⊕ᴰ` and `Enumerable.findΣ` still record
    -- that), so this `parse` assumes more than it must.  It assumes it
    -- INTERNALLY, which is the trade that matters here.
    -- ================================================================

    parse : (P : V) → Cover (MaybeG (Deriv P))
    parse P = toMaybe (Deriv P) ∘g derives? P
