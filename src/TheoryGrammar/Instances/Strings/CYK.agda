{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- A context-free grammar in Chomsky normal form IS a description, with the
   non-terminals as the description's non-terminals. -}
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
open DecGuard strGraded
  using (SortFam; ▷ᴬ; ▷ᴾ; ▷ᴬ→▷ᴾ; löbᵍ; dec-⊗▷ᴾ; resourceOf; World; module TabΠ)

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

  -- THE DESCRIPTION, READ AS CONNECTIVES. `⟦_⟧c` (Inductive) is the
  -- description spelled in the connectives: `⊕e` IS `⊕ᴰ`, `&e` IS `&ᴰ`,
  -- `⊗e` IS `⊗ˢ`, `⌜_⌝` IS `Liftg`, all DEFINITIONALLY.

  Layer : V → Gr
  Layer P = G.⟦ CYKF P ⟧c Der

  RuleG : (P : V) → Rule P → Gr
  RuleG P r = G.⟦ ruleF P r ⟧c Der

  SlotG : V → Gr
  SlotG Q = G.⟦ NEvar Q ⟧c Der

  binSlots : V → V → Bool → Gr
  binSlots Q T a = G.⟦ binSlot Q T a ⟧c Der

  -- THE FIXED POINT, as maps of the calculus.

  -- the fixed point, as maps of the calculus.  Both come from
  -- `Guard` now (`TheoryGrammar.Grading`); they used to be written
  -- out here, pointfully, in this and three sibling files.
  unrollD : (P : V) → Deriv P ⊢ Layer P
  unrollD P = G.unrollg CYKF P

  rollD : (P : V) → Layer P ⊢ Deriv P
  rollD P = G.rollg CYKF P

  -- THE RESOURCE CERTIFICATE A SLOT CARRIES -- a term.

  neOf : (Q : V) → SlotG Q ⊢ NonTrivial
  neOf Q = lowerg ∘g &ᴰ-E Bool {B = λ b → G.⟦ NEslot Q b ⟧c Der} false

  derOf : (Q : V) → SlotG Q ⊢ Deriv Q
  derOf Q = &ᴰ-E Bool {B = λ b → G.⟦ NEslot Q b ⟧c Der} true

  -- Guardedness. Both slots of a binary rule are proper parts, so this is
  -- the uniform rule -- CNF is precisely the shape that makes it so.

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

-- Every word is trivial or not. This IS the decomposition axiom with its
-- branches swapped -- no argument left to make, because the resource
-- predicate is defined as the non-trivial branch.
decNT : Cover (NonTrivial ⊕ ⌈ [] ⌉)
decNT = caseOf charCase ⊕-I₂ ⊕-I₁

-- PRIMITIVE (phase 1): the empty word is trivial.  The only fact about
-- the resource predicate that is not already a term.
¬NT[] : No (NonTrivial [])
¬NT[] (c , (u , v , s) , h) = go (h true) s
  where go : u Eq.≡ c ∷ [] → Split3 u v [] → E.⊥* {ℓ-zero}
        go Eq.refl ()

-- ... so non-triviality is DECIDED, as an internal probe: the cover
-- `decNT` says every word is trivial or not, and `¬NT[]` turns the trivial
-- branch into a refutation.
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

  -- THE PARSER. The SAME term as `Decide` below, at the error grammar `⊤G`
  -- instead of `¬G _`, and with every completeness hypothesis deleted:
  -- mapR ⊤G (Deriv P) (rollD P) ∘ maybe-⊕ᴰ (Rule P) … -- search the rules
  -- (Result) ∘ per rule: mapR … ∘ matchLit c -- the terminal findΣ (cuts
  -- w) … -- search the...

  -- THE DECISION, as maps of the calculus. The motive is `&ᴰ V (λ P → Dec⟨
  -- Deriv P ⟩)` -- ONE GRAMMAR holding the decision for every nonterminal
  -- at the current word.

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

    -- a binary rule: scan the cuts, chart available LATER.
    decBin : (Q T : V) → ▷ᴾ ChartF ⊢ Dec⟨ ⊗ˢ appop (binSlots Q T) ⟩
    decBin Q T =
      dec-⊗▷ᴾ appop (binSlots Q T) ChartF
             cuts (enumComplete appop)
             (resourceOf appop (binSlots Q T) (λ _ → NonTrivial) (λ _ → probe-NT)
                         (λ { true → neOf Q ; false → neOf T })
                         ntProper appAr appArComplete)
             (λ m sp d → decΠBool (d true) (d false))   -- arity is finite
             λ { true → decSlot Q ; false → decSlot T }

    decRule : (P : V) (r : Rule P) → ▷ᴾ ChartF ⊢ Dec⟨ RuleG P r ⟩
    decRule P (inl (c , _))     = decLit c ∘g ⊤-I
    decRule P (inr (Q , T , _)) = decBin Q T

    decRow : (P : V) → ▷ᴾ ChartF ⊢ Dec⟨ Deriv P ⟩
    decRow P =
      dec-map (Layer P) (Deriv P) (rollD P) (unrollD P)
      ∘g dec-⊕ᴰ (Rule P) (RuleG P) (allRules P) (allComplete P)
      ∘g &ᴰ-I {B = λ r → Dec⟨ RuleG P r ⟩} (decRule P)

    -- THE LÖB STEP, a term.  No index matched, no Agda function fed to
    -- `löb`, no element where a map belongs.
    step : ▷ᴾ ChartF ⊢ Chart
    step = &ᴰ-I {B = λ P → Dec⟨ Deriv P ⟩} decRow

    -- `löbᵍ` still solves it: `▷ᴬ` is the STRONGER later, so a step
    -- written against `▷ᴾ` may be run by either.
    chart : Cover Chart
    chart = löbᵍ ChartF (λ _ → step ∘g ▷ᴬ→▷ᴾ ChartF) tt

    -- THE SHARED CHART -- everything except the schedule.

    module Shared (allV : List V)
                  (allVComplete : (P : V) → P ∈L allV) where

      private module TΠ = TabΠ V (λ P _ → Dec⟨ Deriv P ⟩) allV allVComplete

      -- THE MISSING PIECE, as a type. Design notes, so the next attempt
      -- does not rediscover them: THE LAYOUT.
      StrSchedule : Type _
      StrSchedule = (w : World) → TΠ.SchedQ w

      chartD : StrSchedule → Cover Chart
      chartD sch = TΠ.löbᴰ (λ _ → step) sch tt

      derivesD? : StrSchedule → (P : V) → Probe (Deriv P)
      derivesD? sch P = chartAt P ∘g chartD sch

    derives? : (P : V) → Probe (Deriv P)
    derives? P = chartAt P ∘g chart

    -- ... and the exclusion is free, so it packages as a `Decision`
    derivesDec : (P : V) → Decision (Deriv P) (¬G (Deriv P))
    derivesDec P = decDefault (Deriv P) (derives? P)

    -- THE PARSER is the decision, FORGOTTEN. `Dec⟨ A ⟩` is `Result (¬G A)
    -- A` and `MaybeG A` is `Result ⊤G A`, so `toMaybe` -- `mapE ⊤-I`,
    -- uniform in the error grammar -- is the whole of it.

    parse : (P : V) → Cover (MaybeG (Deriv P))
    parse P = toMaybe (Deriv P) ∘g derives? P
