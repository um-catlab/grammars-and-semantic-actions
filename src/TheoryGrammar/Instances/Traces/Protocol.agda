{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  A PROTOCOL LOG, PARSED AS A SHUFFLE.

  The claim this file exists to test is:

      "this log is a valid interleaving of N concurrent sessions,
       each individually following the protocol"

  is a CFG parsing problem -- the SAME one CYK solves -- once the
  decomposition operator of the promodel is interleaving instead of
  concatenation.  Nothing about the algorithm changes.  What changes is
  `Fibered .Split`, and it changed once, in `Traces/Base`.

  ==================================================================
  THE ALPHABET IS A CONCURRENT ALPHABET.

  An event is a session id and an action, and the independence relation
  is

      Ind (i , a) (j , b)  =  i ≠ j

  -- events of DIFFERENT sessions commute, events of the SAME session do
  not.  That single line does two jobs at once, and they are the two
  halves of the specification:

    * ACROSS sessions, `ITr Ind u v w` is full interleaving, so
      `Session₀ ⊗' Session₁` says exactly "w is some interleaving of a
      session-0 trace and a session-1 trace".

    * WITHIN a session, no `right` step is licensed, so `ITr Ind` on
      same-session factors is concatenation and `open ⊗' body` really
      does force the open to come FIRST.

  So one `⊗ˢ appop` is read as "concurrent composition" at the top of
  the grammar and as "sequencing" inside a session, and which one it is
  is decided by the alphabet, not by the grammar.  `ProtocolTests` pins
  both halves, and the second one is pinned by a CONTROL: `Over` below
  is parameterised by the independence relation, so `ProtocolTests`
  can run the identical grammar and the identical decision procedure at
  `⊤I` and watch it accept a log in which a session closes before it
  opens (`Control.wrong-at-⊤`).

  ==================================================================
  THE PROTOCOL.

      Session i  ->  open_i  Body_i
      Body_i     ->  send_i  Body_i  |  close_i
      Log        ->  Session_0  Session_1

  in Chomsky normal form, as a `Rule`/`unitR`/`binR` triple -- the
  identical interface `Instances.Strings.CYK` and `Instances.Spans.CYK`
  take.  The last production is the whole exercise: over strings it
  would say "session 0's events all precede session 1's", and over
  traces it says "the two sessions are interleaved arbitrarily".

  ==================================================================
  WHAT IS NEW HERE AND WHAT IS NOT.  See the closing note in
  `ProtocolTests`; briefly, the only genuinely new mathematics is the
  four length lemmas about `ITr` that make `trGraded` a grading.  The
  enumeration of splittings -- the expensive part, and the one a
  hand-written interleaving parser would spend all its effort on -- was
  already `Traces/Enumeration.shuffles`, written for another purpose.

  DEFINES the concurrent alphabet (`Sid`/`Act`/`Ev`/`Ind`) and, inside
  `module Over` -- parameterised by the independence relation -- the
  grading `trGraded`, the resource predicate `NonTrivial` with its
  probe, the CYK module over the trace promodel, the protocol grammar
  `NT`, the decision `derives?`, and the specification term
  `logIsShuffle`.  `Conc` is `Over` at the concurrent alphabet and is
  re-exported unqualified; `Full` is `Over` at `⊤I`, the control.
-}
module TheoryGrammar.Instances.Traces.Protocol where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.List
open import Cubical.Data.List.Properties using (discreteList)
open import Cubical.Data.Empty as E using (⊥)
open import Cubical.Relation.Nullary.Base using (Discrete; decRec; yes; no)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded
open import TheoryGrammar.View
open import TheoryGrammar.Enumerable
open import TheoryGrammar.Decidable.Representable
open import TheoryGrammar.Decidable.Guarded
import TheoryGrammar.Decidable.Enumerated as DE
open DE using (module DecEnum)

import TheoryGrammar.Instances.Traces.Enumeration as TrEnum

-- ==================================================================
-- THE CONCURRENT ALPHABET.
-- ==================================================================

data Sid : Type₀ where
  s₀ s₁ : Sid

data Act : Type₀ where
  opn msg cls : Act

Ev : Type₀
Ev = Sid × Act

-- `Diff i j` DENOTES "different sessions".  Symmetric and irreflexive,
-- which is what an independence alphabet wants.
Diff : Sid → Sid → Type₀
Diff s₀ s₀ = ⊥
Diff s₀ s₁ = Unit
Diff s₁ s₀ = Unit
Diff s₁ s₁ = ⊥

-- THE INDEPENDENCE RELATION.  Concurrency, spelled once.
Ind : Ev → Ev → Type₀
Ind e f = Diff (e .fst) (f .fst)

decDiff : (i j : Sid) → Diff i j ⊎ No (Diff i j)
decDiff s₀ s₀ = inr λ ()
decDiff s₀ s₁ = inl tt
decDiff s₁ s₀ = inl tt
decDiff s₁ s₁ = inr λ ()

decInd : (e f : Ev) → Ind e f ⊎ No (Ind e f)
decInd e f = decDiff (e .fst) (f .fst)

isPropDiff : (i j : Sid) → isProp (Diff i j)
isPropDiff s₀ s₀ = E.isProp⊥
isPropDiff s₀ s₁ = isPropUnit
isPropDiff s₁ s₀ = isPropUnit
isPropDiff s₁ s₁ = E.isProp⊥

isPropInd : (e f : Ev) → isProp (Ind e f)
isPropInd e f = isPropDiff (e .fst) (f .fst)

-- External decidability of the alphabet, used ONLY to build the
-- internal literal probe below.  `SidCode`/`ActCode` are the usual
-- encode-decode families; nothing here is specific to this development.
SidCode : Sid → Sid → Type₀
SidCode s₀ s₀ = Unit
SidCode s₁ s₁ = Unit
SidCode _  _  = ⊥

ActCode : Act → Act → Type₀
ActCode opn opn = Unit
ActCode msg msg = Unit
ActCode cls cls = Unit
ActCode _   _   = ⊥

discreteSid : Discrete Sid
discreteSid s₀ s₀ = yes refl
discreteSid s₁ s₁ = yes refl
discreteSid s₀ s₁ = no λ p → subst (SidCode s₀) p tt
discreteSid s₁ s₀ = no λ p → subst (SidCode s₁) p tt

discreteAct : Discrete Act
discreteAct opn opn = yes refl
discreteAct msg msg = yes refl
discreteAct cls cls = yes refl
discreteAct opn msg = no λ p → subst (ActCode opn) p tt
discreteAct opn cls = no λ p → subst (ActCode opn) p tt
discreteAct msg opn = no λ p → subst (ActCode msg) p tt
discreteAct msg cls = no λ p → subst (ActCode msg) p tt
discreteAct cls opn = no λ p → subst (ActCode cls) p tt
discreteAct cls msg = no λ p → subst (ActCode cls) p tt

discreteEv : Discrete Ev
discreteEv (i , x) (j , y) =
  decRec (λ p → decRec (λ q → yes (cong₂ _,_ p q))
                       (λ ¬q → no λ r → ¬q (cong snd r))
                       (discreteAct x y))
         (λ ¬p → no λ r → ¬p (cong fst r))
         (discreteSid i j)

-- ==================================================================
-- THE WHOLE DEVELOPMENT, OVER AN ARBITRARY INDEPENDENCE RELATION.
--
-- Everything below -- the grading, the resource probe, CYK, the
-- protocol grammar and its decision -- depends on the alphabet's
-- INDEPENDENCE RELATION only through `Traces/Base`'s `Split`.  So it is
-- a module in that relation, and the file ends by instantiating it
-- twice:
--
--     Conc = Over Ind …    events of different sessions commute
--     Full = Over ⊤I  …    EVERYTHING commutes
--
-- `Conc` is the protocol parser.  `Full` is a control: the same grammar,
-- the same decision procedure, one different `Fibered`.  `ProtocolTests`
-- runs both at the same log and gets different answers, which is what
-- turns "the independence relation is doing the work" from a remark
-- into a theorem.
-- ==================================================================

module Over (I : Ev → Ev → Type₀)
            (decI : (e f : Ev) → I e f ⊎ No (I e f))
            (isPropI : (e f : Ev) → isProp (I e f)) where

  -- ==================================================================
  -- The trace promodel at this alphabet, and the view combinators.
  -- ==================================================================

  open TrEnum Ev I decI isPropI public
  open Views trFib public

  -- ==================================================================
  -- THE GRADING.  `deg = length`, and the four length lemmas about the
  -- shuffle relation.  These four inductions are the ONLY facts this file
  -- proves that `Instances.Strings.Graded` did not already prove for
  -- concatenation; the shapes are identical, with the extra `right`
  -- constructor handled exactly as `left` is on the other side.
  -- ==================================================================

  itrLenL : ∀ {u v w} → ITr I u v w → length u ≤ length w
  itrLenL nil         = zero-≤
  itrLenL (left s)    = suc-≤-suc (itrLenL s)
  itrLenL (right _ s) = ≤-suc (itrLenL s)

  itrLenR : ∀ {u v w} → ITr I u v w → length v ≤ length w
  itrLenR nil         = zero-≤
  itrLenR (left s)    = ≤-suc (itrLenR s)
  itrLenR (right _ s) = suc-≤-suc (itrLenR s)

  itrLenL< : ∀ {u v w} → ITr I u v w → 0 < length v → length u < length w
  itrLenL< nil         pr = pr
  itrLenL< (left s)    pr = suc-≤-suc (itrLenL< s pr)
  itrLenL< (right _ s) pr = suc-≤-suc (itrLenL s)

  itrLenR< : ∀ {u v w} → ITr I u v w → 0 < length u → length v < length w
  itrLenR< nil         pr = pr
  itrLenR< (left s)    pr = suc-≤-suc (itrLenR s)
  itrLenR< (right _ s) pr = suc-≤-suc (itrLenR< s pr)

  -- THE RESOURCE PREDICATE, internally: `w` is non-trivial when it
  -- decomposes with an ATOM on the left.  Character for character
  -- `Instances.Strings.Graded.NonTrivial` -- it is `⌈_⌉`, `⊗'`, `⊕ᴰ` and
  -- `⊤` only, so it makes sense at any promodel with atoms, and at THIS
  -- one it still says "w has at least one event".
  NonTrivial : Gr
  NonTrivial = ⊕ᴰ Ev (λ e → ⌈ e ∷ [] ⌉ ⊗' ⊤G)

  -- PRIMITIVE (phase 1).  The ONE bridge from the internal predicate to
  -- the grading.
  ntLen : {v : Word} → NonTrivial v → 0 < length v
  ntLen {v} (e , (u' , v' , s) , h) = go (h true) s
    where go : u' Eq.≡ e ∷ [] → ITr I u' v' v → 0 < length v
          go Eq.refl s' = itrLenL s'

  TrProper : (o : MonOp) (m : Word) → MonSplit o m → MonAr o → Type₀
  TrProper nilop m sp ()
  TrProper appop w (u , v , _) b = NonTrivial (if b then v else u)

  trGraded : GradedFib monoidSig ℓ-zero ℓ-zero
  trGraded .fib    = trFib
  trGraded .deg _  = length
  trGraded .Proper = TrProper
  trGraded .deg≤ nilop m sp ()
  trGraded .deg≤ appop m (u , v , s) true  = itrLenL s
  trGraded .deg≤ appop m (u , v , s) false = itrLenR s
  trGraded .deg< nilop m sp ()
  trGraded .deg< appop m (u , v , s) true  pr = itrLenL< s (ntLen pr)
  trGraded .deg< appop m (u , v , s) false pr = itrLenR< s (ntLen pr)

  -- THE RESOURCE LAW: properness of a slot IS non-triviality of its
  -- complement.  Verbatim `Strings.Graded.ntProper`.
  ntProper : (w : Word) (sp : MonSplit appop w)
           → ((a : Bool) → NonTrivial (MonParts appop w sp a))
           → (a : Bool) → TrProper appop w sp a
  ntProper w sp h true  = h false
  ntProper w sp h false = h true

  appAr : List Bool
  appAr = true ∷ false ∷ []

  appArComplete : (a : Bool) → a ∈L appAr
  appArComplete true  = here
  appArComplete false = there here

  -- ==================================================================
  -- THE DECOMPOSITION VIEW, and the probe it decides.
  --
  -- The one place a word is destructured.  `left (itrNil I w)` is the
  -- shuffle that takes the head into the left factor and everything else
  -- into the right, and it needs no independence -- once the left factor
  -- is exhausted, `itrNil` walks the rest unconditionally.
  -- ==================================================================

  trCase : Cover (⌈ [] ⌉ ⊕ NonTrivial)
  trCase []      _ = inl Eq.refl
  trCase (e ∷ w) _ = inr (e , ⊗-mk (left (itrNil I w)) Eq.refl tt)

  -- PRIMITIVE (phase 1): the empty trace is trivial.
  ¬NT[] : No (NonTrivial [])
  ¬NT[] (e , (u , v , s) , h) = go (h true) s
    where go : u Eq.≡ e ∷ [] → ITr I u v [] → E.⊥* {ℓ-zero}
          go Eq.refl ()

  probe-NT : Probe NonTrivial
  probe-NT =
    caseOf trCase
      (⌈⌉-E {a = []} {B = Dec⟨ NonTrivial ⟩} (dec-no NonTrivial [] ¬NT[]))
      (dec-yes NonTrivial)

  -- The level coercion the constant former `⌜_⌝` of a description carries
  -- (`Inductive.⟦ ⌜ B ⌝ ⟧c A w = Lift _ (B w)`).  Pure bookkeeping;
  -- `Strings/Connectives` has the same three lines and `Traces/Base` chose
  -- not to, so they are here.
  Liftg : Gr → Gr
  Liftg A w = Lift ℓ-zero (A w)

  liftg : {A : Gr} → A ⊢ Liftg A
  liftg _ = lift

  lowerg : {A : Gr} → Liftg A ⊢ A
  lowerg _ = lower

  -- the cut search, and the two abbreviations its hypothesis is stated in
  open DecEnum  trFib    using (⊗at; Refutes; dec-⊗-cuts; slotMiss)
  open DecGuard trGraded using (SortFam; ▷ᴬ; löbᵍ; dec-⊗▷; resourceOf)

  -- ==================================================================
  -- CYK, OVER THE TRACE PROMODEL.
  --
  -- `Instances.Strings.CYK` with `strGraded` replaced by `trGraded` and
  -- the cut enumeration `cuts` replaced by `shuffles`.  Every other
  -- token is the same, including `NonTrivial`, `ntProper`, `appAr` and
  -- the whole of `Decide`.  `Decidable.Guarded`'s closing note says the
  -- chart cannot yet be assembled generically (an `Ix`-family is not a
  -- grammar), so this module is the third copy of the same forty lines,
  -- not a reuse -- see the accounting in `ProtocolTests`.
  -- ==================================================================

  module CYK (V : Type₀)
             (unitR : V → Ev → Type₀)          -- P -> e
             (binR  : V → V → V → Type₀) where -- P -> Q T

    module G = Guard trGraded ℓ-zero V (λ _ → tt)

    Rule : V → Type₀
    Rule P = (Σ[ e ∈ Ev ] unitR P e) ⊎ (Σ[ Q ∈ V ] Σ[ T ∈ V ] binR P Q T)

    -- A recursive occurrence together with a proof its part is non-empty.
    -- CNF's ban on ε-productions is what supplies it, and it is what makes
    -- the SIBLING slot a proper part.
    NEslot : V → Bool → G.Functor tt
    NEslot Q true  = G.Var Q
    NEslot Q false = G.⌜ NonTrivial ⌝

    NEvar : V → G.Functor tt
    NEvar Q = G.&e Bool (NEslot Q)

    binSlot : V → V → Bool → G.Functor tt
    binSlot Q T true  = NEvar Q
    binSlot Q T false = NEvar T

    ruleF : (P : V) → Rule P → G.Functor tt
    ruleF P (inl (e , _))     = G.⌜ ⌈ e ∷ [] ⌉ ⌝
    ruleF P (inr (Q , T , _)) = G.⊗e appop (binSlot Q T)

    CYKF : (P : V) → G.Functor tt
    CYKF P = G.⊕e (Rule P) (ruleF P)

    -- THE PARSE TREES of `w` from `P`, as a grammar over TRACES.
    Deriv : V → Gr
    Deriv P w = G.μ CYKF (P , w)

    Der : G.Ix → Type₀
    Der = G.μ CYKF

    Layer : V → Gr
    Layer P = G.⟦ CYKF P ⟧c Der

    RuleG : (P : V) → Rule P → Gr
    RuleG P r = G.⟦ ruleF P r ⟧c Der

    SlotG : V → Gr
    SlotG Q = G.⟦ NEvar Q ⟧c Der

    binSlots : V → V → Bool → Gr
    binSlots Q T a = G.⟦ binSlot Q T a ⟧c Der

    -- the fixed point, as maps of the calculus
    unrollD : (P : V) → Deriv P ⊢ Layer P
    unrollD P w t = G.toC (CYKF P) w (G.unroll t)

    rollD : (P : V) → Layer P ⊢ Deriv P
    rollD P w t = G.roll (G.fromC (CYKF P) w t)

    -- the resource certificate a slot carries -- a term
    neOf : (Q : V) → SlotG Q ⊢ NonTrivial
    neOf Q = lowerg ∘g &ᴰ-E Bool {B = λ b → G.⟦ NEslot Q b ⟧c Der} false

    derOf : (Q : V) → SlotG Q ⊢ Deriv Q
    derOf Q = &ᴰ-E Bool {B = λ b → G.⟦ NEslot Q b ⟧c Der} true

    -- PRIMITIVE (phase 1): the same certificate at the level of SHAPES,
    -- which is where guardedness lives.
    neOfSh : (Q : V) (w : Word) → G.Sh (NEvar Q) w → NonTrivial w
    neOfSh Q w sh = lower (sh false)

    ≤NEslot : (Q : V) (b : Bool) → G.Guarded≤ (NEslot Q b)
    ≤NEslot Q true  = G.≤Var Q
    ≤NEslot Q false = G.≤⌜⌝ NonTrivial

    ≤binSlot : (Q T : V) (b : Bool) → G.Guarded≤ (binSlot Q T b)
    ≤binSlot Q T true  = G.≤&e Bool (NEslot Q) (≤NEslot Q)
    ≤binSlot Q T false = G.≤&e Bool (NEslot T) (≤NEslot T)

    -- THE TERMINATION ARGUMENT.  Identical to the string one, and it is
    -- worth saying why it survives: a shuffle's two factors are both
    -- SUBWORDS, so both are no longer than the whole, and a factor whose
    -- complement is non-empty is strictly shorter.  Interleaving reorders
    -- the events but cannot duplicate them, which is exactly what
    -- `itrLenL`/`itrLenR` say.
    cykGuarded : (P : V) → G.Guarded (CYKF P)
    cykGuarded P = G.<⊕e (Rule P) (ruleF P) alt
      where
        pr : (Q T : V) (m : Word) (sp : MonSplit appop m)
             (sh : (a : Bool) → G.Sh (binSlot Q T a) (MonParts appop m sp a))
             (a : Bool) → G.Pos (binSlot Q T a) _ (sh a) → TrProper appop m sp a
        pr Q T m sp sh true  p = neOfSh T (MonParts appop m sp false) (sh false)
        pr Q T m sp sh false p = neOfSh Q (MonParts appop m sp true)  (sh true)

        alt : (r : Rule P) → G.Guarded (ruleF P r)
        alt (inl (e , _))     = G.<⌜⌝ ⌈ e ∷ [] ⌉
        alt (inr (Q , T , _)) =
          G.<⊗e appop (binSlot Q T) (≤binSlot Q T) (pr Q T)

    -- ================================================================
    -- THE DECISION, as maps of the calculus.  `Instances.Spans.CYK.Decide`
    -- and `Instances.Strings.CYK.Decide` verbatim; the ONE argument that
    -- differs from the string version is `shuffles` where that one passes
    -- `cuts`.
    -- ================================================================

    module Decide (allRules    : (P : V) → List (Rule P))
                  (allComplete : (P : V) (r : Rule P) → r ∈L allRules P)
                  (litProbe    : (e : Ev) → Probe ⌈ e ∷ [] ⌉) where

      Chart : Gr
      Chart = &ᴰ V (λ P → Dec⟨ Deriv P ⟩)

      ChartF : SortFam ℓ-zero
      ChartF _ = Chart

      chartAt : (P : V) → Chart ⊢ Dec⟨ Deriv P ⟩
      chartAt P = &ᴰ-E V {B = λ Q → Dec⟨ Deriv Q ⟩} P

      decLit : (e : Ev) → Probe (Liftg ⌈ e ∷ [] ⌉)
      decLit e = dec-map ⌈ e ∷ [] ⌉ (Liftg ⌈ e ∷ [] ⌉) liftg lowerg ∘g litProbe e

      decSlot : (Q : V) → Chart ⊢ Dec⟨ SlotG Q ⟩
      decSlot Q =
        dec-&ᴰ (λ b → G.⟦ NEslot Q b ⟧c Der)
        ∘g &ᴰ-I {B = λ b → Dec⟨ G.⟦ NEslot Q b ⟧c Der ⟩}
                 λ { true  → chartAt Q
                   ; false → dec-map NonTrivial (Liftg NonTrivial) liftg lowerg
                             ∘g probe-NT ∘g ⊤-I }

      -- A BINARY RULE: scan the SHUFFLES, with the chart available LATER.
      -- This is the only line in the module that knows what the
      -- decomposition operator is.
      decBin : (Q T : V) → ▷ᴬ ChartF ⊢ Dec⟨ ⊗ˢ appop (binSlots Q T) ⟩
      decBin Q T =
        dec-⊗▷ appop (binSlots Q T) ChartF
               shuffles (enumComplete appop)
               (resourceOf appop (binSlots Q T) (λ _ → NonTrivial) (λ _ → probe-NT)
                           (λ { true → neOf Q ; false → neOf T })
                           ntProper appAr appArComplete)
               (λ m sp d → decΠBool (d true) (d false))
               λ { true → decSlot Q ; false → decSlot T }

      decRule : (P : V) (r : Rule P) → ▷ᴬ ChartF ⊢ Dec⟨ RuleG P r ⟩
      decRule P (inl (e , _))     = decLit e ∘g ⊤-I
      decRule P (inr (Q , T , _)) = decBin Q T

      decRow : (P : V) → ▷ᴬ ChartF ⊢ Dec⟨ Deriv P ⟩
      decRow P =
        dec-map (Layer P) (Deriv P) (rollD P) (unrollD P)
        ∘g dec-⊕ᴰ (Rule P) (RuleG P) (allRules P) (allComplete P)
        ∘g &ᴰ-I {B = λ r → Dec⟨ RuleG P r ⟩} (decRule P)

      step : ▷ᴬ ChartF ⊢ Chart
      step = &ᴰ-I {B = λ P → Dec⟨ Deriv P ⟩} decRow

      chart : Cover Chart
      chart = löbᵍ ChartF (λ _ → step) tt

      derives? : (P : V) → Probe (Deriv P)
      derives? P = chartAt P ∘g chart

      derivesDec : (P : V) → Decision (Deriv P) (¬G (Deriv P))
      derivesDec P = decDefault (Deriv P) (derives? P)

  -- ==================================================================
  -- THE PROTOCOL, IN CHOMSKY NORMAL FORM.
  --
  --     Log    ->  SessA SessB
  --     SessA  ->  OpnA BodyA          SessB  ->  OpnB BodyB
  --     BodyA  ->  MsgA BodyA | 'c₀'   BodyB  ->  MsgB BodyB | 'c₁'
  --     OpnA   ->  'o₀'   MsgA -> 'm₀'
  --     OpnB   ->  'o₁'   MsgB -> 'm₁'
  -- ==================================================================

  data NT : Type₀ where
    log                   : NT
    sessA bodyA opnA msgA : NT
    sessB bodyB opnB msgB : NT

  -- the terminal productions
  unitR : NT → Ev → Type₀
  unitR opnA  e = e Eq.≡ (s₀ , opn)
  unitR msgA  e = e Eq.≡ (s₀ , msg)
  unitR bodyA e = e Eq.≡ (s₀ , cls)
  unitR opnB  e = e Eq.≡ (s₁ , opn)
  unitR msgB  e = e Eq.≡ (s₁ , msg)
  unitR bodyB e = e Eq.≡ (s₁ , cls)
  unitR log   e = ⊥
  unitR sessA e = ⊥
  unitR sessB e = ⊥

  -- The binary productions.  Every nonterminal of this grammar has AT
  -- MOST ONE of them, so the relation is presented as a partial function
  -- -- `Bin` says whether the production exists and `lhs`/`rhs` name its
  -- two children.  Nothing about CYK requires this; it is what makes
  -- `allComplete` nine clauses rather than ninety, because matching
  -- `Eq.refl` determines both children at once.
  Bin : NT → Type₀
  Bin log   = Unit
  Bin sessA = Unit
  Bin bodyA = Unit
  Bin sessB = Unit
  Bin bodyB = Unit
  Bin opnA  = ⊥
  Bin msgA  = ⊥
  Bin opnB  = ⊥
  Bin msgB  = ⊥

  lhs : NT → NT
  lhs log   = sessA
  lhs sessA = opnA
  lhs bodyA = msgA
  lhs sessB = opnB
  lhs bodyB = msgB
  lhs opnA  = log
  lhs msgA  = log
  lhs opnB  = log
  lhs msgB  = log

  rhs : NT → NT
  rhs log   = sessB
  rhs sessA = bodyA
  rhs bodyA = bodyA
  rhs sessB = bodyB
  rhs bodyB = bodyB
  rhs opnA  = log
  rhs msgA  = log
  rhs opnB  = log
  rhs msgB  = log

  binR : NT → NT → NT → Type₀
  binR P Q T = Bin P × (Q Eq.≡ lhs P) × (T Eq.≡ rhs P)

  open CYK NT unitR binR public

  allRules : (P : NT) → List (Rule P)
  allRules log   = inr (sessA , sessB , (tt , Eq.refl , Eq.refl)) ∷ []
  allRules sessA = inr (opnA  , bodyA , (tt , Eq.refl , Eq.refl)) ∷ []
  allRules bodyA = inl ((s₀ , cls) , Eq.refl)
                 ∷ inr (msgA , bodyA , (tt , Eq.refl , Eq.refl)) ∷ []
  allRules opnA  = inl ((s₀ , opn) , Eq.refl) ∷ []
  allRules msgA  = inl ((s₀ , msg) , Eq.refl) ∷ []
  allRules sessB = inr (opnB  , bodyB , (tt , Eq.refl , Eq.refl)) ∷ []
  allRules bodyB = inl ((s₁ , cls) , Eq.refl)
                 ∷ inr (msgB , bodyB , (tt , Eq.refl , Eq.refl)) ∷ []
  allRules opnB  = inl ((s₁ , opn) , Eq.refl) ∷ []
  allRules msgB  = inl ((s₁ , msg) , Eq.refl) ∷ []

  allComplete : (P : NT) (r : Rule P) → r ∈L allRules P
  allComplete log   (inl (e , ()))
  allComplete log   (inr (Q , T , (tt , Eq.refl , Eq.refl))) = here
  allComplete sessA (inl (e , ()))
  allComplete sessA (inr (Q , T , (tt , Eq.refl , Eq.refl))) = here
  allComplete bodyA (inl (e , Eq.refl))                      = here
  allComplete bodyA (inr (Q , T , (tt , Eq.refl , Eq.refl))) = there here
  allComplete opnA  (inl (e , Eq.refl))                      = here
  allComplete opnA  (inr (Q , T , (() , _)))
  allComplete msgA  (inl (e , Eq.refl))                      = here
  allComplete msgA  (inr (Q , T , (() , _)))
  allComplete sessB (inl (e , ()))
  allComplete sessB (inr (Q , T , (tt , Eq.refl , Eq.refl))) = here
  allComplete bodyB (inl (e , Eq.refl))                      = here
  allComplete bodyB (inr (Q , T , (tt , Eq.refl , Eq.refl))) = there here
  allComplete opnB  (inl (e , Eq.refl))                      = here
  allComplete opnB  (inr (Q , T , (() , _)))
  allComplete msgB  (inl (e , Eq.refl))                      = here
  allComplete msgB  (inr (Q , T , (() , _)))

  -- external decidability enters ONCE, here, to build an internal map
  private
    module TrR = DecRep (trFib .carrier)

  discreteWord : Discrete Word
  discreteWord = discreteList discreteEv

  litProbe : (e : Ev) → Probe ⌈ e ∷ [] ⌉
  litProbe e = TrR.dec-⌈⌉ discreteWord (e ∷ [])

  open Decide allRules allComplete litProbe public

  -- ==================================================================
  -- THE SPECIFICATION, AS A TERM.
  --
  -- A derivation of `log` IS a shuffle of a session-0 derivation and a
  -- session-1 derivation -- and `⊗'` at this promodel is interleaving.
  -- So the statement "the log is a valid interleaving of the two
  -- sessions" is not a comment about what the decision procedure means;
  -- it is this type, and `logIsShuffle` is its proof.
  -- ==================================================================

  private
    logRule : (r : Rule log) → RuleG log r ⊢ ⊗ˢ appop (binSlots sessA sessB)
    logRule (inl (e , ()))
    logRule (inr (Q , T , (tt , Eq.refl , Eq.refl))) = idg

  logIsShuffle : Deriv log ⊢ (SlotG sessA ⊗' SlotG sessB)
  logIsShuffle =
    ⊗ˢ-map appop {A = binSlots sessA sessB}
                 {B = λ b → if b then SlotG sessA else SlotG sessB}
                 (λ { true → idg ; false → idg })
    ∘g ⊕ᴰ-E logRule
    ∘g unrollD log

  -- ... and each factor really is a session derivation, with its
  -- non-emptiness certificate discarded
  sessionOf : (Q : NT) → SlotG Q ⊢ Deriv Q
  sessionOf = derOf

-- ==================================================================
-- THE TWO INSTANTIATIONS.
--
-- `Conc` is THE protocol parser and everything it defines is re-exported
-- unqualified.  `Full` is the ⊤-endpoint control -- the free
-- COMMUTATIVE monoid's splittings, which `Traces/Commutative` proves are
-- `Instances.Bags`' interleavings.  Its `derives?` is the same term; it
-- accepts more logs, and `ProtocolTests.wrong-at-⊤` exhibits one.
-- ==================================================================

⊤I : Ev → Ev → Type₀
⊤I _ _ = Unit

dec⊤I : (e f : Ev) → ⊤I e f ⊎ No (⊤I e f)
dec⊤I e f = inl tt

isProp⊤I : (e f : Ev) → isProp (⊤I e f)
isProp⊤I e f = isPropUnit

module Conc = Over Ind  decInd isPropInd
module Full = Over ⊤I   dec⊤I  isProp⊤I

open Conc public
