{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  ONE TEST SUITE, PARAMETRIC IN WHICH BACKENDS ARE SELECTED.

  ------------------------------------------------------------------
  WHAT THIS REPLACES
  ------------------------------------------------------------------

  `Compile/Showcase.agda` composes three backends through ONE observable
  (`LinLam.Codegen.layout u`) and reports agreement as `Eq.sym`/`Eq._∙_`.
  That works, and §7 of that file says exactly how far it goes: the three
  backends are USAGE-directed, `Simulation.noBlindBackend` refutes any
  computational theorem for them, so LAYOUT-level agreement is all they
  can have -- and the agreement is hard-wired, three named lemmas for
  three fixed backends.

  Here the backends are DATA.  A `Backend` is a record; a suite is a
  `List Backend`; and the same suite serves ARM alone, Rust alone, or
  both at once with no new code.  Two consequences that the hard-wired
  version could not have:

    * a DISAGREEMENT is a row of the report, not a typecheck failure --
      the user reads what each backend said and sees where they parted;
    * a DELIBERATELY BROKEN backend can be dropped into the list, and the
      harness's ability to see it is itself a checked theorem
      (`Compile/Suite/Tests.agda` §5).

  ------------------------------------------------------------------
  THE COMMON OBSERVABLE, AND WHY IT IS AS COARSE AS IT IS
  ------------------------------------------------------------------

  This is the part of the design that was MEASURED rather than chosen,
  and the measurement is worth more than the harness.

  The first attempt was the CAPTURE TREE: decode `IR.Val`'s `clos i vs`
  to `vclos vs` (dropping the block index, which `Correct.noNoseSquare`
  proves is a fact about one table and hence meaningless across two
  compilations), and decode a Rust answer `rClos n b` to `vclos (the
  topmost closure subterms of b)` -- Rust having substituted its captures
  inline rather than storing them.  That agrees on `idLin`, `selfApp`,
  `bigT` and `applyK`, and §5 of `Compile/Suite/Tests.agda` shows why
  that was luck: the GENERATOR immediately produced `λf. λx. f x`, where
  the two disagree 1 vs 0, and three more like it.

  THE CAPTURE COUNT IS NOT AN INVARIANT, and `Correct.agda` says so in
  one constructor.  `RelE`'s

      rcap : RelV T t (σ (slotOf 0 u s')) → RelE T σ t (ivar s')
             -- "the source substituted a value here; the target reads
                 the frame"

  IS the statement that substitution and environment-passing are the same
  thing only UP TO THE RELATION.  A closure-converted answer carries the
  free variables its block was compiled with; a substituting answer has
  none left, and carries its own nested λs instead.  No structural count
  -- captures, closure nodes, depth -- separates those two facts, because
  the difference between them is exactly what `RelV` exists to absorb.

  What IS shared is termination and the KIND of the answer:

      data Val = vfun     the target answered with a function
               | vstuck   ... with something that is not one

      Obs = Maybe Val     `nothing` = no answer within the budget

  so `Backend.obs : Tm [] → Obs` is `Correct.obs`'s type.  Coarse, and
  not vacuous: `vstuck` is what an OPEN term produces in `Codegen.agda`
  (a free `yp`, and `evalRust` sticks), it is what a MISCOMPILED binder
  produces, and `nothing` separates both from divergence.  §6 of the
  tests is the demonstration that it is sharp enough to catch a one-`suc`
  mutation of the Rust code generator.

  Anything finer belongs in a per-backend `refl` line -- and
  `Compile/Suite/Backends.agda` §4 keeps both native answers side by side,
  so what the observable forgets is still on the page.

  ------------------------------------------------------------------
  AGREEMENT IS A GRAMMAR, AND DISAGREEMENT IS A REFUTATION
  ------------------------------------------------------------------

  §3 is the part that matters.  `agreeOn t` is a `Bool`, and a `Bool` is
  not a test -- CLAUDE.md's rule is that `run f w ≡ false` is strictly
  weaker than what a decision proves.  So agreement is stated as a
  GRAMMAR and decided internally:

      Agree t   : Ctx                      -- "the selected backends
                                              agree on t, at the unit"
      agreeDec  : ⊤G ⊢ Dec⟨ Agree t ⟩      -- a DECISION, not a Bool
      agrees!   : Tm [] → Bool             -- ... observed by `okA`

  and then `SemanticAction.refute` turns a `refl`-checkable `≡ false`
  into the branch CONTENT, which at `E = ¬G (Agree t)` is a theorem:

      refuteAgree t : agrees! t ≡ false → (¬G (Agree t)) []

  A harness that can only say "the Bool was false" cannot distinguish
  "the backends differed" from "the harness did not look".  This one
  hands back a function that eats any purported agreement.

  `Agree t` is guarded by `⌈ [] ⌉` for the reason `Correct.ClosedTm` is:
  the backends compile CLOSED terms, and the internal way to say so is
  the representable at the unit of the usage monoid rather than a side
  condition.  `isNil` is what lets the decision be uniform in the world:
  away from `[]` the grammar is empty, and the refutation says so by
  matching the representable's `Eq.refl`.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1 throughout, and marked: `Backend` is a record of metalanguage
  functions (a backend IS a metalanguage function -- that is what makes
  it a backend), the decoders recurse on a target value, and `isNil` /
  `decB` are the two decidability primitives the internal decision is
  built from.  Everything from `agreeDec` down is `⊕-I₁`/`⊕-I₂` at a
  point plus `refute`, i.e. the calculus's own rules.
-}
open import Cubical.Foundations.Prelude

module Compile.Suite.Backend where

open import Agda.Builtin.String using (String)
open import Cubical.Data.Bool using (Bool; true; false; _and_)
open import Cubical.Data.List using (List; []; _∷_; map; _++_; length)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Theories.Monoid using (monoidSig)
import TheoryGrammar.Result           as TR
import TheoryGrammar.Decidable.Additive as TD
import TheoryGrammar.SemanticAction   as SA

-- the SOURCE, unqualified: this file writes grammars over `Usage`
open import TheoryGrammar.Instances.LinLam.Syntax

-- the additive layers at this theory
-- `Result` is already re-exported by `RulesF linFib` (Context.agda), so
-- only the decidability layer and the semantic-action layer are applied
-- here.  Same carrier, hence the same `CarrierNotation` application --
-- nothing below is ambiguous.
module LD = TD.DecAdd                    (linFib .carrier)
module LA = SA.Act {σ = monoidSig}       (linFib .carrier)

open LD using (¬G_; Dec⟨_⟩)

-- ==================================================================
-- §1  THE COMMON OBSERVABLE.
--
-- Termination, and the kind of the answer.  See the header: NOTHING
-- finer is invariant, and the reason is `Correct.RelE`'s `rcap` -- the
-- constructor that says substitution and environment-passing agree only
-- up to the realisation relation.
-- ==================================================================

data Val : Type₀ where
  vfun   : Val                 -- the target answered with a function
  vstuck : Val                 -- ... with something that is not one

Obs : Type₀
Obs = Maybe Val

eqVal : Val → Val → Bool
eqVal vfun   vfun   = true
eqVal vstuck vstuck = true
eqVal _      _      = false

eqObs : Obs → Obs → Bool
eqObs nothing  nothing  = true
eqObs (just x) (just y) = eqVal x y
eqObs _        _        = false

-- ==================================================================
-- §2  A BACKEND.
--
-- PRIMITIVE (phase 1).  Four fields and two type fields: a compiler is
-- a metalanguage function from the common source into ITS OWN target,
-- an execution of that target, and a decoding of the answer into the
-- observable everyone shares.  The two `Type₀` fields are what makes
-- ARM and Rust members of one list despite having nothing in common
-- between `compile` and `decode`.
-- ==================================================================

record Backend : Type₁ where
  field
    name    : String
    Target  : Type₀            -- what this backend compiles INTO
    Answer  : Type₀            -- what running it produces
    compile : Tm [] → Target
    run     : Target → Answer
    decode  : Answer → Obs

  -- the whole pipeline, as one observation of the source
  obs : Tm [] → Obs
  obs t = decode (run (compile t))

open Backend public

-- ==================================================================
-- §3  THE SUITE, over whichever backends were selected.
-- ==================================================================

module Suite (bs : List Backend) where

  -- ----------------------------------------------------------------
  -- 3a.  THE REPORT.  Per term: what each backend said, and whether
  -- they all said the same.  A disagreement is DATA -- a row the user
  -- can read -- and not an unsatisfiable goal.
  -- ----------------------------------------------------------------

  obsOf : Tm [] → List (String × Obs)
  obsOf t = map (λ b → Backend.name b , Backend.obs b t) bs

  -- every entry equal to the first one
  sameAs : Obs → List (String × Obs) → Bool
  sameAs o []            = true
  sameAs o ((_ , o') ∷ r) = eqObs o o' and sameAs o r

  agreeL : List (String × Obs) → Bool
  agreeL []            = true
  agreeL ((_ , o) ∷ r) = sameAs o r

  -- one row of the report
  Row : Type₀
  Row = List (String × Obs) × Bool

  row : Tm [] → Row
  row t = obsOf t , agreeL (obsOf t)

  report : List (Tm []) → List Row
  report = map row

  -- the Bool the internal decision below is about
  agreeOn : Tm [] → Bool
  agreeOn t = agreeL (obsOf t)

  andL : List Bool → Bool
  andL []       = true
  andL (b ∷ bs') = b and andL bs'

  allAgree : List (Tm []) → Bool
  allAgree ts = andL (map agreeOn ts)

  -- ... and the terms that DISAGREED, so a failing run reports itself
  -- rather than merely failing.
  disagreements : List (Tm []) → List Row
  disagreements []       = []
  disagreements (t ∷ ts) = pick (agreeOn t)
    where pick : Bool → List Row
          pick true  = disagreements ts
          pick false = row t ∷ disagreements ts

  -- THE COUNTEREXAMPLE ITSELF, and not merely its row.  This is what
  -- §3c consumes: a generated term the backends parted on is the `t` a
  -- refutation is produced AT, so the search has to hand back the term.
  -- The default is returned when there is nothing to report, which keeps
  -- the type a `Tm []` -- `refuteAgree` wants a term, not a `Maybe`, and
  -- at the default the `≡ false` premise is simply not provable.
  firstBadOr : Tm [] → List (Tm []) → Tm []
  firstBadOr d []       = d
  firstBadOr d (t ∷ ts) = pick (agreeOn t)
    where pick : Bool → Tm []
          pick true  = firstBadOr d ts
          pick false = t

  -- ----------------------------------------------------------------
  -- 3b.  AGREEMENT AS A GRAMMAR.
  --
  -- `⌈ [] ⌉` is `Correct.ClosedTm`'s guard: the backends compile CLOSED
  -- terms, and the representable at the unit of the usage monoid is how
  -- one says so without a side condition.  Away from `[]` the grammar
  -- is empty, which is what makes the decision uniform in the world.
  -- ----------------------------------------------------------------

  Agree : Tm [] → Ctx
  Agree t u = ⌈ [] ⌉ u × (agreeOn t Eq.≡ true)

  -- PRIMITIVE (phase 1): the two decidability facts the decision needs.
  -- Two clauses each, no `Discrete`, no transport.
  isNil : (u : Usage) → (⌈ [] ⌉ u) ⊎ ((⌈ [] ⌉ u) → ⊥)
  isNil []      = inl Eq.refl
  isNil (_ ∷ _) = inr λ ()

  decB : (b : Bool) → (b Eq.≡ true) ⊎ ((b Eq.≡ true) → ⊥)
  decB true  = inl Eq.refl
  decB false = inr λ ()

  -- THE DECISION.  `⊕-I₁`/`⊕-I₂` at a point; the refuting branches are
  -- the only content, and each is one projection.
  agreeDec : (t : Tm []) → ⊤G ⊢ Dec⟨ Agree t ⟩
  agreeDec t u _ = go (isNil u) (decB (agreeOn t))
    where
      go : (⌈ [] ⌉ u) ⊎ ((⌈ [] ⌉ u) → ⊥)
         → (agreeOn t Eq.≡ true) ⊎ ((agreeOn t Eq.≡ true) → ⊥)
         → Dec⟨ Agree t ⟩ u
      go (inl p) (inl e) = inl (p , e)
      go (inl p) (inr k) = inr λ z → E.rec (k (z .snd))
      go (inr k) _       = inr λ z → E.rec (k (z .fst))

  -- `Dec⟨ A ⟩ IS Result (¬G A) A`, definitionally (`Result.agda`).
  agreeR : (t : Tm []) → ⊤G ⊢ Result (¬G (Agree t)) (Agree t)
  agreeR = agreeDec

  -- ----------------------------------------------------------------
  -- 3c.  OBSERVING IT, AND REFUTING IT.
  --
  -- `agrees!` is `okA` composed with the decision -- i.e. every
  -- `accepts`/`isYes`/`closed!` in the instances, at this program.  It
  -- computes to `agreeOn`, which is the sense in which the internal
  -- statement is not a re-spelling of the Bool but a strengthening of
  -- it: `refuteAgree` consumes the SAME `refl`.
  -- ----------------------------------------------------------------

  agrees! : Tm [] → Bool
  agrees! t = LA.accepts? (Agree t) (¬G (Agree t)) (agreeR t) []

  -- A NEGATIVE TEST IS A REFUTATION.  Uniform in the error grammar, and
  -- here the error grammar is `¬G (Agree t)`, so the branch content is a
  -- theorem: anything claiming the backends agreed on `t` is absurd.
  refuteAgree : (t : Tm []) → agrees! t ≡ false → (¬G (Agree t)) []
  refuteAgree t = LA.refute (Agree t) (¬G (Agree t)) (agreeR t) []

  -- ... and the positive direction, for completeness: a `true` hands
  -- back the agreement itself.
  witnessAgree : (t : Tm []) → agrees! t ≡ true → Agree t []
  witnessAgree t = LA.witness (Agree t) (¬G (Agree t)) (agreeR t) []
