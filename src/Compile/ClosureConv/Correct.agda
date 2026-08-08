{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  CLOSURE CONVERSION: THE ON-THE-NOSE SQUARE IS FALSE, AND THE
  RELATIONAL ONE IS THE REPAIR.

  ------------------------------------------------------------------
  1.  THE SAME FAILURE, ONE LEVEL FURTHER OUT
  ------------------------------------------------------------------

  `Compile/Relational/Refutation.agda` refutes

      Simulates = (t v : Tm []) → t ⇓ₛ v → compileRust t ⇓ compileRust v

  because `compileE` names a binder by its DEPTH and substitution moves
  binders.  The diagnosis there is "level-based naming is not stable
  under substitution", and the repair is a relation that does not care
  which level a binder carries.

  Closure conversion removes binders altogether, so that particular
  instability is gone.  What replaces it is worse, and §2 proves it:

      A BLOCK INDEX NAMES A POSITION IN ONE PARTICULAR TABLE.

  `Convert.agda`'s `convApp` offsets the right premise by the number of
  blocks the left premise allocated, so an index is a fact about the
  WHOLE PROGRAM.  Evaluating the source changes the program, hence
  changes the numbering, and the target's answer names a block that the
  compilation of the source's answer does not have.  Concretely

      obs selfApp  = just (clos 1 [])          -- the target's answer
      obs idLin    = just (clos 0 [])          -- and idLin IS its value

  and both are `Eq.refl`.  `(λx.x)(λx.x)` returns its ARGUMENT, which
  the pass numbered `1`; compiled alone, `λx.x` is block `0`.

  The failure is sharper than the Rust one, and worth stating as such.
  There, the two answers were α-equivalent -- the same term up to a
  renaming, so a relation could absorb the difference and `Rel` is a
  strictly weaker `≡`.  Here the observation is not merely too fine, it
  is MEANINGLESS: a `Val` carries a number into a table it no longer
  travels with.  §2's second theorem makes that precise --

      valuesCollapse : (b b' : Tm (true ∷ [])) → obs (tlam b) Eq.≡ obs (tlam b')

  -- `obs` sends EVERY closed value to `clos 0 []`, so it separates
  nothing at all.  That is `Compile/Semantics/CBV.agda`'s `noBlindCBV`
  reappearing for a compiler that is fully term-directed: the compiler
  is not blind, the OBSERVATION is.  A `Val` is only meaningful
  relative to a table, and no equation between values compiled from
  different programs can be a correctness statement.

  ------------------------------------------------------------------
  2.  SO THE RELATION IS INDEXED BY THE TABLE
  ------------------------------------------------------------------

      RelV T v w      "the target value w realises the source value v,
                       with respect to the code table T"

  `rvClos` takes the index `i` as an ARBITRARY natural, constrained
  only by `At T i sh body` -- the block it names.  That is exactly the
  freedom `Rel`'s `rlam n` has over binder levels, moved to code
  pointers: two closures with different indices realise the same source
  λ as long as the blocks they name relate.  `capstone` below is the
  measurement: the answer `obs bigT` computes and the compilation of
  `bigT`'s source value are DISTINCT values, and `RelV` relates them.

  The companion relation is

      RelE T σ t e    "under the frame σ, e realises t"

  with the source term CLOSED-so-far and the target open: that is the
  bridge between a substituting source semantics and an environment
  target, and it is the only place the two disagree.

  THE JUNK SLOT.  `rvClos` and `rclos` state their premise at the frame
  `callFrame sh vs junk` -- the environment, with JUNK in the argument
  slot.  That is sound because slot 0 is still a live variable on BOTH
  sides at that point, and `rvar` relates two slots by their POSITIONS
  without consulting σ.  It is also exactly where the difficulty lives:
  the square has to replace that junk by the actual argument, and that
  is `relSubst`.

  ------------------------------------------------------------------
  3.  WHAT IS PROVED
  ------------------------------------------------------------------

  Everything, with no holes and no postulates:

    * `noNoseSquare`  -- the on-the-nose square is false, witness
      `(λx.x)(λx.x)`, both sides by `Eq.refl`.
    * `valuesCollapse` -- and the observation separates nothing.
    * `capstone` -- the target's answer for `(λf.λx. f x)(λy.y)` is
      `RelV`-related to the source's answer, by hand, at the concrete
      table.  This is the statement the `≡` could not make.
    * `relSubst` -- substituting the argument on the source IS filling
      the argument slot on the target,

          relSubst : RelE T (extF junk σ) b body
                   → RelV T a va
                   → RelE T (extF va σ) (b [ a ]) body

      via the generalised `relSubstG` of §5.5, which is the one that
      recurses.
    * `square`, `squareProg` -- the relational square, structural in
      the source derivation.

  An earlier draft of this header left `relSubst`'s `rapp` and `rclos`
  cases open and diagnosed them as waiting on a MISSING PREMISE on
  `rapp` -- agreement of the two splittings at slot 0.  That diagnosis
  was wrong in an instructive way and the record is worth keeping.

  (a) THE `rapp` PREMISE IS A THEOREM, NOT A PREMISE.  The two
      splittings really are independent -- `sp` over the source usage,
      `sp'` over the target's, and they do not even have the same
      length, so no equation between them is typeable.  What ties them
      is the relation itself: `rvar` pins the two sides' slot NUMBERS
      together, and `rcap` only ever loses a source variable (the target
      goes on reading the frame).  So

          relSub : RelE T σ t e → (p : ℕ) → LiveAt p su → LiveAt p u

      -- the target usage DOMINATES the source usage, positionwise --
      is provable by induction, and it says which branch of `sp'` the
      substituted slot went to.  `split-excl`, which is `Use⊎`'s missing
      (true,true) constructor, then says the OTHER branch is dead there,
      so `relFrame` moves that premise between the two frames.

  (b) `relDelE`/`relInsE` -- the weakening and strengthening lemmas --
      do need what the draft called `Last`, and for the reason it gave:

          THE SUBSTITUTED SLOT IS ALWAYS THE LAST ONE.

      A closed λ-body is `Tm (true ∷ [])`; `subS`'s `tlam` clause
      descends with `mthere true m`, so at depth `d` the scope has
      length `d + 1` and the mark sits at position `d` -- the END.
      Nothing is above it, so `delT`/`insT` shift no live position and
      `rvar`'s slot equation survives untouched.  `Names.agda` §3 states
      this as `Above k v` -- a property of the USAGE rather than of the
      `Mark`, which is what lets it propagate through a splitting
      without anyone casing on `atSplit`/`delSplit`/`insSplit`.

  (c) WHAT DID CHANGE IN THE RELATION IS `rclos`, and it is the capture
      and not the splitting.  `rclos` used to take an arbitrary
      `cap : Cap sh u`; it now takes `idCap u`, which is the only
      capture `Convert.convLam` emits.  A general capture puts an
      arbitrary renaming between a block's shape position and a caller's
      slot, and `rvar` compares slot NUMBERS -- so with a permuting
      capture the relation cannot see that its two premises talk about
      the same variable, and `Names.spreadIdCap`

          spread u (capVals σ (idCap u)) p ≡ σ p     for p live in u

      -- the fact `Convert.agda`'s header §3 claims and does not prove
      -- is exactly what fails.  This is the closure-conversion form of
      the lesson `Compile/Relational/Base.agda` records for binder
      levels: the unrestricted statement is not the one that holds, and
      the restriction that does hold is the compiler's own.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1: metatheorems about the compiler.
-}
open import Cubical.Foundations.Prelude

module Compile.ClosureConv.Correct where

open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; snotz; injSuc)
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.List using (List; []; _∷_; _++_; length)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import Compile.ClosureConv.Convert public
open import Compile.ClosureConv.Names
import Compile.Semantics.CBV as S
import Compile.Semantics.Size as Sz
open import TheoryGrammar.Fibered
import TheoryGrammar.SemanticAction as SA
open import TheoryGrammar.Theories.Monoid using (monoidSig)

-- the semantic-action layer at this substrate, for `Δ`
module CA = SA.Act {σ = monoidSig} (Fibered.carrier linFib)
open CA using (Δ)

-- ==================================================================
-- §1  THE OBSERVATION, AND THE SQUARE IT SUPPORTS.
--
-- `obs` is `Compile/Semantics/Simulation.Backend.run ∘ compile`: the
-- whole program compiled and run.  `Simulates` is
-- `Compile/LinToRust/Codegen.Simulation.Simulates` with `≡` between
-- ANSWERS instead of between compilations, which is the weakest form
-- the statement has -- and it is still false.
-- ==================================================================

-- ------------------------------------------------------------------
-- THE OBSERVATION, INTERNALLY.
--
-- `runP` is the IR's own interpreter, so it is external BY NECESSITY --
-- it is the target's semantics, the model being compiled into, not a
-- program in the calculus.  What is NOT forced is that the observation
-- ITSELF leave the calculus: the codomain is a constant family, so
-- `obsT` is a SEMANTIC ACTION `TmG ⊢ Δ (Maybe Val)`, exactly as
-- `LinToRust/Codegen.srcTm` is `TmG ⊢ Δ String`.  `convertT` is already
-- a term; this puts the run behind one.
-- ------------------------------------------------------------------

-- CLOSED, INTERNALLY.  `runP` runs a CLOSED program, so the domain is
-- not all of `TmG`.  The internal way to say so is the representable at
-- the unit of the usage monoid: `⌈ [] ⌉ & TmG` is "a term, at the empty
-- usage".  No `Tm []` appears in a signature and no side condition is
-- carried alongside -- the restriction is a grammar.
ClosedTm : Ctx
ClosedTm = ⌈ [] ⌉ & TmG

obsT : ClosedTm ⊢ Δ (Maybe Val)
obsT .([]) (Eq.refl , t) = runP 64 (tableOf t , convert t) , tt

-- the external reading, recovered by projection at a point -- the same
-- exit `LinToRust/Codegen.runAt` is, and used only here and in `refl`
-- lines.
obs : Tm [] → Maybe Val
obs t = obsT [] (Eq.refl , t) .fst

-- ------------------------------------------------------------------
-- THE EVALUATION RELATION, AS A GRAMMAR -- which is what lets the square
-- be an equation between `⊢`-TERMS rather than a pointwise claim.
-- ------------------------------------------------------------------

-- `S._⇓_` is a relation on CLOSED terms, so the evaluation relation
-- exists only at the unit world -- and `⌈ [] ⌉ &` is how one says that
-- without a side condition.  The constant family is legitimate here
-- because it is a HYPOTHESIS, not a producer's codomain: `⌈ [] ⌉` pins
-- the world, and the pair is exactly "an evaluation, at the unit".
EvalC : Type₀
EvalC = Σ[ t ∈ Tm [] ] Σ[ v ∈ Tm [] ] (t S.⇓ v)

ClosedEval : Ctx
ClosedEval = ⌈ [] ⌉ & (λ _ → EvalC)

srcOf tgtOf : ClosedEval ⊢ ClosedTm
srcOf .([]) (Eq.refl , t , v , d) = Eq.refl , t
tgtOf .([]) (Eq.refl , t , v , d) = Eq.refl , v

-- THE SQUARE, INTERNALLY: the two composites out of the evaluation
-- relation agree.  An equation between maps of the calculus, with no
-- point and no `Eq.≡` on answers anywhere in the statement.
SimulatesG : Type₀
SimulatesG = _≡_ {A = ClosedEval ⊢ Δ (Maybe Val)}
                 (λ u x → obsT u (srcOf u x))
                 (λ u x → obsT u (tgtOf u x))

-- ... and the pointwise form is its consequence, so refuting THAT
-- refutes this.  Stated in this direction deliberately: the internal
-- statement is the headline and the external one is derived from it.
Simulates : Type₀
Simulates = (t v : Tm []) → t S.⇓ v → obs t Eq.≡ obs v

simG→sim : SimulatesG → Simulates
-- apply both sides of `sq` at the world and the point, then project.
-- `funExt⁻` twice rather than a raw `cong`, so the motive is forced
-- rather than guessed.
simG→sim sq t v d =
  Eq.pathToEq (cong fst (funExt⁻ (funExt⁻ sq []) (Eq.refl , t , v , d)))

-- the tag that reads a code pointer off an answer.  `suc` so that a
-- non-answer and block `0` are not conflated.
codeOfM : Maybe Val → ℕ
codeOfM nothing           = 0
codeOfM (just (clos i _)) = suc i

-- ==================================================================
-- §2  THE REFUTATION.
--
-- Everything computed is `Eq.refl`, so nothing here is an argument by
-- hand -- exactly the standard `Compile/Relational/Refutation.agda`
-- sets.
-- ==================================================================

-- ------------------------------------------------------------------
-- 2.1  THE WITNESS.  `(λx.x)(λx.x)` -- the smallest term whose value
-- is a SUBTERM the pass numbered second.
-- ------------------------------------------------------------------

_ : obs selfApp Eq.≡ just (clos 1 [])
_ = Eq.refl

_ : obs idLin Eq.≡ just (clos 0 [])
_ = Eq.refl

-- ... and `idLin` really is `selfApp`'s call-by-value answer
selfApp⇓ : selfApp S.⇓ idLin
selfApp⇓ = S.evalD selfApp

-- THE VERDICT.  The block index a value carries is a fact about the
-- program it was compiled with, and evaluation changes the program.
noNoseSquare : Simulates → ⊥
noNoseSquare sq =
  snotz (injSuc (cong codeOfM (Eq.eqToPath (sq selfApp idLin selfApp⇓))))

-- THE INTERNAL VERDICT.  The square, stated as an equation between
-- `⊢`-terms, is false -- and the refutation is the external one composed
-- with `simG→sim`, so nothing about the argument changed, only where the
-- statement lives.
noSquareG : SimulatesG → ⊥
noSquareG sq = noNoseSquare (simG→sim sq)

-- ------------------------------------------------------------------
-- 2.2  THE RICHER WITNESS, for the record.  `(λf. λx. f x)(λy. y)` is
-- `Compile/Relational`'s own counterexample; here the answer even has
-- a NON-EMPTY environment, so the two sides differ in their payload
-- and not only in their tag.
-- ------------------------------------------------------------------

bigV : Tm []
bigV = S.evalV bigT

_ : obs bigT Eq.≡ just (clos 1 (clos 2 [] ∷ []))
_ = Eq.refl

_ : obs bigV Eq.≡ just (clos 0 [])
_ = Eq.refl

-- ------------------------------------------------------------------
-- 2.3  ... AND THE OBSERVATION SEPARATES NOTHING.
--
-- A closed source value is a λ (`CBV.closedVal`), the pass sends every
-- λ at the empty usage to `iclos 0` with an empty capture, and the
-- machine answers `clos 0 []`.  So `obs` is CONSTANT on values.  This
-- is `Simulation.noBlindBackend`'s failure of injectivity, arrived at
-- from the other end: the compiler is term-directed and it is the
-- OBSERVATION that is blind.
--
-- Read together with 2.1: `Simulates` would force every terminating
-- program to observe as `clos 0 []`, and `selfApp` does not.
-- ------------------------------------------------------------------

valuesCollapse : (b b' : Tm (true ∷ [])) → obs (tlam b) Eq.≡ obs (tlam b')
valuesCollapse b b' = Eq.refl

valueObs : (b : Tm (true ∷ [])) → obs (tlam b) Eq.≡ just (clos 0 [])
valueObs b = Eq.refl

-- ==================================================================
-- §3  THE REALISATION RELATION.
--
-- Two mutually inductive families.  `RelV` relates a closed source
-- VALUE to a target value; `RelE` relates a source term to a target
-- expression together with the frame that supplies what the source has
-- already substituted.
--
-- `rvar` is the only clause that mentions positions, and it mentions
-- them as an `Eq.≡` of slot numbers, so it computes.  `rcap` is the
-- clause that crosses the substitution/environment divide: the source
-- has a VALUE where the target has a frame read.
-- ==================================================================

data RelV (T : Table) : {u : Usage} → Tm u → Val → Type₀
data RelE (T : Table) : Frame → {su u : Usage} → Tm su → IR u → Type₀

data RelV T where
  -- the code index is ARBITRARY; only the block it names is
  -- constrained.  This is `Relational.Base.rlam`'s free level.
  rvClos : ∀ {u} {b : Tm (true ∷ u)} {i sh vs} {body : IR (true ∷ sh)}
         → Empty u
         → At T i sh body
         → RelE T (callFrame sh vs junk) b body
         → RelV T (tlam b) (clos i vs)

data RelE T where
  -- both sides still hold the variable, at corresponding slots
  rvar  : ∀ {σ su u} (s : Solo su) (s' : Solo u)
        → slotOf 0 su s Eq.≡ slotOf 0 u s'
        → RelE T σ (tvar s) (ivar s')

  -- the source substituted a value here; the target reads the frame
  rcap  : ∀ {σ su u} {t : Tm su} (s' : Solo u)
        → RelV T t (σ (slotOf 0 u s'))
        → RelE T σ t (ivar s')

  -- a call is a call.  The two splittings are independent, which is
  -- the gap §3 of the header names.
  rapp  : ∀ {σ su₁ su₂ su u₁ u₂ u}
          {sp : Use⊎ su₁ su₂ su} {sp' : Use⊎ u₁ u₂ u}
          {x : Tm su₁} {y : Tm su₂} {x' : IR u₁} {y' : IR u₂}
        → RelE T σ x x' → RelE T σ y y'
        → RelE T σ (tapp sp x y) (iapp sp' x' y')

  -- a λ is a closure: the block it names must relate to the λ's body,
  -- under the frame the capture builds out of σ.
  --
  -- THE CAPTURE IS `idCap`, AND THAT IS A PREMISE AND NOT A CHOICE.
  -- `Convert.convLam` emits `idCap u` and nothing else, and its header
  -- §3 says why: taking the block's shape to be the usage AT the λ is
  -- what makes the capture positional, i.e. what makes
  --
  --     spread u (capVals σ (idCap u))   agree with   σ
  --
  -- on every live position (`Names.spreadIdCap`).  A general `Cap sh u`
  -- puts an arbitrary renaming between a shape position and a caller
  -- slot, and then NOTHING relates the two sides' positions -- `rvar`
  -- compares slot NUMBERS, so a relation that admits a permuting
  -- capture cannot see that its two premises talk about the same
  -- variable.  This is the closure-conversion form of the lesson
  -- `Compile/Relational/Base.agda` records for binder levels: the
  -- unrestricted statement is not the one that holds.
  rclos : ∀ {σ su u i} {b : Tm (true ∷ su)} {body : IR (true ∷ u)}
        → At T i u body
        → RelE T (callFrame u (capVals σ (idCap u)) junk) b body
        → RelE T σ (tlam b) (iclos i (idCap u))

-- ==================================================================
-- §4  THE CAPSTONE.  THE `≡` WAS WRONG, THE RELATION IS RIGHT.
--
-- `obs bigT` computes to `clos 1 (clos 2 [] ∷ [])`; `obs bigV`
-- computes to `clos 0 []`; §2.2 shows they are different.  Here is a
-- proof that the FIRST of them realises `bigV` with respect to
-- `bigT`'s own table -- the statement the equation could not make.
--
-- Every premise is either `ahere`/`athere` (which block) or `Eq.refl`
-- (which slot).  Nothing is transported.
-- ==================================================================

capstone : RelV (tableOf bigT) bigV (clos 1 (clos 2 [] ∷ []))
capstone =
  rvClos tt (athere ahere)
    (rapp (rcap tt (rvClos tt (athere (athere ahere)) (rvar tt tt Eq.refl)))
          (rvar tt tt Eq.refl))

-- ... and that value really is the one the machine produced
_ : obs bigT Eq.≡ just (clos 1 (clos 2 [] ∷ []))
_ = Eq.refl

-- the compiled source answer, related to itself, for contrast: the two
-- `RelV`-related values are `clos 1 (clos 2 [] ∷ [])` and `clos 0 []`,
-- and `codeOfM` separates them
_ : codeOfM (obs bigT) Eq.≡ 2
_ = Eq.refl

_ : codeOfM (obs bigV) Eq.≡ 1
_ = Eq.refl

-- ==================================================================
-- §5  THE SUBSTITUTION LEMMA -- THE ONE THING THE SQUARE NEEDS.
--
-- Source substitution at slot 0 IS filling the target's argument slot.
-- The shape of the section is `Compile/Relational/Names.agda` +
-- `Subst.agda`, one backend over: first the relation is shown blind to
-- the three index manipulations `subS` performs (5.1, 5.4), then the
-- two facts that are special to an ENVIRONMENT target rather than a
-- substituting one -- that the target usage dominates the source's
-- (5.2), and that a frame may be changed off the slots an expression
-- reads (5.3) -- and then the lemma itself (5.5).
-- ==================================================================

-- ------------------------------------------------------------------
-- 5.1  THE RELATION IS BLIND TO THE THREE INDEX MANIPULATIONS.
--
-- Exactly `Compile/Relational/Names.agda`'s §4, one backend over.
-- `subS` calls `coeTm`, `delT` and `insT`, and the TARGET is unchanged
-- by all three, so each is a lemma saying the relation does not notice.
-- Here `delT`/`insT` DO move slot numbers, and `Above` is the
-- hypothesis that says they move none that is live -- see
-- `Names.agda` §3.
-- ------------------------------------------------------------------

relVCoe : ∀ {T u v} (p : u Eq.≡ v) {a : Tm u} {w : Val}
        → RelV T a w → RelV T (coeTm p a) w
relVCoe Eq.refl r = r

-- `RelV`'s source is closed -- the fact that kills case (ii) below
relVEmpty : ∀ {T u} {a : Tm u} {w : Val} → RelV T a w → Empty u
relVEmpty (rvClos e _ _) = e

-- ------------------------------------------------------------------
-- 5.2  THE SOURCE'S LIVE POSITIONS ARE LIVE ON THE TARGET.
--
-- This is what `rapp` was missing, and it is a THEOREM rather than the
-- extra `hd` premise the old header §3(a) proposed: the two splittings
-- really are independent, but they are not unrelated, because `rvar`
-- pins the two sides' slot numbers together and `rcap` only ever loses
-- a source variable (the target keeps reading the frame).  So the
-- target usage DOMINATES the source usage, positionwise, and that is
-- enough to know which branch of `sp'` the substituted slot went to.
-- ------------------------------------------------------------------
relSub : ∀ {T σ su u} {t : Tm su} {e : IR u}
       → RelE T σ t e → (p : ℕ) → LiveAt p su → LiveAt p u
relSub (rvar {su = su} {u = u} s s' eq) p l =
  Eq.transport (λ z → LiveAt z u)
    (Eq.sym (soloUnique su s p l Eq.∙ eq)) (soloLiveAt u s')
relSub {su = su} (rcap s' rv) p l =
  E.rec (live-dead p su l (emptyDead su (relVEmpty rv) p))
relSub (rapp {sp = s} {sp' = s'} rx ry) p l with split-live s p l
... | inl l₁ = split-liveL s' p (relSub rx p l₁)
... | inr l₂ = split-liveR s' p (relSub ry p l₂)
relSub (rclos at rb) p l = relSub rb (suc p) l

-- ------------------------------------------------------------------
-- 5.3  CHANGING THE FRAME OFF THE EXPRESSION'S OWN SLOTS.
--
-- `IR u` is indexed by the usage, so `u` already says which frame slots
-- the expression reads: `rcap` reads the one `Solo u` names, and
-- `rclos`'s capture reads the live ones.  Two frames agreeing there
-- are interchangeable.
-- ------------------------------------------------------------------
relFrame : ∀ {T su u} {σ₀ σ₁ : Frame} {t : Tm su} {e : IR u}
         → ((p : ℕ) → LiveAt p u → σ₀ p Eq.≡ σ₁ p)
         → RelE T σ₀ t e → RelE T σ₁ t e
relFrame ag (rvar s s' eq) = rvar s s' eq
relFrame {T = T} ag (rcap {u = u} {t = t} s' rv) =
  rcap s' (Eq.transport (λ w → RelV T t w)
             (ag (slotOf 0 u s') (soloLiveAt u s')) rv)
relFrame ag (rapp {sp' = s'} rx ry) =
  rapp (relFrame (λ p l → ag p (split-liveL s' p l)) rx)
       (relFrame (λ p l → ag p (split-liveR s' p l)) ry)
relFrame {T = T} ag (rclos {u = u} {b = b} {body = body} at rb) =
  rclos at (Eq.transport (λ vs → RelE T (callFrame u vs junk) b body)
                         (capValsCong u _ _ ag) rb)

-- ------------------------------------------------------------------
-- 5.4  STRENGTHENING AND WEAKENING THE SOURCE, TARGET UNTOUCHED.
--
-- `relDelE`/`relInsE` are `Relational/Names.agda`'s `relDel`/`relIns`.
-- Their `rvar` cases are the only content and they are `delSlot` /
-- `insSlot`: with nothing live above the moved slot, the slot NUMBERS
-- do not change, so the target's `rvar` equation is reused verbatim.
-- The old header §3(b) feared a renaming would be needed here, as in
-- the Rust path; `Above` is why it is not.
-- ------------------------------------------------------------------

relDelE : ∀ {T k q v u} {σ : Frame} {y : Tm v} {y' : IR u}
          (m : Mark false k q v) → Above k v
        → RelE T σ y y' → RelE T σ (delT m y) y'
relDelV : ∀ {T k q v} {y : Tm v} {w : Val}
          (m : Mark false k q v) → Above k v
        → RelV T y w → RelV T (delT m y) w

relDelE m ab (rvar s s' eq) =
  rvar (markF-Solo← m s) s' (delSlot m ab s Eq.∙ eq)
relDelE m ab (rcap s' rv) = rcap s' (relDelV m ab rv)
relDelE m ab (rapp {sp = s} rx ry) with delSplit m s
... | (_ , _ , m₁ , m₂ , _) =
  rapp (relDelE m₁ (above-splitL s ab) rx)
       (relDelE m₂ (above-splitR s ab) ry)
relDelE m ab (rclos at rb) =
  rclos at (relDelE (mthere true m) (above-cons true ab) rb)

relDelV m ab (rvClos e at rb) =
  rvClos (markF-Empty← m e) at
    (relDelE (mthere true m) (above-cons true ab) rb)

relInsE : ∀ {T k q v u} {σ : Frame} {a : Tm q} {e : IR u}
          (m : Mark false k q v) → Above k v
        → RelE T σ a e → RelE T σ (insT m a) e
relInsV : ∀ {T k q v} {a : Tm q} {w : Val}
          (m : Mark false k q v) → Above k v
        → RelV T a w → RelV T (insT m a) w

relInsE m ab (rvar s s' eq) =
  rvar (markF-Solo→ m s) s' (insSlot m ab s Eq.∙ eq)
relInsE m ab (rcap s' rv) = rcap s' (relInsV m ab rv)
relInsE m ab (rapp {sp = s} rx ry) with insSplit m s
... | (_ , _ , m₁ , m₂ , s') =
  rapp (relInsE m₁ (above-splitL s' ab) rx)
       (relInsE m₂ (above-splitR s' ab) ry)
relInsE m ab (rclos at rb) =
  rclos at (relInsE (mthere true m) (above-cons true ab) rb)

relInsV m ab (rvClos e at rb) =
  rvClos (markF-Empty→ m e) at
    (relInsE (mthere true m) (above-cons true ab) rb)

-- ------------------------------------------------------------------
-- 5.5  THE SUBSTITUTION LEMMA, GENERALISED SO THAT IT RECURSES.
--
-- The statement `relSubst` wants is not an induction hypothesis: under
-- a binder the source's mark moves from position `k` to `k+1` and the
-- target's frame is replaced by the block's, so both the marked
-- position and the two frames have to be quantified.  What is preserved
-- is the pair of facts
--
--     the two frames agree AWAY FROM the marked position   (`ag`)
--     and at it, the new one holds the argument's value    (`hit`)
--
-- and `Names.spreadIdCap` is exactly the lemma that re-establishes both
-- after `rclos` swaps the frame for `callFrame u (capVals σ (idCap u))`.
-- ------------------------------------------------------------------
relSubstG : ∀ {T : Table} {k : ℕ} {su v u₂ u : Usage}
            (m : Mark true k su v) (sp : Use⊎ su u₂ u)
            {σ₀ σ₁ : Frame} {tu : Usage} {b : Tm v} {body : IR tu}
            {a : Tm u₂} {va : Val}
          → Above k v
          → ((p : ℕ) → Dif p k → σ₀ p Eq.≡ σ₁ p)
          → σ₁ k Eq.≡ va
          → RelE T σ₀ b body
          → RelV T a va
          → RelE T σ₁ (Sz.subSize m sp b a) body

-- (i)  THE BODY IS THE VARIABLE.  `subS`'s `tvar` clause returns the
-- argument outright (`coeTm`), and the target reads the slot `rvar`'s
-- equation pins to the marked position -- which is where `hit` put the
-- value.
relSubstG {T = T} m sp {σ₁ = σ₁} {a = a} ab ag hit (rvar s s' eq) rv =
  rcap s'
    (Eq.transport (λ w → RelV T (coeTm (useEmptyL sp (markT-Solo m s)) a) w)
      (Eq.sym (Eq.ap σ₁ (Eq.sym eq Eq.∙ markT-slotOf m s) Eq.∙ hit))
      (relVCoe (useEmptyL sp (markT-Solo m s)) rv))

-- (ii) THE BODY IS A CAPTURED VALUE.  Impossible: `RelV` forces its
-- source to sit at an `Empty` usage, and a usage carrying `Mark true`
-- is not one.
relSubstG m sp ab ag hit (rcap s' rv') rv =
  E.rec (markT-¬Empty m (relVEmpty rv'))

-- (iii) A CALL.  `atSplit` says the substituted variable went to
-- exactly one premise; `relSub` says the corresponding TARGET slot is
-- live in that premise's usage, hence -- by `split-excl`, which is
-- linearity -- dead in the other's.  So the other premise reads no slot
-- the two frames disagree on, and `relFrame` moves it across after
-- `relDelE` has strengthened it.  This is the "same branch" fact the
-- old header §3(a) wanted as a premise.
relSubstG {k = k} m sp ab ag hit (rapp {sp = s} {sp' = sp'} rx ry) rv
  with atSplit m s
... | inl (_ , _ , mp , mq , sq) =
  rapp (relSubstG mp (useExch sq sp .snd .fst) (above-splitL s ab) ag hit rx rv)
       (relFrame
         (λ p l → ag p (live-dead-dif p k _ l
                          (split-excl sp' k (relSub rx k (markT-liveAt mp)))))
         (relDelE mq (above-splitR s ab) ry))
... | inr (_ , _ , mp , mq , sq) =
  rapp (relFrame
         (λ p l → ag p (live-dead-dif p k _ l
                          (split-exclR sp' k (relSub ry k (markT-liveAt mq)))))
         (relDelE mp (above-splitL s ab) rx))
       (relSubstG mq (useAssoc sq sp .snd .fst) (above-splitR s ab) ag hit ry rv)

-- (iv) A CLOSURE.  `subS`'s `tlam` clause shifts the argument past the
-- binder (`insT mhere`, absorbed by `relInsV`), and on the target the
-- block runs under `callFrame u (capVals σ (idCap u)) junk`.  Slot
-- `suc p` of that frame is `σ p` on every live `p` (`spreadIdCap`) and
-- `junk` on every dead one, which is `ag` and `hit` one level down --
-- the argument's slot is live because `relSub` says the source's marked
-- position is live on the target.
relSubstG {T = T} {k = k} {u₂ = u₂} m sp {σ₀ = σ₀} {σ₁ = σ₁} {va = va}
          ab ag hit (rclos {u = tu} at rb) rv =
  rclos at
    (relSubstG (mthere true m) (uleft sp) (above-cons true ab) ag' hit' rb
      (relInsV mhere argAbove rv))
  where
  argAbove : Above 0 (false ∷ u₂)
  argAbove zero    l = E.rec l
  argAbove (suc p) l = emptyDead u₂ (relVEmpty rv) p

  liveK : LiveAt k tu
  liveK = relSub rb (suc k) (markT-liveAt m)

  agS : (p : ℕ) → Dif p k
      → spread tu (capVals σ₀ (idCap tu)) p
     Eq.≡ spread tu (capVals σ₁ (idCap tu)) p
  agS p d = go (liveDec p tu)
    where
    go : LiveAt p tu ⊎ DeadAt p tu
       → spread tu (capVals σ₀ (idCap tu)) p
      Eq.≡ spread tu (capVals σ₁ (idCap tu)) p
    go (inl l)  = spreadIdCap tu σ₀ p l Eq.∙ ag p d
                Eq.∙ Eq.sym (spreadIdCap tu σ₁ p l)
    go (inr dd) = spreadIdCapDead tu σ₀ p dd
                Eq.∙ Eq.sym (spreadIdCapDead tu σ₁ p dd)

  ag' : (p : ℕ) → Dif p (suc k)
      → callFrame tu (capVals σ₀ (idCap tu)) junk p
     Eq.≡ callFrame tu (capVals σ₁ (idCap tu)) junk p
  ag' zero    d = Eq.refl
  ag' (suc p) d = agS p d

  hit' : callFrame tu (capVals σ₁ (idCap tu)) junk (suc k) Eq.≡ va
  hit' = spreadIdCap tu σ₁ k liveK Eq.∙ hit

-- ------------------------------------------------------------------
-- ... AND THE STATEMENT THE SQUARE CONSUMES.  At the top the mark is
-- `mhere` at position 0, the splitting is the only `Use⊎ [] [] []`, and
-- both side conditions are `Eq.refl`.
-- ------------------------------------------------------------------
relSubst : {T : Table} {σ : Frame} {u : Usage}
           {b : Tm (true ∷ [])} {body : IR (true ∷ u)}
           {a : Tm []} {va : Val}
         → RelE T (extF junk σ) b body
         → RelV T a va
         → RelE T (extF va σ) (b S.[ a ]) body
relSubst {σ = σ} {va = va} rb rv = relSubstG mhere unil ab₀ ag₀ Eq.refl rb rv
  where
  ab₀ : Above 0 (true ∷ [])
  ab₀ zero    l = E.rec l
  ab₀ (suc p) l = tt

  ag₀ : (p : ℕ) → Dif p 0 → extF junk σ p Eq.≡ extF va σ p
  ag₀ zero    d = E.rec d
  ag₀ (suc p) d = Eq.refl

-- ==================================================================
-- §6  THE RELATIONAL SQUARE.
--
-- Structural in the source derivation, exactly as
-- `Compile/Relational/Square.agda` is: `⇓app`'s three premises --
-- callee, argument, and BODY AT THE VALUE -- are all subderivations,
-- so no measure is needed even though the body is not a subterm.
--
--   ⇓lam  a source value is a λ.  The target's expression is either a
--         closure (`rclos`, and its premise IS `rvClos`'s) or a frame
--         read (`rcap`, and its premise IS the conclusion).  Both
--         branches are complete.
--   ⇓app  the callee evaluates to a closure whose block is named by
--         `rvClos`; the argument evaluates; `relSubst` puts the
--         argument in the frame; and `⇓call` assembles the three.
-- ==================================================================

square : {T : Table} {t v : Tm []} → t S.⇓ v
       → {u : Usage} {σ : Frame} {e : IR u}
       → RelE T σ t e
       → Σ[ w ∈ Val ] (Ev T σ e w × RelV T v w)

square S.⇓lam (rclos at rb)  = _ , ⇓clos _ _ , rvClos tt at rb
square S.⇓lam (rcap s' rv)   = _ , ⇓var s'   , rv

square (S.⇓app df da dw) (rcap s' ())
square (S.⇓app df da dw) (rapp rf ra) = go (square df rf)
  where
  go : Σ[ wf ∈ Val ] (Ev _ _ _ wf × RelV _ _ wf) → _
  go (_ , evf , rvClos _ at rb) =
    let (wa , eva , rva)  = square da ra
        (w  , evb , rvw)  = square dw (relSubst rb rva)
    in w , ⇓call evf at eva evb , rvw

-- ------------------------------------------------------------------
-- THE FORM A BACKEND CONSUMES.  A closed program's target answer
-- realises its source's answer, with respect to the program's own
-- table -- which is the only table the answer means anything in.
-- ------------------------------------------------------------------

squareProg : (t : Tm []) {e : IR []}
           → RelE (tableOf t) emptyF t e
           → Σ[ w ∈ Val ] (Ev (tableOf t) emptyF e w × RelV (tableOf t) (S.evalV t) w)
squareProg t r = square (S.evalD t) r
