{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE PROTOCOL LOG, DECIDED -- and the accounting.

  `Protocol` builds the grammar; this file runs it.  Every answer below
  is one `refl`, so the typechecker is the evaluator and the decision
  procedure really does compute at these logs.

  Three things are pinned, in increasing strength:

    (1) the SEARCH SPACE, counted.  The same log has 5 concatenations,
        9 I-shuffles and 16 interleavings; the middle number is the one
        this parser searches, and it is what "the decomposition operator
        is interleaving, not concatenation" means quantitatively.

    (2) the ANSWERS, as a suite of `refl`s -- valid logs accepted,
        invalid ones rejected.

    (3) the answers as THEOREMS.  `witness` turns an accepted log into a
        derivation, and `refute` turns a rejected one into a map
        `Deriv log w → ⊥` -- a proof that NO interleaving of NO pair of
        valid sessions produces that log.  A `≡ false` alone would not
        say that; the error grammar is `¬G (Deriv log)`, so it does.

  The negative cases are chosen to fail for four DIFFERENT protocol
  reasons, and `bad-out-of-order` is the interesting one: it fails only
  because same-session events do not commute.  `module Control` at the
  end PROVES that, by running the same grammar and the same decision
  procedure at the ⊤ endpoint -- where everything commutes, and where
  `Traces/Commutative` shows the splittings are `Instances.Bags`'
  interleavings.  There the log is ACCEPTED, and `wrong-at-⊤` is the
  derivation.  So the two files together are a controlled experiment:
  one `Fibered` changed, one answer changed.
-}
module TheoryGrammar.Instances.Traces.ProtocolTests where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.List
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Empty as E using (⊥)

open import TheoryGrammar.Enumerable using (No)
open import TheoryGrammar.SemanticAction using (passes; _↦_; _at_)

open import TheoryGrammar.Instances.Traces.Protocol

import TheoryGrammar.Instances.Traces.Ordered     as TrOrd
import TheoryGrammar.Instances.Traces.Commutative as TrCom
import TheoryGrammar.Instances.Traces.Enumeration as TrE

-- ==================================================================
-- The six events, and the logs.
-- ==================================================================

o₀ m₀ c₀ o₁ m₁ c₁ : Ev
o₀ = s₀ , opn
m₀ = s₀ , msg
c₀ = s₀ , cls
o₁ = s₁ , opn
m₁ = s₁ , msg
c₁ = s₁ , cls

-- VALID: the two sessions overlap, session 0 closing first
logOK : Word
logOK = o₀ ∷ o₁ ∷ c₀ ∷ c₁ ∷ []

-- VALID: properly nested
logNest : Word
logNest = o₀ ∷ o₁ ∷ c₁ ∷ c₀ ∷ []

-- VALID: no overlap at all -- a sequential log is a special interleaving
logSeq : Word
logSeq = o₀ ∷ c₀ ∷ o₁ ∷ c₁ ∷ []

-- VALID: with messages, six events
logMsg : Word
logMsg = o₀ ∷ o₁ ∷ m₀ ∷ m₁ ∷ c₀ ∷ c₁ ∷ []

-- VALID: eight events, two messages per session
logBig : Word
logBig = o₀ ∷ o₁ ∷ m₀ ∷ m₁ ∷ m₀ ∷ m₁ ∷ c₀ ∷ c₁ ∷ []

-- INVALID: session 0 opens and never closes
badOpen : Word
badOpen = o₀ ∷ o₁ ∷ c₁ ∷ []

-- INVALID: session 1 sends before it opens
badMsg : Word
badMsg = o₀ ∷ m₁ ∷ c₀ ∷ c₁ ∷ []

-- INVALID: session 0 closes before it opens.  Its MULTISET of events is
-- that of `logOK`; only the order is wrong.
badOrder : Word
badOrder = c₀ ∷ o₀ ∷ o₁ ∷ c₁ ∷ []

-- INVALID: session 0 sends after it has closed
badAfter : Word
badAfter = o₀ ∷ c₀ ∷ m₀ ∷ o₁ ∷ c₁ ∷ []

-- ==================================================================
-- (1)  THE SEARCH SPACE, COUNTED.
--
-- The two endpoints of the trace family (`Traces/Ordered` and
-- `Traces/Commutative`) instantiated at this alphabet, purely to
-- measure.  `Ordered` and `Commutative` PROVE the enumerated types are
-- `Strings`' `Split3` and `Bags`' `Ilv`, so these are not three
-- unrelated counts -- they are the free monoid, the trace monoid and
-- the free commutative monoid at the same word.
-- ==================================================================

module OrdI = TrOrd Ev
module ComI = TrCom Ev

dec⊥ : (x y : Ev) → OrdI.⊥I x y ⊎ No (OrdI.⊥I x y)
dec⊥ x y = inr λ ()

isProp⊥I : (x y : Ev) → isProp (OrdI.⊥I x y)
isProp⊥I x y = E.isProp⊥

module Cat = TrE Ev OrdI.⊥I dec⊥ isProp⊥I   -- concatenation

-- ... and full interleaving is `Protocol.Full`, the ⊤ endpoint the
-- control below runs the parser at.  `Traces/Commutative` proves that
-- relation's splittings ARE `Instances.Bags`' interleavings, and the
-- two spellings of ⊤ agree on the nose:
_ : (e f : Ev) → ⊤I e f ≡ ComI.⊤I e f
_ = λ e f → refl

-- four events:  5 < 9 < 16
_ : length (Cat.shuffles logOK) ≡ 5
_ = refl

_ : length (shuffles logOK) ≡ 9
_ = refl

_ : length (Full.shuffles logOK) ≡ 16
_ = refl

-- six events:  7 < 16 < 64.  The independence relation prunes hard --
-- it forbids reordering WITHIN a session -- which is why a decision
-- procedure that scans every splitting is still tractable here.
_ : length (Cat.shuffles logMsg) ≡ 7
_ = refl

_ : length (shuffles logMsg) ≡ 16
_ = refl

_ : length (Full.shuffles logMsg) ≡ 64
_ = refl

-- ==================================================================
-- (2)  THE ANSWERS.
-- ==================================================================

derives! : (P : NT) → ⊤G ⊢ Δ Bool
derives! P = okA (Deriv P) (¬G Deriv P) ∘g derives? P

-- ---- one session on its own.  Inside a session `⊗ˢ appop` is
-- concatenation, because same-session events are dependent, so the
-- open must come first and the close last.
_ : passes (run (derives! sessA) at
             ( (o₀ ∷ c₀ ∷ [])      ↦ true
             ∷ (o₀ ∷ m₀ ∷ c₀ ∷ []) ↦ true
             ∷ (c₀ ∷ o₀ ∷ [])      ↦ false
             ∷ (o₀ ∷ [])           ↦ false
             ∷ (m₀ ∷ c₀ ∷ [])      ↦ false
             ∷ (o₀ ∷ c₀ ∷ m₀ ∷ []) ↦ false ∷ [] ))
_ = refl

-- ... and a session-0 grammar does not accept session-1 events
_ : passes (run (derives! sessA) at ( (o₁ ∷ c₁ ∷ []) ↦ false ∷ [] ))
_ = refl

-- ---- THE WHOLE LOG.  Across sessions `⊗ˢ appop` is interleaving, so
-- all three arrangements of two valid sessions are accepted.
_ : passes (run (derives! log) at
             ( logOK   ↦ true
             ∷ logNest ↦ true
             ∷ logSeq  ↦ true
             ∷ logMsg  ↦ true
             ∷ logBig  ↦ true ∷ [] ))
_ = refl

-- ---- ... and every protocol violation is rejected
_ : passes (run (derives! log) at
             ( badOpen  ↦ false
             ∷ badMsg   ↦ false
             ∷ badOrder ↦ false
             ∷ badAfter ↦ false ∷ [] ))
_ = refl

-- ==================================================================
-- (3)  THE ANSWERS AS THEOREMS.
--
-- `run … ≡ true/false` is an observation.  `witness`/`refute` read the
-- same term at the same word and hand back the CONTENT of the branch,
-- because the error grammar is `¬G (Deriv log)` and not `⊤G`.
-- ==================================================================

overlapping : Deriv log logOK
overlapping = witness (Deriv log) (¬G Deriv log) (derives? log) logOK refl

nested : Deriv log logNest
nested = witness (Deriv log) (¬G Deriv log) (derives? log) logNest refl

with-messages : Deriv log logMsg
with-messages = witness (Deriv log) (¬G Deriv log) (derives? log) logMsg refl

-- NO interleaving of NO pair of protocol-following sessions is this log.
-- That is what the four types below say, and each is proved by the
-- `refl` of the corresponding line above.

-- an open with no matching close
bad-unmatched-open : Deriv log badOpen → E.⊥* {ℓ-zero}
bad-unmatched-open =
  refute (Deriv log) (¬G Deriv log) (derives? log) badOpen refl

-- a send belonging to a session that never opened
bad-send-before-open : Deriv log badMsg → E.⊥* {ℓ-zero}
bad-send-before-open =
  refute (Deriv log) (¬G Deriv log) (derives? log) badMsg refl

-- a send after the session closed
bad-send-after-close : Deriv log badAfter → E.⊥* {ℓ-zero}
bad-send-after-close =
  refute (Deriv log) (¬G Deriv log) (derives? log) badAfter refl

-- THE ONE THAT SEPARATES TRACES FROM BAGS.  `badOrder` has exactly the
-- events of `logOK`, permuted; it is refuted because `Ind` does not
-- relate a session to itself, so no `right` step may carry `o₀` past
-- `c₀`.
bad-out-of-order : Deriv log badOrder → E.⊥* {ℓ-zero}
bad-out-of-order =
  refute (Deriv log) (¬G Deriv log) (derives? log) badOrder refl

-- ==================================================================
-- THE CONTROL: THE SAME PARSER AT THE ⊤ ENDPOINT.
--
-- `Protocol.Full` is `Protocol.Over` at `⊤I` -- every pair of events
-- commutes, so the splittings are the free COMMUTATIVE monoid's, which
-- `Traces/Commutative` proves are `Instances.Bags`' interleavings.  The
-- grammar is the same, the decision procedure is the same term; only
-- `Fibered .Split` differs.
--
-- And it gets the WRONG ANSWER on `badOrder`: with `o₀` free to commute
-- past `c₀`, the session-0 factor `c₀ o₀` can be re-read as `o₀ c₀`, so
-- the parser certifies a log in which a session closes before it opens.
-- The refutation above therefore is not an artefact of the grammar; it
-- is the independence relation doing work, and this is the measurement
-- of exactly how much.
-- ==================================================================

-- Every name below is qualified: `Full` and `Conc` are the SAME module
-- at two independence relations, so every one of them -- `Deriv`, `⊤G`,
-- `run`, even `NT` -- exists twice, and that is precisely the claim
-- being made.
module Control where

  derivesFull! : Full._⊢_ (Full.⊤G {tt}) (Full.Δ Bool)
  derivesFull! = Full._∘g_ (Full.okA (Full.Deriv Full.log)
                                     (Full.¬G_ (Full.Deriv Full.log)))
                           (Full.derives? Full.log)

  -- the valid logs are still valid -- ⊤I only ADDS splittings
  _ : passes (Full.run derivesFull! at ( logOK ↦ true ∷ logMsg ↦ true ∷ [] ))
  _ = refl

  -- ... and so, WRONGLY, is the out-of-order one
  _ : passes (Full.run derivesFull! at ( badOrder ↦ true ∷ [] ))
  _ = refl

  -- the same `witness` call as above, one `Fibered` over: at ⊤ the
  -- parser hands back a derivation of a log that violates the protocol
  wrong-at-⊤ : Full.Deriv Full.log badOrder
  wrong-at-⊤ = Full.witness (Full.Deriv Full.log)
                            (Full.¬G_ (Full.Deriv Full.log))
                            (Full.derives? Full.log) badOrder refl

-- ==================================================================
-- WHAT THE PARSE FOUND: the log, DEMULTIPLEXED.
--
-- `Protocol.logIsShuffle` is the specification as a term -- a `log`
-- derivation IS a shuffle of two session derivations -- so applying it
-- to a witness exposes the shuffle, whose splitting is the pair of
-- per-session traces.  Reading `.fst` off a splitting is leaving the
-- calculus, which is why it happens HERE, at the observation, and not
-- in any definition.
-- ==================================================================

sessionTraces : (w : Word) → Deriv log w → Word × Word
sessionTraces w d = let (u , v , _) = logIsShuffle w d .fst in u , v

-- the parser did not merely accept `logOK`; it recovered which events
-- belong to which session
_ : sessionTraces logOK overlapping ≡ ((o₀ ∷ c₀ ∷ []) , (o₁ ∷ c₁ ∷ []))
_ = refl

_ : sessionTraces logMsg with-messages
    ≡ ((o₀ ∷ m₀ ∷ c₀ ∷ []) , (o₁ ∷ m₁ ∷ c₁ ∷ []))
_ = refl

-- ==================================================================
-- THE ACCOUNTING -- reused unchanged vs. written fresh.
--
-- REUSED, NOT ONE TOKEN CHANGED:
--
--   the promodel          `Traces/Base`: carrier `Word`, `Split` the
--                         I-shuffle.  Written for another purpose.
--   the enumeration       `Traces/Enumeration.shuffles` + `complete`.
--                         This is the expensive combinatorial content
--                         -- "list every way this log splits into two
--                         concurrent factors" -- and a hand-written
--                         interleaving checker is mostly this function.
--                         It was already here.
--   the decision kernel   `Decidable/Guarded` (`▷ᴬ`, `löbᵍ`, `dec-⊗▷`,
--                         `resourceOf`), `Decidable/Enumerated`
--                         (`dec-⊗-cuts`, `slotMiss`),
--                         `Decidable/Listable` (`dec-⊕ᴰ`, `dec-&ᴰ`),
--                         `Decidable/Additive` (`dec-map`, `¬G`),
--                         `Decidable/Representable` (`dec-⌈⌉`).
--   the descriptions      `Inductive` / `Grading` / `Automaton.Guard`:
--                         `⊕e`/`&e`/`⊗e`/`⌜_⌝`, `μ`, `Guarded`.
--   the observations      `SemanticAction`: `run`, `okA`, `witness`,
--                         `refute`, `passes`.
--
-- WRITTEN FRESH, and honestly:
--
--   trGraded (~25 lines)  the grading.  Four inductions on `ITr`
--                         (`itrLenL`, `itrLenR`, and their strict
--                         versions) saying a shuffle's factors are
--                         subwords.  THIS IS THE ONLY NEW MATHEMATICS
--                         IN THE FILE, and it is the fact that makes
--                         the recursion terminate.  `Strings/Graded`
--                         proves the same four for concatenation.
--   NonTrivial, trCase,   the resource predicate and its probe.  Copied
--   probe-NT, ntProper    from `Strings/{Graded,Decomposition}` with
--   (~20 lines)           `cons nil` replaced by `left (itrNil Ind w)`.
--   Liftg/liftg/lowerg    three lines `Strings/Connectives` also has;
--                         `Traces/Base` had not needed them.
--   module CYK            A COPY of `Strings/CYK`, with `strGraded` ->
--   (~90 lines)           `trGraded` and `cuts` -> `shuffles`.  Two
--                         tokens.  This is a real cost and it is not
--                         hidden: `Decidable/Guarded`'s closing note
--                         says the chart cannot yet be assembled
--                         generically, because an `Ix`-family is not a
--                         grammar, and `Strings/CYK` and `Spans/CYK`
--                         are already the same forty lines twice.  This
--                         is the third instance of a duplication the
--                         framework has already diagnosed -- not a new
--                         obstruction found by the shuffle.
--   the alphabet          `Sid`/`Act`/`Ind`/`Discrete` and the grammar
--   and the grammar       `NT`/`unitR`/`binR`/`allRules`.  Input, not
--                         machinery.
--
-- THE CLAIM, STATED PRECISELY.  No new ALGORITHM was written.  The
-- decision procedure -- `decRow`/`decBin`/`decSlot`/`step`/`chart` --
-- is character-for-character `Instances.Strings.CYK.Decide`; the only
-- differing argument is the list of splittings it scans.  A
-- hand-written checker for "is this log a valid interleaving of N
-- sessions" would have to enumerate interleavings, propagate
-- per-session state, and then be proved sound and complete separately.
-- Here the enumeration was already a component of the promodel, the
-- per-session state is the CFG, and soundness/completeness are the two
-- branches of `Dec⟨_⟩` -- which is why `bad-out-of-order` above is a
-- THEOREM and not a report.
--
-- THE CONTROLLED EXPERIMENT.  `Protocol.Over` is parameterised by the
-- independence relation and instantiated twice, so `Conc` and `Full`
-- share every line of source.  `bad-out-of-order` (a refutation) and
-- `Control.wrong-at-⊤` (a derivation of the SAME log) are the same call
-- to the same procedure over two `Fibered`s.  That pair is the sharpest
-- statement this file can make: the algorithm is a constant of the
-- experiment, and the promodel is the variable.
--
-- WHAT WOULD MAKE THE CLAIM UNCONDITIONAL: lifting `module Decide` out
-- of the three instances into a functor over `GradedFib` + a splitting
-- enumeration.  That is the `DecDesc` note in `Decidable/Guarded`, and
-- this file is a third data point that it is worth doing.
-- ==================================================================
