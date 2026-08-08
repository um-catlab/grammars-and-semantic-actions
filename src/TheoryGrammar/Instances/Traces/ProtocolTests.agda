{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- THE PROTOCOL LOG, DECIDED -- and the accounting. -}
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

-- The six events, and the logs.

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

-- (1) THE SEARCH SPACE, COUNTED. The two endpoints of the trace family
-- (`Traces/Ordered` and `Traces/Commutative`) instantiated at this
-- alphabet, purely to measure.

module OrdI = TrOrd Ev
module ComI = TrCom Ev

dec⊥ : (x y : Ev) → OrdI.⊥I x y ⊎ No (OrdI.⊥I x y)
dec⊥ x y = inr λ ()

isProp⊥I : (x y : Ev) → isProp (OrdI.⊥I x y)
isProp⊥I x y = E.isProp⊥

module Cat = TrE Ev OrdI.⊥I dec⊥ isProp⊥I   -- concatenation

-- ... and full interleaving is `Protocol.Full`, the ⊤ endpoint the control
-- below runs the parser at.
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

-- (2)  THE ANSWERS.

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

-- (3) THE ANSWERS AS THEOREMS. `run … ≡ true/false` is an observation.

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

-- THE ONE THAT SEPARATES TRACES FROM BAGS. `badOrder` has exactly the
-- events of `logOK`, permuted; it is refuted because `Ind` does not relate
-- a session to itself, so no `right` step may carry `o₀` past `c₀`.
bad-out-of-order : Deriv log badOrder → E.⊥* {ℓ-zero}
bad-out-of-order =
  refute (Deriv log) (¬G Deriv log) (derives? log) badOrder refl

-- THE CONTROL: THE SAME PARSER AT THE ⊤ ENDPOINT. `Protocol.Full` is
-- `Protocol.Over` at `⊤I` -- every pair of events commutes, so the
-- splittings are the free COMMUTATIVE monoid's, which `Traces/Commutative`
-- proves are `Instances.Bags`' interleavings.

-- Every name below is qualified: `Full` and `Conc` are the SAME module at
-- two independence relations, so every one of them -- `Deriv`, `⊤G`,
-- `run`, even `NT` -- exists twice, and that is precisely the claim being
-- made.
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

-- WHAT THE PARSE FOUND: the log, DEMULTIPLEXED.

sessionTraces : (w : Word) → Deriv log w → Word × Word
sessionTraces w d = let (u , v , _) = logIsShuffle w d .fst in u , v

-- the parser did not merely accept `logOK`; it recovered which events
-- belong to which session
_ : sessionTraces logOK overlapping ≡ ((o₀ ∷ c₀ ∷ []) , (o₁ ∷ c₁ ∷ []))
_ = refl

_ : sessionTraces logMsg with-messages
    ≡ ((o₀ ∷ m₀ ∷ c₀ ∷ []) , (o₁ ∷ m₁ ∷ c₁ ∷ []))
_ = refl

-- THE ACCOUNTING -- reused unchanged vs. written fresh.
