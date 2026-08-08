{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- THE CONCURRENT QUINE, RUN. Every `refl` below is the decision procedure
   filling its chart at typecheck time and the interpreter running on the
   parse tree it produced. -}
module TheoryGrammar.Quine.TraceTests where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Empty as E using (⊥)

open import TheoryGrammar.Enumerable using (No)
open import TheoryGrammar.SemanticAction using (passes; _↦_; _at_)
open import TheoryGrammar.Quine.Trace

import TheoryGrammar.Instances.Traces.Protocol   as Pr
import TheoryGrammar.Instances.Traces.Enumeration as TrE

-- §0 THE SOURCE. Written ONCE, as a PAIR of session texts -- because that
-- is what a concurrent program is.

quineA quineB : Wd
quineA = a0 ∷ hsh ∷ []
quineB = b0 ∷ b0 ∷ []

-- the printed trace, as a pair of concurrent streams
out0 : Wd × Wd
out0 = (quineA , quineB)

-- ALL SIX WORDS OF THAT TRACE.  Session 0's two events keep their order
-- and session 1's two keep theirs; everything else is free, which is
-- `Ind` and not the grammar.
w1 w2 w3 w4 w5 w6 : Wd
w1 = a0 ∷ hsh ∷ b0  ∷ b0  ∷ []
w2 = a0 ∷ b0  ∷ hsh ∷ b0  ∷ []
w3 = a0 ∷ b0  ∷ b0  ∷ hsh ∷ []
w4 = b0 ∷ a0  ∷ hsh ∷ b0  ∷ []
w5 = b0 ∷ a0  ∷ b0  ∷ hsh ∷ []
w6 = b0 ∷ b0  ∷ a0  ∷ hsh ∷ []

-- §1 THE SEARCH SPACE, COUNTED. The two endpoints of the trace family at
-- this alphabet, purely to measure: `⊥I` is concatenation (the free
-- monoid) and `⊤I` is full interleaving (the free commutative monoid).

⊥I : Pr.Ev → Pr.Ev → Type₀
⊥I _ _ = ⊥

dec⊥I : (x y : Pr.Ev) → ⊥I x y ⊎ No (⊥I x y)
dec⊥I x y = inr λ ()

isProp⊥I : (x y : Pr.Ev) → isProp (⊥I x y)
isProp⊥I x y = E.isProp⊥

module Cat = TrE Pr.Ev ⊥I dec⊥I isProp⊥I     -- concatenation

_ : length (Cat.shuffles w1) ≡ 5
_ = refl

_ : length (shuffles w1) ≡ 9
_ = refl

_ : length (Full.shuffles w1) ≡ 16
_ = refl

-- §2 IT PARSES, AND IT PRINTS ITSELF -- AT EVERY SPELLING.

_ : passes (run (derives! ntS) at
             ( w1 ↦ true ∷ w2 ↦ true ∷ w3 ↦ true
             ∷ w4 ↦ true ∷ w5 ↦ true ∷ w6 ↦ true ∷ [] ))
_ = refl

_ : passes (runOut ntS at
             ( w1 ↦ just out0 ∷ w2 ↦ just out0 ∷ w3 ↦ just out0
             ∷ w4 ↦ just out0 ∷ w5 ↦ just out0 ∷ w6 ↦ just out0 ∷ [] ))
_ = refl

-- READ `w1` AND `w6`. `w1` spells the code before the data; `w6` spells
-- the whole quoted data before the code.

-- ... and THE QUINE EQUATION, as a term. `IsQuine w refl` is `Prints (what
-- w printed) w` -- the source is one word of the trace it printed -- and
-- `quineAt` discharges it from the `refl` above, through `witness`, so the
-- shuffle exhibiting it is EXTRACTED FROM THE DECISION and never written
-- by hand.
quine1 : IsQuine w1 refl
quine1 = quineAt w1 refl refl

quine2 : IsQuine w2 refl
quine2 = quineAt w2 refl refl

quine3 : IsQuine w3 refl
quine3 = quineAt w3 refl refl

quine4 : IsQuine w4 refl
quine4 = quineAt w4 refl refl

quine5 : IsQuine w5 refl
quine5 = quineAt w5 refl refl

quine6 : IsQuine w6 refl
quine6 = quineAt w6 refl refl

-- ... and it is a FAMILY, not an accident.
bigA bigB : Wd
bigA = a0 ∷ a1 ∷ hsh ∷ []
bigB = b0 ∷ b0 ∷ b1 ∷ b1 ∷ []

wbig : Wd
wbig = a0 ∷ a1 ∷ hsh ∷ b0 ∷ b0 ∷ b1 ∷ b1 ∷ []

_ : length (shuffles wbig) ≡ 20
_ = refl

_ : passes (runOut ntS at (wbig ↦ just (bigA , bigB) ∷ []))
_ = refl

quine-big : IsQuine wbig refl
quine-big = quineAt wbig refl refl

-- §3  THE PROPERTY IS NOT FREE.  Neighbours, and what they print.

-- the OTHER opcode.  `a1` is the opcode `1`, which prints the hash
-- BEFORE the code -- and the source has it after.  What it prints is
-- the ⊤-quine of §5, which at `Ind` is not a program at all.
opc1 : Wd
opc1 = a1 ∷ hsh ∷ b1 ∷ b1 ∷ []

-- the data decodes to `0`, so it prints the quine -- but it is not one
near1 : Wd
near1 = a0 ∷ hsh ∷ b0 ∷ b1 ∷ []

-- the data decodes to `1`, and it prints a different program
near2 : Wd
near2 = a0 ∷ hsh ∷ b1 ∷ b0 ∷ []

_ : passes (runOut ntS at
             ( opc1  ↦ just (hsh ∷ a1 ∷ [] , b1 ∷ b1 ∷ [])
             ∷ near1 ↦ just out0
             ∷ near2 ↦ just (a1 ∷ hsh ∷ [] , b1 ∷ b1 ∷ []) ∷ [] ))
_ = refl

-- ... and each of those is a REFUTATION, not a report: `notQuineAt`
-- says NO interleaving of the two printed streams is this source.
not-quine-opc1 : (¬G Prints (printed opc1 refl)) opc1
not-quine-opc1 = notQuineAt opc1 refl refl

not-quine-near1 : (¬G Prints (printed near1 refl)) near1
not-quine-near1 = notQuineAt near1 refl refl

not-quine-near2 : (¬G Prints (printed near2 refl)) near2
not-quine-near2 = notQuineAt near2 refl refl

-- §4  AND THE LANGUAGE IS NOT EVERYTHING.  A negative answer here is a
--     refutation, so these are theorems that no parse tree exists.

_ : passes (run (derives! ntS) at
             ( (a0 ∷ hsh ∷ b0 ∷ [])       ↦ false   -- odd data
             ∷ (hsh ∷ b0 ∷ b0 ∷ [])       ↦ false   -- no code
             ∷ (a0 ∷ b0 ∷ b0 ∷ [])        ↦ false   -- no hash
             ∷ (a0 ∷ hsh ∷ [])            ↦ false   -- no data
             ∷ [] ))
_ = refl

-- an odd-length datum is not a quoted anything, and this is a proof
no-odd : C.Deriv ntS (a0 ∷ hsh ∷ b0 ∷ []) → E.⊥* {ℓ-zero}
no-odd = noDeriv (a0 ∷ hsh ∷ b0 ∷ []) refl

-- §5 THE CONTROL: THE SAME PARSER AT THE ⊤ ENDPOINT.

topA topB : Wd
topA = hsh ∷ a1 ∷ []
topB = b1  ∷ b1 ∷ []

v1 : Wd
v1 = hsh ∷ a1 ∷ b1 ∷ b1 ∷ []

-- AT `Ind`: not a program.  A theorem, because the error grammar is `¬G _`.
_ : passes (run (derives! ntS) at (v1 ↦ false ∷ []))
_ = refl

no-hash-first : C.Deriv ntS v1 → E.⊥* {ℓ-zero}
no-hash-first = noDeriv v1 refl

-- Every name below is qualified: `Full` and `Conc` are the SAME module
-- at two independence relations, so `C`, `Deriv`, `run`, `Prints` --
-- all of them exist twice, and that is precisely the claim being made.
module Control where

  -- the concurrent quine of §2 is still a quine -- `⊤I` only ADDS
  -- splittings, so an `Ind`-derivation is a `⊤I`-derivation
  _ : passes (Full.runOut ntS at (w1 ↦ just out0 ∷ []))
  _ = refl

  still-a-quine : Full.IsQuine w1 refl
  still-a-quine = Full.quineAt w1 refl refl

  -- ... and so, at `⊤I` ONLY, is the hash-first program
  _ : passes (Full.run (Full.derives! ntS) at (v1 ↦ true ∷ []))
  _ = refl

  _ : passes (Full.runOut ntS at (v1 ↦ just (topA , topB) ∷ []))
  _ = refl

  -- THE ⊤-ONLY QUINE, as a theorem.  Compare `no-hash-first` above:
  -- the same word, the same grammar, the same procedure, one `Fibered`.
  quine-at-⊤ : Full.IsQuine v1 refl
  quine-at-⊤ = Full.quineAt v1 refl refl

-- THE ACCOUNTING. REUSED, NOT ONE TOKEN CHANGED: the alphabet `Protocol`'s
-- `Sid`/`Act`/`Ev`/`Ind`, with its `decInd`/`isPropInd`/`discreteEv`. the
-- `Fibered` `Traces/Base`: carrier `Word`, `Split` the I-shuffle; and
-- `Traces/Enumeration.shuffles`. the parser `Protocol.Over`'s
-- `trGraded`,...
