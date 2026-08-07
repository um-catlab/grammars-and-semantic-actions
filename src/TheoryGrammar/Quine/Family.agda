{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE QUINE FAMILY, and the shape of the fixpoint.

  `Quine.Tiny` pins one four-letter program.  There are more: for ANY
  nonempty bit string `a` beginning with the opcode `0`,

      quine a  =  a ++ "#" ++ enc a

  is a quine, because the interpreter at opcode `0` prints
  `dec(data) ++ "#" ++ enc(dec(data))` and `dec (enc a) = a`.  Writing
  the program as `quine a` rather than as a list of letters is not a
  shortcut: `quine a` REDUCES to that list, and both sides of every test
  below are the same expression, so a test says exactly "the output of
  this text is this text".

  The point of the file is the SCALE: the same `refl` at 4, 7, 13, 25
  and 49 letters, each one a full run of the decision procedure and the
  interpreter.  Beyond about 250 letters the evaluator gives out; see
  the note at the end of `Quine.Meta`.
-}
module TheoryGrammar.Quine.Family where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.List
open import Cubical.Data.Maybe using (Maybe; just; nothing)

open import TheoryGrammar.SemanticAction using (passes; _↦_; _at_)
open import TheoryGrammar.Quine.Base

-- the family, as a function of its code half
quine : String → String
quine a = a ++ (c# ∷ enc a)

-- ==================================================================
-- FIVE MEMBERS, at five sizes.  4, 7, 13, 25, 49 letters.
-- ==================================================================

a1 a2 a4 a8 a16 : String
a1  = c0 ∷ []
a2  = c0 ∷ c1 ∷ []
a4  = c0 ∷ c1 ∷ c1 ∷ c0 ∷ []
a8  = c0 ∷ c1 ∷ c1 ∷ c0 ∷ c1 ∷ c0 ∷ c0 ∷ c1 ∷ []
a16 = c0 ∷ c1 ∷ c1 ∷ c0 ∷ c1 ∷ c0 ∷ c0 ∷ c1 ∷ c1 ∷ c0 ∷ c0 ∷ c1 ∷ c0 ∷ c1 ∷ c1 ∷ c0 ∷ []

_ : passes (runOut ntS at
             ( quine a1  ↦ just (quine a1)         --  4 letters
             ∷ quine a2  ↦ just (quine a2)         --  7
             ∷ quine a4  ↦ just (quine a4)         -- 13
             ∷ quine a8  ↦ just (quine a8)         -- 25
             ∷ quine a16 ↦ just (quine a16)        -- 49
             ∷ [] ))
_ = refl

-- ==================================================================
-- AND WHAT IS NOT A QUINE.
--
-- The condition is `a = dec(e)` AND `e = enc(a)` AND opcode `0`;
-- breaking any of the three breaks the fixpoint, and each of these says
-- what the text prints INSTEAD.  A program whose data is not the quoted
-- form of its code prints some OTHER program of the family.
-- ==================================================================

-- opcode `1`: the interpreter prints the quoted half first, so the
-- output does not even begin with a bit.  (That opcode 1 has NO quine
-- is argued in `Quine.Base`'s header; what is checked here is only that
-- these two texts print something else.)
_ : passes (runOut ntS at
             ( (c1 ∷ c# ∷ c1 ∷ c1 ∷ [])
                 ↦ just (c1 ∷ c1 ∷ c# ∷ c1 ∷ [])
             ∷ (c1 ∷ c0 ∷ c# ∷ c1 ∷ c1 ∷ c0 ∷ c0 ∷ [])
                 ↦ just (c1 ∷ c1 ∷ c0 ∷ c0 ∷ c# ∷ c1 ∷ c0 ∷ [])
             ∷ [] ))
_ = refl

-- right opcode, wrong data: it prints the quine whose code its data
-- decodes to.  Applying the interpreter to its own output would then
-- reach a fixpoint -- the standard "one step to a quine".
_ : passes (runOut ntS at
             ( (c0 ∷ c1 ∷ c# ∷ c0 ∷ c1 ∷ c1 ∷ c0 ∷ [])   -- data decodes to `01`
                 ↦ just (quine a2)
             ∷ (c1 ∷ c1 ∷ c# ∷ c0 ∷ c0 ∷ c0 ∷ c0 ∷ [])   -- code `11`, data → `00`
                 ↦ just (c0 ∷ c0 ∷ c0 ∷ c0 ∷ c# ∷ c0 ∷ c0 ∷ [])
             ∷ [] ))
_ = refl

-- ... and ONE STEP LATER it is a quine: the output of `01#0110` is
-- `01#0011`, and THAT is a fixpoint.  (`quine a2` is `01#0011`.)
_ : passes (runOut ntS at (quine a2 ↦ just (quine a2) ∷ []))
_ = refl
