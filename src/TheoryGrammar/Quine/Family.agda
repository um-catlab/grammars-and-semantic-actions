{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- THE QUINE FAMILY, and the shape of the fixpoint. -}
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

-- FIVE MEMBERS, at five sizes.  4, 7, 13, 25, 49 letters.

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

-- AND WHAT IS NOT A QUINE. The condition is `a = dec(e)` AND `e = enc(a)`
-- AND opcode `0`; breaking any of the three breaks the fixpoint, and each
-- of these says what the text prints INSTEAD.

-- opcode `1`: the interpreter prints the quoted half first, so the output
-- does not even begin with a bit.
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
