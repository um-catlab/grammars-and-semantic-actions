{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  WHAT `Chain.Project` IS MISSING, AND THE SIX LINES THAT SUPPLY IT.

  `Chain.Project` says a stage is an IR with a printer and a projection
  is a backward map that PRINTS THE SAME THING:

      record B ↘ A where
        bwd   : B .Ir → A .Ir
        faith : (b : B .Ir) → A .says (bwd b) ≡ B .says b

  A COMPILER ERROR IS NOT AN OBJECT OF ANY STAGE, so it cannot be
  carried by `↘` as it stands, and it is worth saying exactly why rather
  than adding a field to `Stage`:

    -- `Stage` has no error slot, and giving it one would be wrong.  The
       failure of a pass is not a second kind of IR; the passes' error
       grammars already live INSIDE the calculus (`TheoryGrammar.Result`
       -- `⊤G ⊢ Result E A`), which is where they belong.

    -- The thing that has no home is the LOCATION.  A diagnostic is a
       piece of an earlier IR (WHERE) together with a sentence about it
       (WHAT), and `↘`'s `faith` is exactly the guarantee a diagnostic
       needs: that carrying the WHERE down the cascade does not silently
       change what is being pointed at.

  So the minimal extension is not a new field on `Stage` and not a
  weakening of `↘`.  It is one record and one map:

      Diagnostic A  =  site : A .Ir  ×  msg : String
      along : B ↘ A → Diagnostic B → Diagnostic A

  `Diagnostic` is a FUNCTOR ON THE STAGE CATEGORY -- `along idProj` is
  the identity and `along (p ∘↘ q)` is the composite, both by `refl` --
  and `alongSays` is the whole content: after moving a diagnostic from a
  late stage to an early one, the text at the early stage is the text
  the late stage would have printed.  That is `faith`, used, and it is
  why nothing has to be re-proved to point a stage-3 error at stage-0
  characters.

  Nothing here mentions linearity, spans, or a tape: this is the generic
  layer, and `Chain.Locate` is the instance.
-}
open import Cubical.Foundations.Prelude

module Chain.Diagnostic where

open import Agda.Builtin.String using () renaming (String to UString)

open import Chain.Project

-- ==================================================================
-- §1  A DIAGNOSTIC, LOCATED AT A STAGE.
--
-- `site` is a piece of that stage's IR -- the subterm the message is
-- about -- and `msg` is the sentence.  The site is an `Ir` and NOT a
-- span, deliberately: spans are one stage's way of locating and the
-- cascade has six stages, so the location has to be stated in the
-- vocabulary every stage already has.
-- ==================================================================

record Diagnostic (A : Stage) : Type₀ where
  constructor mkDiag
  field
    msg  : UString          -- WHAT is wrong
    site : A .Ir            -- ... and WHERE

open Diagnostic public

-- ==================================================================
-- §2  A DIAGNOSTIC TRAVELS DOWN THE CASCADE.
--
-- This is the missing map, and it is the projection applied to the
-- site.  Note what is NOT needed: no error slot on `Stage`, no
-- weakening of `faith`, and no per-stage code -- `ldb↘chr` is already a
-- composite of six links, so `along ldb↘chr` points a stage-3
-- diagnostic at stage-0 characters with nothing written.
-- ==================================================================

along : {A B : Stage} → B ↘ A → Diagnostic B → Diagnostic A
along p d .msg  = d .msg
along p d .site = p .bwd (d .site)

-- THE POINT.  `faith` says the projection prints the same program; read
-- at a diagnostic it says the message did not start describing
-- something else on the way down.  This is the only theorem in the file
-- and it is `Chain.Project`'s, applied.
alongSays : {A B : Stage} (p : B ↘ A) (d : Diagnostic B)
          → A .says (along p d .site) ≡ B .says (d .site)
alongSays p d = p .faith (d .site)

-- ... and functoriality, so a diagnostic may be moved one stage at a
-- time or all at once, with the same answer.  Both are `refl`, which is
-- the reason `along` is the right definition rather than a plausible
-- one.
along-id : {A : Stage} (d : Diagnostic A) → along idProj d ≡ d
along-id d = refl

along-∘ : {A B C : Stage} (p : B ↘ A) (q : C ↘ B) (d : Diagnostic C)
        → along (p ∘↘ q) d ≡ along p (along q d)
along-∘ p q d = refl

-- ==================================================================
-- §3  READING ONE OUT.  A diagnostic is reported by saying its message
-- and then showing the text of its site AT WHATEVER STAGE the reader
-- speaks; `alongSays` is what makes the choice of stage immaterial.
-- ==================================================================

saysSite : (A : Stage) → Diagnostic A → UString
saysSite A d = A .says (d .site)

-- `saysSite` commutes with `along`: the site's text does not depend on
-- the stage it is read at.  (Same statement as `alongSays`, in the
-- vocabulary a reporter uses.)
saysSite-along : {A B : Stage} (p : B ↘ A) (d : Diagnostic B)
               → saysSite A (along p d) ≡ saysSite B d
saysSite-along = alongSays

-- ... and the two objects at DIFFERENT stages that one message points
-- at are comparable, through what they say -- `Chain.Project.sameSay`,
-- specialised.
sameSite : {A B : Stage} (p : B ↘ A) (d e : Diagnostic B)
         → saysSite A (along p d) ≡ saysSite A (along p e)
         → saysSite B d ≡ saysSite B e
sameSite p d e = sameSay p (d .site) (e .site)
