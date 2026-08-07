{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE QUINES, RUN.

  Every `refl` below is the decision procedure filling its chart at
  typecheck time and the interpreter running on the parse tree it
  produced.  Nothing is postulated and nothing is assumed to terminate:
  if the parse did not evaluate, the file would not compile.
-}
module TheoryGrammar.Quine.Tiny where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.List
open import Cubical.Data.Unit
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.SemanticAction using (passes; _↦_; _at_)
open import TheoryGrammar.Quine.Base

-- ==================================================================
-- §0  THE SOURCE TEXT.  Written ONCE.  Everything below refers to this
--     name, so no test can drift from the text it is about.
-- ==================================================================

-- the four-character program   0 # 0 0
src : String
src = c0 ∷ c# ∷ c0 ∷ c0 ∷ []

-- ==================================================================
-- §1  IT PARSES -- and the parse tree is a THEOREM, not a report.
-- ==================================================================

_ : passes (run (derives! ntS) at (src ↦ true ∷ []))
_ = refl

selfDeriv : Deriv ntS src
selfDeriv = witness (Deriv ntS) (¬G Deriv ntS) (derives? ntS) src refl

-- ... and `⌈_⌉` PINS the text.  `⌈ src ⌉` is the grammar that holds at
-- one world and that world is the literal source, so this term says
-- "the source text, and nothing else, derives from S".  The `Eq.refl`
-- hiding inside `⌈⌉-E` is the whole of the pinning.
selfLit : ⌈ src ⌉ ⊢ Deriv ntS
selfLit = ⌈⌉-E selfDeriv

-- ==================================================================
-- §2  ... AND IT PRINTS ITSELF.
--
-- THE QUINE EQUATION, stated in the calculus.  `⌈ src ⌉ ⊢ Δ String` is
-- by Yoneda (`⌈⌉-UP`) just a string, read off at the point
-- `⌈⌉-pt src = Eq.refl`; the left side is "parse the source and run
-- it", the right side is the source itself.
--
--     ⌈ src ⌉  --selfLit-->  Deriv S  --interp-->  Δ String
--
-- and `refl` says that composite is the identity on the text.
-- ==================================================================

quine : (interp ntS ∘g selfLit) src (⌈⌉-pt src) ≡ (src , tt)
quine = refl

-- the same fact through the whole pipeline -- decide, then interpret --
-- with the parser's own failure branch in play
_ : passes (runOut ntS at (src ↦ just src ∷ []))
_ = refl

-- ==================================================================
-- §3  THE PROPERTY IS NOT FREE.  Neighbours of the quine, and what
--     they print instead.  If `emit` were the identity every string
--     would pass; these are what says it is not.
-- ==================================================================

-- `1#11` has the OTHER opcode, which prints the quoted data first
_ : passes (runOut ntS at ((c1 ∷ c# ∷ c1 ∷ c1 ∷ []) ↦ just (c1 ∷ c1 ∷ c# ∷ c1 ∷ [])) ∷ [])
_ = refl

-- `0#01` decodes to `0`, so it prints the quine -- but it is not one
_ : passes (runOut ntS at ((c0 ∷ c# ∷ c0 ∷ c1 ∷ []) ↦ just src ∷ []))
_ = refl

-- `0#10` decodes to `1`, and prints a different program altogether
_ : passes (runOut ntS at
             ((c0 ∷ c# ∷ c1 ∷ c0 ∷ []) ↦ just (c1 ∷ c# ∷ c1 ∷ c1 ∷ [])) ∷ [])
_ = refl

-- ==================================================================
-- §4  AND THE LANGUAGE IS NOT EVERYTHING.  A negative answer here is a
--     REFUTATION (the error grammar is `¬G _`), so these are theorems
--     that no parse tree exists -- not reports that none was found.
-- ==================================================================

_ : passes (run (derives! ntS) at
             ( (c0 ∷ c# ∷ c0 ∷ [])           ↦ false   -- odd data
             ∷ (c# ∷ c0 ∷ c0 ∷ [])           ↦ false   -- no code
             ∷ (c0 ∷ c0 ∷ [])                ↦ false   -- no hash
             ∷ (c0 ∷ c# ∷ [])                ↦ false   -- no data
             ∷ [] ))
_ = refl

noDeriv : (w : String) → run (derives! ntS) w ≡ false → (¬G Deriv ntS) w
noDeriv = refute (Deriv ntS) (¬G Deriv ntS) (derives? ntS)

-- `0#0` -- an odd-length datum -- is NOT a program, and this is a proof
no-odd : Deriv ntS (c0 ∷ c# ∷ c0 ∷ []) → E.⊥* {ℓ-zero}
no-odd = noDeriv (c0 ∷ c# ∷ c0 ∷ []) refl
