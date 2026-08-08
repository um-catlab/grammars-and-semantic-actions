{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- THE CONCRETE SYNTAX OF THE LINEAR LANGUAGE -- everything a parser needs
   before it is pointed at a word. -}
module TheoryGrammar.Instances.LinLam.Surface where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit
open import Cubical.Data.Empty as E using (⊥)

-- THE TOKENS.

data Tok (Name : Type₀) : Type₀ where
  tvar : Name → Tok Name
  tlam : Name → Tok Name
  tlpar trpar : Tok Name

-- THE ONE LEXICAL CLASS, and its content. `IsVarTok t` DENOTES: "`t` is a
-- variable token".

IsVarTok : {Name : Type₀} → Tok Name → Type₀
IsVarTok (tvar n) = Unit
IsVarTok (tlam n) = ⊥
IsVarTok tlpar    = ⊥
IsVarTok trpar    = ⊥

-- PRIMITIVE (phase 1): the witness IS the name.  There is no clause at
-- the other three tokens because `IsVarTok` is `⊥` there, which is the
-- same fact that makes `decIsVarTok` total.
nameOfTok : {Name : Type₀} (t : Tok Name) → IsVarTok t → Name
nameOfTok (tvar n) _ = n
