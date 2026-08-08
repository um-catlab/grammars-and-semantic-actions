{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- THE DYCK PARSER AT A LEXED UNICODE ALPHABET. `Instances.Strings.DyckDec`
   proves the parser generically in the alphabet; this file instantiates it
   so that test cases can be written as ORDINARY STRING LITERALS.
   ================================================================== WHY A
   LEXER RATHER... -}
module TheoryGrammar.Instances.Strings.DyckLex where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.List
open import Cubical.Data.Maybe using (Maybe; just; nothing)
import Cubical.Data.Equality as Eq

-- the builtins.  `String` is the THEORY's word type, so Agda's is `Text`
open import Agda.Builtin.String renaming (String to Text) using (primStringToList)
open import Agda.Builtin.Char   using (Char; primCharEquality)
open import Agda.Builtin.List   renaming (List to BList; [] to bnil; _∷_ to bcons)

open import TheoryGrammar.Enumerable using (No)
open import TheoryGrammar.SemanticAction using (passes; _↦_; _at_)

-- THE TOKENS, and the lexer.  Total by construction.

data Tok : Type₀ where
  lparT rparT junkT : Tok

lexChar : Char → Tok
lexChar c =
  if primCharEquality c '('
    then lparT
    else (if primCharEquality c ')' then rparT else junkT)

private
  conv : BList Char → List Tok
  conv bnil         = []
  conv (bcons c cs) = lexChar c ∷ conv cs

-- A STRING LITERAL, as a word of the theory.
tok : Text → List Tok
tok s = conv (primStringToList s)

-- PRIMITIVE (phase 1).  The one external input: the tokens are
-- distinguishable.  No postulate, no appeal to a primitive's injectivity.
decEqTok : (a b : Tok) → (a Eq.≡ b) ⊎ No (a Eq.≡ b)
decEqTok lparT lparT = inl Eq.refl
decEqTok rparT rparT = inl Eq.refl
decEqTok junkT junkT = inl Eq.refl
decEqTok lparT rparT = inr λ ()
decEqTok lparT junkT = inr λ ()
decEqTok rparT lparT = inr λ ()
decEqTok rparT junkT = inr λ ()
decEqTok junkT lparT = inr λ ()
decEqTok junkT rparT = inr λ ()

-- the string theory at this alphabet, for `run` / `Δ`
open import TheoryGrammar.Instances.Strings.Enumeration Tok

-- ... and the parser, instantiated
open import TheoryGrammar.Instances.Strings.DyckDec Tok decEqTok lparT rparT

-- VERIFIED TEST CASES, WRITTEN AS STRING LITERALS.

_ : passes (run dyckTree! at
             ( tok ""       ↦ just εT
             ∷ tok "()"     ↦ just (nodeT εT εT)
             ∷ [] ))
_ = refl

-- the two length-4 words are told apart by WHERE the nesting sits --
-- which is what a Boolean cannot say
_ : passes (run dyckTree! at
             ( tok "(())"   ↦ just (nodeT (nodeT εT εT) εT)
             ∷ tok "()()"   ↦ just (nodeT εT (nodeT εT εT))
             ∷ [] ))
_ = refl

_ : passes (run dyckTree! at
             ( tok "(()())" ↦ just (nodeT (nodeT εT (nodeT εT εT)) εT)
             ∷ tok "((()))" ↦ just (nodeT (nodeT (nodeT εT εT) εT) εT)
             ∷ [] ))
_ = refl

-- REFUTATIONS.  The middle two have equal bracket counts, so a counting
-- check accepts them; the last two contain junk the lexer flagged.
_ : passes (run dyckTree! at
             ( tok ")("     ↦ nothing
             ∷ tok "(("     ↦ nothing
             ∷ tok "())("   ↦ nothing
             ∷ tok ")(()"   ↦ nothing
             ∷ tok "(a)"    ↦ nothing
             ∷ tok "()x"    ↦ nothing
             ∷ [] ))
_ = refl

-- and the Boolean shadow, for the record
_ : passes (run dyck! at
             ( tok "(())"   ↦ true
             ∷ tok "(()"    ↦ false
             ∷ [] ))
_ = refl
