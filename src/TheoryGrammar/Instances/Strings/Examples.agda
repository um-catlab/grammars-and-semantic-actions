{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Worked examples at a two-letter alphabet: a parse, a star, and CYK. -}
module TheoryGrammar.Instances.Strings.Examples where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool
open import Cubical.Data.List
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Instances.Strings.CYK Bool

-- the grammar `a b` over the two-letter alphabet
ab : Gr
ab = literal true ⊗' literal false

parse-ab : ab (true ∷ false ∷ [])
parse-ab = ⊗-mk (cons nil) Eq.refl Eq.refl

-- a two-element star, built from the star's combinators rather than
-- from constructors of a bespoke datatype
aa : KL* (literal true) (true ∷ true ∷ [])
aa = cons* _ (⊗-mk (cons nil) Eq.refl
       (cons* _ (⊗-mk (cons nil) Eq.refl
         (nil* _ ε-mk))))

-- ================================================================
-- CYK at a two-letter alphabet:  S → A B,  A → 'a',  B → 'b'
-- (true = 'a', false = 'b').
-- ================================================================

data NT : Type₀ where ntS ntA ntB : NT

unitR : NT → Bool → Bool
unitR ntS c = false
unitR ntA c = c
unitR ntB c = not c

binR : NT → NT → NT → Bool
binR ntS ntA ntB = true
binR _   _   _   = false

open CYK NT (ntS ∷ ntA ∷ ntB ∷ []) unitR binR

-- "ab" is derivable from S
_ : cyk (true ∷ false ∷ []) ≡ (ntS ∷ [])
_ = refl

-- "ba" is not
_ : cyk (false ∷ true ∷ []) ≡ []
_ = refl

-- single letters get their unit rules
_ : cyk (true ∷ []) ≡ (ntA ∷ [])
_ = refl
