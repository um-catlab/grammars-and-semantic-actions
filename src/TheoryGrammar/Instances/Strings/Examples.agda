{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Worked examples at a two-letter alphabet: a parse, a star, and CYK. -}
module TheoryGrammar.Instances.Strings.Examples where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Sigma
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

-- CYK at a two-letter alphabet:  S → A B,  A → 'a',  B → 'b'
-- (true = 'a', false = 'b').  Rules are TYPES, so a rule may carry
-- evidence rather than just a Bool.

data NT : Type₀ where ntS ntA ntB : NT

unitR : NT → Bool → Type₀
unitR ntS c = ⊥
unitR ntA c = c Eq.≡ true
unitR ntB c = c Eq.≡ false

binR : NT → NT → NT → Type₀
binR ntS ntA ntB = Unit
binR _   _   _   = ⊥

open CYK NT unitR binR

-- the two leaves ...
leafA : Deriv ntA (true ∷ [])
leafA = G.sup (inl (true , Eq.refl) , lift Eq.refl) λ ()

leafB : Deriv ntB (false ∷ [])
leafB = G.sup (inl (false , Eq.refl) , lift Eq.refl) λ ()

-- ... and a parse tree for "ab" from S.  The type is a GRAMMAR, so the
-- word it parses is in the index and cannot drift from the tree.
parseAB : Deriv ntS (true ∷ false ∷ [])
parseAB = G.sup
  ( inr (ntA , ntB , tt)
  , (((true ∷ []) , (false ∷ []) , cons nil)
    , λ { true  → λ { true → tt* ; false → lift ≤-refl }
        ; false → λ { true → tt* ; false → lift ≤-refl } }) )
  λ { (true  , (true  , _)) → leafA
    ; (false , (true  , _)) → leafB
    ; (true  , (false , ()))
    ; (false , (false , ())) }
