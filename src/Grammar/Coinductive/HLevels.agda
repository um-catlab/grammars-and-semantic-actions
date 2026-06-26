open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Coinductive.HLevels (Alphabet : hSet ℓ-zero) where

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Inductive.SetValued Alphabet
open import Grammar.Coinductive.Indexed Alphabet

private
  variable
    ℓX : Level

-- The final coalgebra `ν F` of a set-preserving strictly-positive functor is a
-- set.  `ν F x w` is a single-field coinductive record (`unroll : ⟦F x⟧ (ν F) w`)
-- so by record-η it is a *retract* of `⟦F x⟧ (ν F) w`; `isSet⟦F⟧` turns
-- set-ness of the carriers (the corecursive hypothesis) into set-ness of that.
-- The corecursive self-reference is productive — discharged with TERMINATING,
-- exactly as the corecursor/ν-η in Grammar.Coinductive.Indexed.
module _ {X : Type ℓX} (F : X → SPFunctor X) (isSetValF : ∀ x → isSetValued (F x)) where
  {-# TERMINATING #-}
  isSetGrammarν : ∀ x → isSetGrammar (ν F x)
  isSetGrammarν x w =
    isSetRetract (λ t → t .unroll) wrap retr
      (isSet⟦F⟧ (F x) (isSetValF x) (λ y → ν F y , isSetGrammarν y) w)
    where
      wrap : ⟦ F x ⟧ (ν F) w → ν F x w
      wrap z .unroll = z
      retr : ∀ t → wrap (t .unroll) ≡ t
      retr t i .unroll = t .unroll
