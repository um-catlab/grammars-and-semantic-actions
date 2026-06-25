{- The μ-independent set-valuedness predicate on SPFunctor codes.

   `isSetValued` and `isSet⟦F⟧` are carved out of `Grammar.Inductive.HLevels`
   so they can sit *below* `Grammar.Inductive.Indexed` (which needs them, via
   `Grammar.Inductive.Semantic`, to build the semantic functor `⟦SPF⟧Pow`).

   Crucially this module does NOT import `Grammar.Inductive.Indexed`, so there
   is no `Indexed → Semantic → SetValued → Indexed` cycle.

   `Grammar.Inductive.HLevels` re-exports both, so existing importers of
   `HLevels` are unaffected. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Inductive.SetValued (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Sum Alphabet
open import Grammar.Product Alphabet
open import Grammar.Product.Binary.AsPrimitive Alphabet
open import Grammar.LinearProduct.Base Alphabet
open import Grammar.Lift.Base Alphabet
open import Term.Base Alphabet

open import Grammar.Inductive.Functor Alphabet

private
  variable ℓA ℓX : Level

isSetValued : ∀ {X : Type ℓX} → SPFunctor X → Type ℓX
isSetValued (k A) = isSetGrammar A
isSetValued {X = X} (Var x) = Unit*
isSetValued (&e Y F) = ∀ y → isSetValued (F y)
isSetValued (⊕e Y F) = isSet Y × (∀ y → isSetValued (F y))
isSetValued (F ⊗e G) = isSetValued F × isSetValued G
isSetValued (F &e2 G) = isSetValued F × isSetValued G

module _ {X : Type ℓX} where
  isSet⟦F⟧ : ∀ (F : SPFunctor X)
    → isSetValued F
    → (A : X → SetGrammar ℓA)
    → isSetGrammar (⟦ F ⟧ (λ x → ⟨ A x ⟩))
  isSet⟦F⟧ (k _) isSetF A = isSetGrammarLift isSetF
  isSet⟦F⟧ (Var x) isSetF A = isSetGrammarLift (A x .snd)
  isSet⟦F⟧ (&e Y F) isSetF A =
    isSetGrammar&ᴰ (λ b → isSet⟦F⟧ (F b) (isSetF b) A)
  isSet⟦F⟧ (⊕e Y F) isSetF A =
    isSetGrammar⊕ᴰ (isSetF .fst) (λ b → isSet⟦F⟧ (F b) (isSetF .snd b) A)
  isSet⟦F⟧ (Fl ⊗e Fr) isSetF A =
    isSetGrammar⊗ (isSet⟦F⟧ Fl (isSetF .fst) A) (isSet⟦F⟧ Fr (isSetF .snd) A)
  isSet⟦F⟧ (F1 &e2 F2) isSetF A =
    isSetGrammar& (isSet⟦F⟧ F1 (isSetF .fst) A) (isSet⟦F⟧ F2 (isSetF .snd) A)
