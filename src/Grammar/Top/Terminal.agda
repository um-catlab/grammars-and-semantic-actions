{- `⊤*` is the terminal object of `|GRAMMAR| ℓ` (Term.Category).

   Packaged as the upstream universal-property witness `Terminal'`; nothing is
   redefined — the contractibility data is gsa's `is-terminal-⊤*`.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Top.Terminal (Alphabet : hSet ℓ-zero) where

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Top.Base Alphabet
open import Term.Base Alphabet
open import Term.Category Alphabet

private
  variable
    ℓ : Level

opaque
  unfolding ⊤*
  isSetGrammar⊤* : ∀ {ℓ} → isSetGrammar (⊤* {ℓ})
  isSetGrammar⊤* w = isProp→isSet (λ _ _ → refl)

⊤SetGrammar : SetGrammar ℓ
⊤SetGrammar = ⊤* , isSetGrammar⊤*

|GRAMMAR|-Terminal : Terminal (|GRAMMAR| ℓ)
|GRAMMAR|-Terminal .fst = ⊤SetGrammar
|GRAMMAR|-Terminal .snd y .fst = is-terminal-⊤* .fst
|GRAMMAR|-Terminal .snd y .snd f = is-terminal-⊤* .snd f

|GRAMMAR|-Terminal' : Terminal' (|GRAMMAR| ℓ)
|GRAMMAR|-Terminal' = terminalToUniversalElement |GRAMMAR|-Terminal
