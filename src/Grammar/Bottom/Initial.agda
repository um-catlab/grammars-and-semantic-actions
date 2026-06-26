{- `⊥*` is the initial object of `|GRAMMAR| ℓ` (Term.Category).

   `Initial' C = Terminal' (C ^op)`: in the opposite category the terminal
   object is `⊥*`, with the unique arrow given by `⊥*`-elimination
   (`is-initial-⊥*`).
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Bottom.Initial (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Empty as Empty hiding (⊥ ; ⊥*)

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Opposite
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.Initial

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Bottom.Base Alphabet
open import Grammar.Bottom.Properties Alphabet
open import Term.Base Alphabet
open import Term.Category Alphabet

private
  variable
    ℓ : Level

opaque
  unfolding ⊥*
  isSetGrammar⊥* : ∀ {ℓ} → isSetGrammar (⊥* {ℓ})
  isSetGrammar⊥* w = isProp→isSet (λ x → Empty.rec (lower x))

⊥SetGrammar : SetGrammar ℓ
⊥SetGrammar = ⊥* , isSetGrammar⊥*

|GRAMMAR|-Terminal^op : Terminal ((|GRAMMAR| ℓ) ^op)
|GRAMMAR|-Terminal^op .fst = ⊥SetGrammar
|GRAMMAR|-Terminal^op .snd y .fst = is-initial-⊥* .fst
|GRAMMAR|-Terminal^op .snd y .snd f = is-initial-⊥* .snd f

|GRAMMAR|-Initial' : Initial' (|GRAMMAR| ℓ)
|GRAMMAR|-Initial' = terminalToUniversalElement |GRAMMAR|-Terminal^op
