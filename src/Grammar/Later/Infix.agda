open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Later.Infix (Alphabet : hSet ℓ-zero) where

open import Cubical.Categories.Direct.Base using (WFOrder)
open import Grammar.Later.InfixOrder Alphabet
import Grammar.Later.Ordered as OrderedLater

{- The infix later modality: ▷ⁱ A x holds when A holds at every *proper
   substring* of x — course-of-values recursion on substrings.  This is the
   CYK shape: the chart of a CYK-style parser is the cofree □ of this
   modality, and lobⁱ is the dynamic program.  All accessors (lobⁱ,
   lobⁱ-unfold, lobⁱ-unique, next⊤ⁱ, and the hylo interface) are inherited
   from the generic Grammar.Later.Ordered at the infix well-order. -}

module InfixLater =
  OrderedLater Alphabet _<ⁱ_ isProp<ⁱ (λ {u} {v} {w} → trans<ⁱ) wf<ⁱ

open InfixLater public
  using ()
  renaming
    ( ▷          to ▷ⁱ
    ; ▷-elim-at  to ▷ⁱ-elim-at
    ; lob        to lobⁱ
    ; next⊤      to next⊤ⁱ
    ; lob-unfold to lobⁱ-unfold
    ; lob-unique to lobⁱ-unique
    ; hylo⟜      to hylo⟜ⁱ
    ; hylo⊸      to hylo⊸ⁱ
    ; hylo&      to hylo&ⁱ
    )

-- The infix well-order, packaged as a record (kept for downstream use).
InfixWFOrder : WFOrder ℓ-zero ℓ-zero
InfixWFOrder = InfixLater.OrdWFOrder
