open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Later.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.List using (rev)
open import Cubical.Categories.Direct.Base using (WFOrder ; wfPullback)
open import Grammar.Later.SuffixOrder Alphabet
import Grammar.Later.Ordered as OrderedLater

{- Both later modalities, their Löb recursions, and the hylo interface are
   instances of the generic Grammar.Later.Ordered at the suffix and prefix
   well-orders.

   Suffix instance (front-consuming; the parser shape):
     ▷ A x = ∀ y → y <ˢ x → A y,
     lob / lob-unfold / lob-unique / next⊤ / hylo⟜ / hylo⊸ / hylo&.

   Prefix instance (back-consuming), obtained by pulling the suffix order
   back along `rev`; every name gets an `r`:
     ▷r A x = ∀ y → rev y <ˢ rev x → A y,
     lob-r / lob-r-unfold / lob-r-unique / next⊤r / hylo⟜r / hylo⊸r / hylo&r. -}

module SuffixLater =
  OrderedLater Alphabet _<ˢ_ isProp<ˢ (λ {u} {v} {w} → trans<ˢ) wf<ˢ

open SuffixLater public hiding (OrdWFOrder)

module PrefixLater =
  OrderedLater Alphabet
    (λ u v → rev u <ˢ rev v)
    (λ u v → isProp<ˢ (rev u) (rev v))
    (λ {u} {v} {w} → trans<ˢ)
    (wfPullback rev _<ˢ_ wf<ˢ)

open PrefixLater public
  using ()
  renaming
    ( ▷          to ▷r
    ; ▷-elim-at  to ▷r-elim-at
    ; lob        to lob-r
    ; next⊤      to next⊤r
    ; lob-unfold to lob-r-unfold
    ; lob-unique to lob-r-unique
    ; hylo⟜      to hylo⟜r
    ; hylo⊸      to hylo⊸r
    ; hylo&      to hylo&r
    )

-- The strict-prefix well-order, as a record (kept for downstream use).
PrefixWFOrder : WFOrder ℓ-zero ℓ-zero
PrefixWFOrder = PrefixLater.OrdWFOrder
