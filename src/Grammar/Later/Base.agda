open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Later.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Top Alphabet
open import Term.Base Alphabet

open import Cubical.Data.List using (rev)
open import Cubical.Categories.Direct.Base using (WFOrder ; wfPullback)
open import Cubical.Categories.Direct.Instances.Suffix (Alphabet .fst) (Alphabet .snd)
open import Cubical.Categories.Direct.Instances.Poset using (löbWF)

private
  variable
    ℓA : Level
    A : Grammar ℓA

-- The later modality, as the suffix-ordered-strings poset later: ▷ A at x
-- holds when A holds at every *strict suffix* y of x.
▷ : Grammar ℓA → Grammar ℓA
▷ A x = ∀ y → y <ˢ x → A y

-- The general elimination combinator: from a strict-suffix witness, project.
-- Every property of ▷ factors through this rather than through any concrete
-- presentation of the modality.
▷-elim-at : ∀ {x y} → y <ˢ x → ▷ A x → A y
▷-elim-at p α = α _ p

-- Löb induction, recovered from the abstract direct-category construct
-- `löbWF` instantiated at the suffix well-order.
lob : isSetGrammar A → (▷ A ⊢ A) → ⊤ ⊢ A
lob {A = A} isSetA f w _ = löbWF SuffixWFOrder (λ v → A v , isSetA v) f w

-- The strict-prefix well-order, obtained as the pullback of the suffix order
-- along `rev`: w is a strict prefix of w' iff rev w is a strict suffix of
-- rev w'.  This reuses all of the suffix order's proven structure.
PrefixWFOrder : WFOrder ℓ-zero ℓ-zero
PrefixWFOrder = record
  { D       = String
  ; isSetD  = SuffixWFOrder .WFOrder.isSetD
  ; _<_     = λ w w' → rev w <ˢ rev w'
  ; isProp< = λ w w' → isProp<ˢ (rev w) (rev w')
  ; trans<  = trans<ˢ
  ; wf<     = wfPullback rev _<ˢ_ wf<ˢ
  }

-- The right later modality: A holds at every strict *prefix* y of x.
▷r : Grammar ℓA → Grammar ℓA
▷r A x = ∀ y → rev y <ˢ rev x → A y

▷r-elim-at : ∀ {x y} → rev y <ˢ rev x → ▷r A x → A y
▷r-elim-at p α = α _ p

lob-r : isSetGrammar A → (▷r A ⊢ A) → ⊤ ⊢ A
lob-r {A = A} isSetA f w _ = löbWF PrefixWFOrder (λ v → A v , isSetA v) f w
