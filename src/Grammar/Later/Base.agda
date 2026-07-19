open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Later.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Top Alphabet
open import Term.Base Alphabet

open import Cubical.Data.List using (rev)
open import Cubical.Data.Sum using (inl)
open import Cubical.Categories.Direct.Base using (WFOrder ; wfPullback ; DirectStr)
open import Grammar.Later.SuffixOrder Alphabet
open import Cubical.Categories.Direct.Instances.Poset using (PosetCat ; PosetDirect)
import Cubical.Categories.Direct.StrictDownset as SD

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
-- `löbFam` (Löb over presheaves on a direct category) instantiated at the
-- suffix well-order viewed as a thin direct category (`PosetDirect`).  The
-- presheaf-level later `▷Fam` is collapsed back to gsa's first-order
-- `▷ A x = ∀ y → y <ˢ x → A y` via `▷FamApp` at the strict hom `inl y<ˢx`.
private
  lobWF : (Wo : WFOrder ℓ-zero ℓ-zero) {A : WFOrder.D Wo → Type ℓA}
    → (isSetA : ∀ d → isSet (A d))
    → (∀ d → (∀ e → WFOrder._<_ Wo e d → A e) → A d)
    → ∀ d → A d
  lobWF Wo {A = A} isSetA f =
    SD.löbFam dir (λ v → A v , isSetA v)
      (λ x β → f x (λ y y<x → SD.▷FamApp dir (λ v → A v , isSetA v) β (inl y<x) y<x))
    where
      dir : DirectStr {C = PosetCat Wo} Wo
      dir = PosetDirect Wo

lob : isSetGrammar A → (▷ A ⊢ A) → ⊤ ⊢ A
lob {A = A} isSetA f w _ = lobWF SuffixWFOrder isSetA f w

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
lob-r {A = A} isSetA f w _ = lobWF PrefixWFOrder isSetA f w
