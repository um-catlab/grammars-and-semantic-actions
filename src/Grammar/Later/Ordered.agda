{- The later modality, Löb recursion, and the internal hylomorphism
   interface, generically over a well-founded strict order ≺ on String.

   Everything here is internal to the Lambek DSL: the accessors are terms
   `A ⊢ B` and equations between them.  The construction of `lob` is
   inherited from cubical-categorical-logic's presheaf-level Löb (`löbFam`
   over the thin direct category of the order); this module collapses it
   back to the first-order later `▷ A x = ∀ y → y ≺ x → A y` and derives:

     • lob         : (▷ A ⊢ A) → ⊤ ⊢ A          closed Löb
     • lob-unfold  : lob f ≡ f ∘g next⊤ (lob f)  computation rule
     • lob-unique  : any other fixed point equals lob f
     • hylo⟜ / hylo⊸ / hylo&                     open recursion at the
       three function types (⟜, ⊸, ⇒) — the hylomorphism interface;
       the premise `A ⊗ ▷(B ⟜ A) ⊢ B` is "consume part of A, recurse
       later on the strict remainder".

   Instantiated at the suffix and prefix orders in Grammar.Later.Base and
   at the infix (substring) order in Grammar.Later.Infix. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.List using (List)
open import Cubical.Data.Unit using (tt)
open import Cubical.Induction.WellFounded

module Grammar.Later.Ordered
  (Alphabet : hSet ℓ-zero)
  (_≺_ : List ⟨ Alphabet ⟩ → List ⟨ Alphabet ⟩ → Type ℓ-zero)
  (isProp≺ : ∀ u v → isProp (u ≺ v))
  (trans≺ : ∀ {u v w} → u ≺ v → v ≺ w → u ≺ w)
  (wf≺ : WellFounded _≺_)
  where

open import Cubical.Data.Sum using (inl)
open import Cubical.Categories.Direct.Base using (WFOrder ; DirectStr)
open import Cubical.Categories.Direct.Instances.Poset using (PosetCat ; PosetDirect)
import Cubical.Categories.Direct.StrictDownset as SD

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Top Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.LinearFunction Alphabet
open import Grammar.Function Alphabet
open import Grammar.Function.AsPrimitive.Exponential Alphabet
  using (isSetGrammar⇒)
open import Grammar.Product.Binary.AsPrimitive Alphabet
open import Term.Base Alphabet

private
  variable
    ℓ ℓA ℓB : Level
    A : Grammar ℓA
    B : Grammar ℓB

-- The order packaged as a c-c-l well-founded order on String.
OrdWFOrder : WFOrder ℓ-zero ℓ-zero
OrdWFOrder = record
  { D       = String
  ; isSetD  = isSetString
  ; _<_     = _≺_
  ; isProp< = isProp≺
  ; trans<  = trans≺
  ; wf<     = wf≺
  }

-- The later modality of the order: A at every strictly-smaller string.
▷ : Grammar ℓA → Grammar ℓA
▷ A x = ∀ (y : String) → y ≺ x → A y

-- The general elimination combinator: from a strictness witness, project.
▷-elim-at : ∀ {x y} → y ≺ x → ▷ A x → A y
▷-elim-at p α = α _ p

private
  dir : DirectStr {C = PosetCat OrdWFOrder} OrdWFOrder
  dir = PosetDirect OrdWFOrder

  module _ {ℓA} {A : Grammar ℓA} (isSetA : isSetGrammar A) (f : ▷ A ⊢ A) where
    Afam : String → hSet ℓA
    Afam v = A v , isSetA v

    -- collapse the presheaf-level ▷Fam to the first-order ▷, then apply f
    φ : ∀ x → SD.▷Fam dir Afam x .fst → A x
    φ x β = f x (λ y y<x → SD.▷FamApp dir Afam β (inl y<x) y<x)

    lobFam : ∀ w → A w
    lobFam = SD.löbFam dir Afam φ

-- Löb induction: the guarded fixed point, internally.
lob : isSetGrammar A → (▷ A ⊢ A) → ⊤ ⊢ A
lob isSetA f w _ = lobFam isSetA f w

------------------------------------------------------------------------------
-- Accessors: computation rule and uniqueness of the guarded fixed point,
-- inherited from upstream löbFam-unfold / löbFam-uniq-unfold.

opaque
  unfolding ⊤

  -- A closed term is available later.  (An unrestricted next : A ⊢ ▷ A does
  -- not exist for grammars; a global element ⊤ ⊢ A always moves under ▷.)
  next⊤ : ⊤ ⊢ A → ⊤ ⊢ ▷ A
  next⊤ g _ _ y _ = g y tt

  -- The guarded fixed-point equation.
  lob-unfold : (isSetA : isSetGrammar A) (f : ▷ A ⊢ A)
    → lob isSetA f ≡ f ∘g next⊤ (lob isSetA f)
  lob-unfold isSetA f = funExt λ w → funExt λ _ →
    SD.löbFam-unfold dir (Afam isSetA f) (φ isSetA f) w

  -- ... and it is the unique such fixed point.
  lob-unique : (isSetA : isSetGrammar A) (f : ▷ A ⊢ A) (g : ⊤ ⊢ A)
    → g ≡ f ∘g next⊤ g
    → g ≡ lob isSetA f
  lob-unique {A = A} isSetA f g g-fix = funExt λ w → funExt λ _ →
    funExt⁻ (SD.löbFam-uniq-unfold dir (Afam isSetA f) (φ isSetA f) t teq) w
    where
      t : ∀ w → A w
      t w = g w tt
      teq : ∀ w → t w ≡ φ isSetA f w (SD.nextFam dir (Afam isSetA f) t w)
      teq w = funExt⁻ (funExt⁻ g-fix w) tt

------------------------------------------------------------------------------
-- The hylomorphism interface: open recursion at the three function types.
--
-- Each premise is a "body": consume part of the input, use the recursive map
-- *later* on the strict remainder.  Each combinator is closed Löb at the
-- corresponding exponential, collapsed back through the adjunction.

-- Linear, function-on-the-right: the recursive-descent shape for a
-- front-consuming ▷ (the later parser is applied to the strict suffix).
hylo⟜ : isSetGrammar B → (A ⊗ ▷ (B ⟜ A) ⊢ B) → A ⊢ B
hylo⟜ {B = B} {A = A} isSetB f =
  ⟜-app
  ∘g id ,⊗ (lob (isSetGrammar⟜ isSetB) (⟜-intro f) ∘g ⊤-intro)
  ∘g ⊗-unit-r⁻

-- Linear, function-on-the-left: the shape matching a prefix ▷.
hylo⊸ : isSetGrammar B → (▷ (A ⊸ B) ⊗ A ⊢ B) → A ⊢ B
hylo⊸ {B = B} {A = A} isSetB f =
  ⊸-app
  ∘g (lob (isSetGrammar⊸ isSetB) (⊸-intro f) ∘g ⊤-intro) ,⊗ id
  ∘g ⊗-unit-l⁻

-- Cartesian: upstream's HyloPsh body `▷(X ⇒ B) × X ⊢ B`, internally.
hylo& : {A B : Grammar ℓ} → isSetGrammar B → (▷ (A ⇒ B) & A ⊢ B) → A ⊢ B
hylo& isSetB f =
  ⇒-app ∘g &-intro (lob (isSetGrammar⇒ isSetB) (⇒-intro f) ∘g ⊤-intro) id
