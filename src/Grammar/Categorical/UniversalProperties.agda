{-# OPTIONS --lossy-unification #-}
{-
  Phase A: package gsa's finite (co)limits as upstream universal-property
  witnesses over the additive category |GRAMMAR| ℓ from Term.Category.

  We provide:
    1. Terminal'    from ⊤*
    2. Initial'     from ⊥*
    3. BinProducts  from _&_
    4. BinCoProducts from _⊕_   (= BinProducts in the opposite category)
    5. AllExponentiable from _⇒_

  Everything is layered on top of the existing connectives; nothing is
  redefined.  We prefer .fst / .snd over ⟨_⟩ to avoid the ambiguity
  between Foundations.Structure and Grammar.HLevels.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

module Grammar.Categorical.UniversalProperties (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Unit
open import Cubical.Data.Empty as Empty hiding (⊥ ; ⊥*)
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Opposite
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf.Constructions.Exponential
open import Cubical.Categories.Exponentials.Small

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Top.Base Alphabet
open import Grammar.Bottom.Base Alphabet
open import Grammar.Bottom.Properties Alphabet
open import Grammar.Product.Binary.AsPrimitive.Base Alphabet
open import Grammar.Product.Binary.AsPrimitive.Properties Alphabet
open import Grammar.Sum.Binary.AsPrimitive.Base Alphabet
open import Grammar.Sum.Binary.AsPrimitive.Properties Alphabet
open import Grammar.Function.AsPrimitive.Base Alphabet
open import Term.Base Alphabet
open import Term.Category Alphabet

private
  variable
    ℓ : Level

open Category
open UniversalElement

------------------------------------------------------------------------
-- hLevel lemmas not already present in the connective modules
------------------------------------------------------------------------

opaque
  unfolding ⊤*
  isSetGrammar⊤* : ∀ {ℓ} → isSetGrammar (⊤* {ℓ})
  isSetGrammar⊤* w = isProp→isSet (λ _ _ → refl)

opaque
  unfolding ⊥*
  isSetGrammar⊥* : ∀ {ℓ} → isSetGrammar (⊥* {ℓ})
  isSetGrammar⊥* w = isProp→isSet (λ x → Empty.rec (lower x))

opaque
  unfolding _⇒_
  isSetGrammar⇒ : {A : Grammar ℓ} {B : Grammar ℓ}
    → isSetGrammar B → isSetGrammar (A ⇒ B)
  isSetGrammar⇒ isSetB w = isSet→ (isSetB w)

------------------------------------------------------------------------
-- 1. Terminal'  (⊤*)
------------------------------------------------------------------------

⊤SetGrammar : SetGrammar ℓ
⊤SetGrammar = ⊤* , isSetGrammar⊤*

|GRAMMAR|-Terminal : Terminal (|GRAMMAR| ℓ)
|GRAMMAR|-Terminal .fst = ⊤SetGrammar
|GRAMMAR|-Terminal .snd y .fst = is-terminal-⊤* .fst
|GRAMMAR|-Terminal .snd y .snd f = is-terminal-⊤* .snd f

|GRAMMAR|-Terminal' : Terminal' (|GRAMMAR| ℓ)
|GRAMMAR|-Terminal' = terminalToUniversalElement |GRAMMAR|-Terminal

------------------------------------------------------------------------
-- 2. Initial'  (⊥*)
--    Initial' C = Terminal' (C ^op).  In the opposite category the
--    terminal object is ⊥*, with the unique arrow given by ⊥*-elim.
------------------------------------------------------------------------

⊥SetGrammar : SetGrammar ℓ
⊥SetGrammar = ⊥* , isSetGrammar⊥*

|GRAMMAR|-Terminal^op : Terminal ((|GRAMMAR| ℓ) ^op)
|GRAMMAR|-Terminal^op .fst = ⊥SetGrammar
-- Hom in C^op from y to ⊥* is Term ⟨⊥*⟩ ⟨y⟩, i.e. a map out of ⊥*.
|GRAMMAR|-Terminal^op .snd y .fst = is-initial-⊥* .fst
|GRAMMAR|-Terminal^op .snd y .snd f = is-initial-⊥* .snd f

|GRAMMAR|-Initial' : Initial' (|GRAMMAR| ℓ)
|GRAMMAR|-Initial' = terminalToUniversalElement |GRAMMAR|-Terminal^op

------------------------------------------------------------------------
-- 3. BinProducts  (_&_)
--    BinProducts C = ∀ cc' → UniversalElement C (BinProductProf ⟅ cc' ⟆).
--    BinProductProf ⟅ (A , B) ⟆ is the presheaf  Γ ↦ C[Γ,A] × C[Γ,B];
--    its action element ∘ᴾ⟨P⟩ f = (f ⋆ π₁ , f ⋆ π₂).  The universal
--    element has vertex A & B, element (π₁ , π₂), and the inverse to
--    "compose with the element" is _,&_, with β/η from the & laws.
------------------------------------------------------------------------

&SetGrammar : SetGrammar ℓ → SetGrammar ℓ → SetGrammar ℓ
&SetGrammar A B =
  (A .fst & B .fst) , isSetGrammar& (A .snd) (B .snd)

module _ (A B : SetGrammar ℓ) where
  private
    P = BinProductProf (|GRAMMAR| ℓ) ⟅ (A , B) ⟆

  &-UniversalElement : UniversalElement (|GRAMMAR| ℓ) P
  &-UniversalElement .vertex = &SetGrammar A B
  &-UniversalElement .element = π₁ , π₂
  &-UniversalElement .universal Γ =
    isoToIsEquiv (iso
      (λ f → (π₁ ∘g f) , (π₂ ∘g f))
      (λ fg → fg .fst ,& fg .snd)
      (λ fg → ΣPathP (&-β₁ (fg .fst) (fg .snd) , &-β₂ (fg .fst) (fg .snd)))
      (λ f → &-η f))

|GRAMMAR|-BinProducts : BinProducts (|GRAMMAR| ℓ)
|GRAMMAR|-BinProducts (A , B) = &-UniversalElement A B

------------------------------------------------------------------------
-- 4. BinCoProducts  (_⊕_)
--    BinCoProducts C = BinProducts (C ^op).  The coproduct A ⊕ B is the
--    product in the opposite category: vertex A ⊕ B, "projections"
--    inl/inr (which in C^op are arrows into the vertex), pairing ⊕-elim.
------------------------------------------------------------------------

⊕SetGrammar : SetGrammar ℓ → SetGrammar ℓ → SetGrammar ℓ
⊕SetGrammar A B =
  (A .fst ⊕ B .fst) , isSetGrammar⊕ (A .snd) (B .snd)

module _ (A B : SetGrammar ℓ) where
  private
    Cop = (|GRAMMAR| ℓ) ^op
    P = BinProductProf Cop ⟅ (A , B) ⟆

  ⊕-UniversalElement : UniversalElement Cop P
  ⊕-UniversalElement .vertex = ⊕SetGrammar A B
  ⊕-UniversalElement .element = inl , inr
  ⊕-UniversalElement .universal Γ =
    isoToIsEquiv (iso
      -- a Cop-arrow Γ ⟶ A⊕B is a term A⊕B ⊢ Γ
      (λ f → (f ∘g inl) , (f ∘g inr))
      (λ fg → ⊕-elim (fg .fst) (fg .snd))
      (λ fg → ΣPathP (⊕-βl (fg .fst) (fg .snd) , ⊕-βr (fg .fst) (fg .snd)))
      (λ f → ⊕-η f))

|GRAMMAR|-BinCoProducts : BinCoProducts (|GRAMMAR| ℓ)
|GRAMMAR|-BinCoProducts (A , B) = ⊕-UniversalElement A B

------------------------------------------------------------------------
-- 5. Exponentials  (_⇒_)
--    AllExponentiable C bp = ∀ c → ∀ d →
--      UniversalElement C (((C [-, c ]) , bp(- , c)) ⇒PshSmall (C [-, d ])).
--    The exponential c⇒d has vertex c ⇒ d, evaluation element ⇒-app, and
--    the universal property is currying ⇒-intro with β/η from ⇒ laws.
------------------------------------------------------------------------

module _ (c d : SetGrammar ℓ) where
  private
    bp = |GRAMMAR|-BinProducts {ℓ}
    -×c : BinProductsWith (|GRAMMAR| ℓ) c
    -×c = λ d' → bp (d' , c)
    P = (((|GRAMMAR| ℓ) [-, c ]) , -×c) ⇒PshSmall ((|GRAMMAR| ℓ) [-, d ])

  ⇒-Exponential : Exponential (|GRAMMAR| ℓ) c d -×c
  ⇒-Exponential .vertex = (c .fst ⇒ d .fst) , isSetGrammar⇒ (d .snd)
  ⇒-Exponential .element = ⇒-app
  -- HOLE: isUniversal (c⇒d) ⇒-app, i.e.
  --   ∀ Γ → isEquiv (λ (f : Γ ⊢ c⇒d) → ⇒-app ∘ᴾ⟨P⟩ f)
  -- where ⇒-app ∘ᴾ⟨P⟩ f reduces to ⇒-app ∘g (G .F-hom f) : Γ & c ⊢ d
  -- and G = LRPsh→Functor ((C[-,c]) , -×c) is the (- & c) functor.
  -- The inverse of currying is ⇒-intro, with β/η from ⇒-β/⇒-η, but the
  -- proof must unfold G .F-hom = (-×c Γ).intro (… ⋆ʳᶜ f), i.e. reason via
  -- BinProductsWithNotation's ×β₁/×β₂.  Left as the documented hole.
  ⇒-Exponential .universal Γ = {!!}

|GRAMMAR|-AllExponentiable :
  AllExponentiable (|GRAMMAR| ℓ) (|GRAMMAR|-BinProducts {ℓ})
|GRAMMAR|-AllExponentiable c d = ⇒-Exponential c d
