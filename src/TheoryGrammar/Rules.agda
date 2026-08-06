{-
  The embedded DSL: intro and elim for every connective, with the β/η
  equations stated as isomorphisms of hom-sets.

  Two presentations of each connective, deliberately:

    * COMBINATORS (`&-I`, `⊕-E`, `⊸-app`, ...) -- what you actually write
      programs with, same names and shapes as LambekD.

    * UNIVERSAL PROPERTIES (`&-UP`, `⊕-UP`, ...) -- an `Iso` of hom-sets.
      This is the β/η package: `sec`/`ret` of the Iso ARE the two
      equations, so there are no separate β and η lemmas to state and no
      bespoke universal-property records.

  Almost every UP below holds with `sec` and `ret` equal to `refl` or to
  a pattern-matching funExt with `refl` inside -- i.e. the connectives
  compute.  The exceptions are flagged in place.

  The representable case

      ⌈ a ⌉ ⊢ B   ≅   B a

  is the Yoneda lemma for this substrate, and is what `ε` and `literal`
  were special cases of in the string setting.
-}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Rules where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥*) renaming (rec to ⊥*rec)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Multiplicative

private variable ℓS ℓ ℓ' ℓX ℓA ℓB ℓC ℓY : Level

module Rules {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (M : Model σ ℓX) where

  open Notation M

  private variable
    s : S
    A : TheoryTy ℓA s
    B : TheoryTy ℓB s
    C : TheoryTy ℓC s

  -- ================================================================
  -- ⊤  --  intro only
  -- ================================================================

  ⊤-I : A ⊢ ⊤G
  ⊤-I _ _ = tt

  ⊤-UP : Iso (A ⊢ ⊤G {s}) Unit
  ⊤-UP .Iso.fun _ = tt
  ⊤-UP .Iso.inv _ = ⊤-I
  ⊤-UP .Iso.sec _ = refl
  ⊤-UP .Iso.ret _ = refl

  -- ================================================================
  -- ⊥  --  elim only
  -- ================================================================

  ⊥-E : ⊥G ⊢ A
  ⊥-E _ ()

  ⊥-UP : Iso (⊥G {s} ⊢ A) Unit
  ⊥-UP .Iso.fun _ = tt
  ⊥-UP .Iso.inv _ = ⊥-E
  ⊥-UP .Iso.sec _ = refl
  ⊥-UP .Iso.ret f = funExt λ m → funExt λ ()

  -- ================================================================
  -- &  --  binary additive conjunction
  -- ================================================================

  &-I : A ⊢ B → A ⊢ C → A ⊢ (B & C)
  &-I f g m x = f m x , g m x

  &-E₁ : (A & B) ⊢ A
  &-E₁ _ = fst

  &-E₂ : (A & B) ⊢ B
  &-E₂ _ = snd

  &-UP : Iso (A ⊢ (B & C)) ((A ⊢ B) × (A ⊢ C))
  &-UP .Iso.fun f = (λ m x → f m x .fst) , (λ m x → f m x .snd)
  &-UP .Iso.inv (f , g) = &-I f g
  &-UP .Iso.sec _ = refl
  &-UP .Iso.ret _ = refl

  -- ================================================================
  -- ⊕  --  binary additive disjunction
  -- ================================================================

  ⊕-I₁ : A ⊢ (A ⊕ B)
  ⊕-I₁ _ = inl

  ⊕-I₂ : B ⊢ (A ⊕ B)
  ⊕-I₂ _ = inr

  ⊕-E : A ⊢ C → B ⊢ C → (A ⊕ B) ⊢ C
  ⊕-E f g m (inl x) = f m x
  ⊕-E f g m (inr y) = g m y

  ⊕-UP : Iso ((A ⊕ B) ⊢ C) ((A ⊢ C) × (B ⊢ C))
  ⊕-UP .Iso.fun f = (λ m x → f m (inl x)) , (λ m y → f m (inr y))
  ⊕-UP .Iso.inv (f , g) = ⊕-E f g
  ⊕-UP .Iso.sec _ = refl
  ⊕-UP .Iso.ret f = funExt λ m → funExt λ { (inl _) → refl ; (inr _) → refl }

  -- ================================================================
  -- ⇒  --  the ADDITIVE function type, right adjoint to &
  -- ================================================================

  ⇒-I : (A & B) ⊢ C → A ⊢ (B ⇒ C)
  ⇒-I f m x y = f m (x , y)

  ⇒-E : A ⊢ (B ⇒ C) → A ⊢ B → A ⊢ C
  ⇒-E f g m x = f m x (g m x)

  ⇒-app : ((A ⇒ B) & A) ⊢ B
  ⇒-app m (f , x) = f x

  ⇒-UP : Iso ((A & B) ⊢ C) (A ⊢ (B ⇒ C))
  ⇒-UP .Iso.fun = ⇒-I
  ⇒-UP .Iso.inv f m (x , y) = f m x y
  ⇒-UP .Iso.sec _ = refl
  ⇒-UP .Iso.ret _ = refl

  -- ================================================================
  -- ⊕ᴰ / &ᴰ  --  the indexed additives
  -- ================================================================

  ⊕ᴰ-I : (Y : Type ℓY) {A : Y → TheoryTy ℓA s} (y : Y) → A y ⊢ ⊕ᴰ Y A
  ⊕ᴰ-I Y y m x = y , x

  ⊕ᴰ-E : {Y : Type ℓY} {A : Y → TheoryTy ℓA s} {B : TheoryTy ℓB s}
       → (∀ y → A y ⊢ B) → ⊕ᴰ Y A ⊢ B
  ⊕ᴰ-E f m (y , x) = f y m x

  ⊕ᴰ-UP : {Y : Type ℓY} {A : Y → TheoryTy ℓA s} {B : TheoryTy ℓB s}
        → Iso (⊕ᴰ Y A ⊢ B) (∀ y → A y ⊢ B)
  ⊕ᴰ-UP .Iso.fun f y m x = f m (y , x)
  ⊕ᴰ-UP .Iso.inv = ⊕ᴰ-E
  ⊕ᴰ-UP .Iso.sec _ = refl
  ⊕ᴰ-UP .Iso.ret _ = refl

  &ᴰ-I : {Y : Type ℓY} {A : TheoryTy ℓA s} {B : Y → TheoryTy ℓB s}
       → (∀ y → A ⊢ B y) → A ⊢ &ᴰ Y B
  &ᴰ-I f m x y = f y m x

  &ᴰ-E : (Y : Type ℓY) {B : Y → TheoryTy ℓB s} (y : Y) → &ᴰ Y B ⊢ B y
  &ᴰ-E Y y m f = f y

  &ᴰ-UP : {Y : Type ℓY} {A : TheoryTy ℓA s} {B : Y → TheoryTy ℓB s}
        → Iso (A ⊢ &ᴰ Y B) (∀ y → A ⊢ B y)
  &ᴰ-UP .Iso.fun f y m x = f m x y
  &ᴰ-UP .Iso.inv = &ᴰ-I
  &ᴰ-UP .Iso.sec _ = refl
  &ᴰ-UP .Iso.ret _ = refl

  -- ================================================================
  -- ⌈ a ⌉  --  representables.  THE YONEDA LEMMA for this substrate,
  -- and the generic replacement for `ε` and `literal`.
  -- ================================================================

  ⌈⌉-I : (a : M .carrier s) → ⌈ a ⌉ ⊢ ⌈ a ⌉
  ⌈⌉-I a = id⊢

  ⌈⌉-pt : (a : M .carrier s) → ⌈ a ⌉ a
  ⌈⌉-pt a = Eq.refl

  -- elim: a map out of a representable is determined by one element
  ⌈⌉-E : {a : M .carrier s} {B : TheoryTy ℓB s} → B a → ⌈ a ⌉ ⊢ B
  ⌈⌉-E b .(_) Eq.refl = b

  ⌈⌉-UP : {a : M .carrier s} {B : TheoryTy ℓB s} → Iso (⌈ a ⌉ ⊢ B) (B a)
  ⌈⌉-UP {a = a} .Iso.fun f = f a Eq.refl
  ⌈⌉-UP .Iso.inv = ⌈⌉-E
  ⌈⌉-UP .Iso.sec _ = refl
  ⌈⌉-UP .Iso.ret f = funExt λ m → funExt λ { Eq.refl → refl }

  -- ================================================================
  -- ⊗[ o ]  --  the multiplicatives.  Intro is n-ary: supply an element
  -- for every slot.  Elim is the currying iso of TheoryGrammar.
  -- Multiplicative, repackaged as a rule.
  -- ================================================================

  module _ (o : σ .ops) {A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a)} where

    ⊗-I : (m⃗ : (a : σ .arities o) → M .carrier (σ .sortOf o a))
        → ((a : σ .arities o) → A a (m⃗ a))
        → ⊗[ o ] A (M .op o m⃗)
    ⊗-I m⃗ h = m⃗ , Eq.refl , h

    ⊗-E : {B : TheoryTy ℓB (σ .resultSort o)}
        → MultiHom M o A B → ⊗[ o ] A ⊢ B
    ⊗-E = uncurry⊗ M o

    ⊗-UP : {B : TheoryTy ℓB (σ .resultSort o)}
         → Iso (⊗[ o ] A ⊢ B) (MultiHom M o A B)
    ⊗-UP = ⊗-currying M o
