{- EQUALITY OF TYPES, decided inside the calculus. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.LinTyped.Types where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Empty as E using ()
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Decidable
open import TheoryGrammar.Instances.LinTyped.Signature
open import TheoryGrammar.Instances.LinTyped.Fibered
open import TheoryGrammar.Instances.LinTyped.Base
open import TheoryGrammar.Instances.LinTyped.Readable

-- Substitution along a type equality IS the Yoneda elimination rule.

-- `tyCast P A B e` denotes transport of a derivation along the type
-- equality `e`, as a MAP of the calculus: `⌈⌉-E`, the Yoneda lemma.
tyCast : {s : TSort} (P : Ty → TheoryTy ℓ-zero s) (A B : Ty)
       → TyEq A B → P A ⊢ P B
tyCast P A B = ⌈⌉-E {B = λ X → P X ⊢ P B} idg A

tyEq-refl : (A : Ty) → TyEq A A
tyEq-refl A = Eq.refl

tyEq-sym : (A B : Ty) → TyEq A B → TyEq B A
tyEq-sym A B e = tyCast (λ X → Kty {s = ty} X A) A B e A (tyEq-refl A)

tyEq-trans : (A B C : Ty) → TyEq A B → TyEq B C → TyEq A C
tyEq-trans A B C e f = tyCast (λ X → Kty {s = ty} A X) B C f A e

-- The tuples that present `base` and `_⊸ᵗ_` as operations.

mBase : (a : TAr baseOp) → Carrier (TSortOf baseOp a)
mBase ()

mLol : Ty → Ty → (a : TAr lolOp) → Carrier (TSortOf lolOp a)
mLol A B b = if b then A else B

-- `⌈⌉ᵗ o m⃗` denotes the slot family "each slot IS the corresponding
-- component of `m⃗`" -- the right-hand side of the representable iso.
⌈⌉ᵗ : (o : TOp) (m⃗ : (a : TAr o) → Carrier (TSortOf o a))
    → (a : TAr o) → TheoryTy ℓ-zero (TSortOf o a)
⌈⌉ᵗ o m⃗ a = ⌈ m⃗ a ⌉

-- Decidability of `⌈ A ⌉`, by the generic tensor rule.  The only
-- recursion is on the description of the type being matched against;
-- the type being tested is never pattern-matched.

dec-⌈⌉ᵗ : (A : Ty) → ⊤G ⊢ Dec⟨ ⌈_⌉ {s = ty} A ⟩
dec-⌈⌉ᵗ base C _ =
  dec-map (⊗ˢ baseOp (⌈⌉ᵗ baseOp mBase)) (⌈_⌉ {s = ty} base)
          (⌈⌉-from baseOp mBase) (⌈⌉-into baseOp mBase) C
          (dec-⊗ baseOp (⌈⌉ᵗ baseOp mBase) C (λ _ ()))
dec-⌈⌉ᵗ (A ⊸ᵗ B) C _ =
  dec-map (⊗ˢ lolOp (⌈⌉ᵗ lolOp (mLol A B))) (⌈_⌉ {s = ty} (A ⊸ᵗ B))
          (⌈⌉-from lolOp (mLol A B)) (⌈⌉-into lolOp (mLol A B)) C
          (dec-⊗ lolOp (⌈⌉ᵗ lolOp (mLol A B)) C λ sp →
             λ { true  → dec-⌈⌉ᵗ A (TParts lolOp C sp true)  tt
               ; false → dec-⌈⌉ᵗ B (TParts lolOp C sp false) tt })

-- WHAT THE ISO BUYS ABOUT `Ty`, with no lemma of its own.

base≢lol : (A B : Ty) → TyEq base (A ⊸ᵗ B) → E.⊥
base≢lol A B e =
  E.rec* (baseLol-⊥ {A = ⌈⌉ᵗ lolOp (mLol A B)} base
           ((mkBase , λ ()) , ⌈⌉-into lolOp (mLol A B) base e))

⊸-slots : (A B A' B' : Ty)
        → TyEq (A ⊸ᵗ B) (A' ⊸ᵗ B') → mLol A B ≡ mLol A' B'
⊸-slots A B A' B' = op-inj Split-isProp lolOp (mLol A B) (mLol A' B')

⊸-injˡ : (A B A' B' : Ty) → TyEq (A ⊸ᵗ B) (A' ⊸ᵗ B') → A ≡ A'
⊸-injˡ A B A' B' e = funExt⁻ (⊸-slots A B A' B' e) true

⊸-injʳ : (A B A' B' : Ty) → TyEq (A ⊸ᵗ B) (A' ⊸ᵗ B') → B ≡ B'
⊸-injʳ A B A' B' e = funExt⁻ (⊸-slots A B A' B' e) false

⊸-inj : (A B A' B' : Ty) → TyEq (A ⊸ᵗ B) (A' ⊸ᵗ B') → (A ≡ A') × (B ≡ B')
⊸-inj A B A' B' e = ⊸-injˡ A B A' B' e , ⊸-injʳ A B A' B' e
