{-
  EQUALITY OF TYPES, decided inside the calculus.

  `TyEq A B` is `⌈ B ⌉ A`, the representable at sort `ty`.  Its
  substitution principle is `⌈⌉-E` -- the Yoneda lemma -- so transport
  along a type equality is a rule of the calculus, not a `subst`; and
  its decidability is `dec-⊗` at `baseOp` and `arrOp`, via the generic
  iso `⌈ op o m⃗ ⌉ ≅ ⊗ˢ o (λ a → ⌈ m⃗ a ⌉)`.

  So `Discrete Ty` is never assumed: the third sort pays for itself by
  supplying its own decision procedure through the same tensor rule the
  term sort uses.  (`Discrete Name` still is assumed -- names have no
  operations, so there is no tensor to decide.)
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.SimplyTyped.Types where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty as E using ()
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Decidable
open import TheoryGrammar.Instances.SimplyTyped.Signature
open import TheoryGrammar.Instances.SimplyTyped.Substrate
open import TheoryGrammar.Instances.SimplyTyped.Base
open import TheoryGrammar.Instances.SimplyTyped.Readable

module StTypes (Name : Type₀) where

  open StBase Name
  open StReadable Name

  -- ================================================================
  -- Substitution along a type equality IS the Yoneda elimination rule.
  -- ================================================================

  tyCast : {s : TSort} (P : Ty → TheoryTy ℓ-zero s) (A B : Ty)
         → TyEq A B → P A ⊢ P B
  tyCast P A B = ⌈⌉-E {B = λ X → P X ⊢ P B} idg A

  tyEq-refl : (A : Ty) → TyEq A A
  tyEq-refl A = Eq.refl

  tyEq-sym : (A B : Ty) → TyEq A B → TyEq B A
  tyEq-sym A B e = tyCast (λ X → Kty {s = ty} X A) A B e A (tyEq-refl A)

  tyEq-trans : (A B C : Ty) → TyEq A B → TyEq B C → TyEq A C
  tyEq-trans A B C e f = tyCast (λ X → Kty {s = ty} A X) B C f A e

  -- ================================================================
  -- The tuples that present `base` and `_⇒ᵗ_` as operations.
  -- ================================================================

  mBase : (a : TAr baseOp) → Carrier (TSortOf baseOp a)
  mBase ()

  mArr : Ty → Ty → (a : TAr arrOp) → Carrier (TSortOf arrOp a)
  mArr A B b = if b then A else B

  ⌈⌉ᵗ : (o : TOp) (m⃗ : (a : TAr o) → Carrier (TSortOf o a))
      → (a : TAr o) → TheoryTy ℓ-zero (TSortOf o a)
  ⌈⌉ᵗ o m⃗ a = ⌈ m⃗ a ⌉

  -- ================================================================
  -- Decidability of `⌈ A ⌉`, by the generic tensor rule.  The only
  -- recursion is on the description of the type being matched against;
  -- the type being tested is never pattern-matched.
  -- ================================================================

  dec-⌈⌉ᵗ : (A : Ty) → ⊤G ⊢ Dec⟨ ⌈_⌉ {s = ty} A ⟩
  dec-⌈⌉ᵗ base C _ =
    dec-map (⊗ˢ baseOp (⌈⌉ᵗ baseOp mBase)) (⌈_⌉ {s = ty} base)
            (⌈⌉-from baseOp mBase) (⌈⌉-into baseOp mBase) C
            (dec-⊗ baseOp (⌈⌉ᵗ baseOp mBase) C (λ _ ()))
  dec-⌈⌉ᵗ (A ⇒ᵗ B) C _ =
    dec-map (⊗ˢ arrOp (⌈⌉ᵗ arrOp (mArr A B))) (⌈_⌉ {s = ty} (A ⇒ᵗ B))
            (⌈⌉-from arrOp (mArr A B)) (⌈⌉-into arrOp (mArr A B)) C
            (dec-⊗ arrOp (⌈⌉ᵗ arrOp (mArr A B)) C λ sp →
               λ { true  → dec-⌈⌉ᵗ A (TParts arrOp C sp true)  tt
                 ; false → dec-⌈⌉ᵗ B (TParts arrOp C sp false) tt })

  -- ================================================================
  -- Injectivity of the arrow, from `op-inj` -- i.e. from unique
  -- readability plus `unsplit`, with no lemma of its own.
  -- ================================================================

  -- and disjointness of the two type constructors, from the SAME iso:
  -- `base` cannot split as an arrow because `IsBase` is not `IsArr`
  base≢arr : (A B : Ty) → TyEq base (A ⇒ᵗ B) → E.⊥
  base≢arr A B e with ⌈⌉-into baseOp mBase (A ⇒ᵗ B) (tyEq-sym base (A ⇒ᵗ B) e)
  ... | () , _

  ⇒ᵗ-inj : (A B A' B' : Ty) → TyEq (A ⇒ᵗ B) (A' ⇒ᵗ B') → (A ≡ A') × (B ≡ B')
  ⇒ᵗ-inj A B A' B' e =
      funExt⁻ (op-inj Split-isProp arrOp (mArr A B) (mArr A' B') e) true
    , funExt⁻ (op-inj Split-isProp arrOp (mArr A B) (mArr A' B') e) false
