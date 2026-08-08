{- THE DERIVATIVE IS PRECOMPOSITION. Brzozowski's `δ_c A w = A (c ∷ w)` is
   not a construction on grammars at all -- it is restriction along a map
   of carriers. -}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Derivative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.BaseChange
open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.CanonicalFocus

private variable ℓS ℓ ℓ' ℓX ℓP ℓA ℓB ℓC ℓY : Level

-- The derivative, along an arbitrary map of carriers.
module Deriv {S : Type ℓS} (X : S → Type ℓX) {s t : S} (act : X s → X t)
  where

  open CarrierNotation X

  δ : TheoryTy ℓA t → TheoryTy ℓA s
  δ B x = B (act x)

  -- functorial, with both laws refl -- `δ` does not touch the payload
  δ-map : {B : TheoryTy ℓA t} {C : TheoryTy ℓB t} → B ⊢ C → δ B ⊢ δ C
  δ-map f x = f (act x)

  δ-map-id : {B : TheoryTy ℓA t} → δ-map (id⊢ {A = B}) ≡ id⊢
  δ-map-id = refl

  δ-map-∘ : {B : TheoryTy ℓA t} {C : TheoryTy ℓB t} {D : TheoryTy ℓC t}
            (g : C ⊢ D) (f : B ⊢ C)
          → δ-map (g ∘⊢ f) ≡ (δ-map g ∘⊢ δ-map f)
  δ-map-∘ g f = refl

  -- THE ADJOINT TRIPLE. Σ_act ⊣ δ ⊣ Π_act `δ` is precomposition, and
  -- precomposition between families of types always has BOTH adjoints -- Σ
  -- and Π over the FIBRES of the action.

  Σact : TheoryTy ℓA s → TheoryTy (ℓ-max ℓX ℓA) t
  Σact A y = Σ[ x ∈ X s ] ((act x Eq.≡ y) × A x)

  Πact : TheoryTy ℓA s → TheoryTy (ℓ-max ℓX ℓA) t
  Πact A y = (x : X s) → act x Eq.≡ y → A x

  -- the fibre: the ways `y` can be peeled by this action
  Fibre : X t → Type ℓX
  Fibre y = Σ[ x ∈ X s ] (act x Eq.≡ y)

  -- Σact ⊣ δ
  Σ⊣δ : {A : TheoryTy ℓA s} {B : TheoryTy ℓB t} → Iso (Σact A ⊢ B) (A ⊢ δ B)
  Σ⊣δ .Iso.fun f x a = f (act x) (x , Eq.refl , a)
  Σ⊣δ .Iso.inv g _ (x , Eq.refl , a) = g x a
  Σ⊣δ .Iso.sec _ = refl
  Σ⊣δ .Iso.ret f = funExt λ _ → funExt λ { (x , Eq.refl , a) → refl }

  -- δ ⊣ Πact -- the amazing right adjoint
  δ⊣Π : {A : TheoryTy ℓA s} {B : TheoryTy ℓB t} → Iso (δ B ⊢ A) (B ⊢ Πact A)
  δ⊣Π .Iso.fun f _ b x Eq.refl = f x b
  δ⊣Π .Iso.inv g x b = g (act x) b x Eq.refl
  δ⊣Π .Iso.sec g = funExt λ _ → funExt λ _ → funExt λ _ → funExt λ { Eq.refl → refl }
  δ⊣Π .Iso.ret _ = refl

  -- ... and the gap between the two adjoints is exactly the ambiguity of
  -- the peeling.
  Σ→Π : {A : TheoryTy ℓA s} (y : X t)
      → isProp (Fibre y) → Σact A y → Πact A y
  Σ→Π {A = A} y pr (x , e , a) x' e' =
    subst (λ f → A (f .fst)) (pr (x , e) (x' , e')) a

  Π→Σ : {A : TheoryTy ℓA s} (y : X t)
      → Fibre y → Πact A y → Σact A y
  Π→Σ y (x , e) h = x , e , h x e

  -- WHAT THE TRIPLE BUYS. (1) `δ` has a left adjoint so it preserves
  -- limits (⊤, &, &ᴰ, ⇒) and a right adjoint so it preserves colimits (⊥,
  -- ⊕, ⊕ᴰ) -- exactly the seven `refl` laws in `δ-laws`.

  -- THE MODALITIES, DERIVED. The triple generates four composites; the two
  -- on WORLDS are the modalities: ◇ = Σact ∘ δ the COMONAD of `Σact ⊣ δ`
  -- -- ◇ B y ≅ Fibre y × B y □ = Πact ∘ δ the MONAD of `δ ⊣ Πact` -- □ B y
  -- ≅ Fibre y → B y i.e. conjunction-with and implication-from the FIBRE,
  -- the open/closed...

  ◇ : TheoryTy ℓA t → TheoryTy (ℓ-max ℓX ℓA) t
  ◇ B = Σact (δ B)

  □ : TheoryTy ℓA t → TheoryTy (ℓ-max ℓX ℓA) t
  □ B = Πact (δ B)

  -- counit and comultiplication of ◇
  ◇-ε : {B : TheoryTy ℓA t} → ◇ B ⊢ B
  ◇-ε _ (x , Eq.refl , b) = b

  ◇-δ : {B : TheoryTy ℓA t} → ◇ B ⊢ ◇ (◇ B)
  ◇-δ _ (x , Eq.refl , b) = x , Eq.refl , (x , Eq.refl , b)

  -- unit and multiplication of □
  □-η : {B : TheoryTy ℓA t} → B ⊢ □ B
  □-η _ b x Eq.refl = b

  □-μ : {B : TheoryTy ℓA t} → □ (□ B) ⊢ □ B
  □-μ _ h x Eq.refl = h x Eq.refl x Eq.refl

  -- ... and both are the fibre, conjoined and implied
  ◇-fibre : {B : TheoryTy ℓA t} (y : X t) → Iso (◇ B y) (Fibre y × B y)
  ◇-fibre y .Iso.fun (x , Eq.refl , b) = (x , Eq.refl) , b
  ◇-fibre y .Iso.inv ((x , Eq.refl) , b) = x , Eq.refl , b
  ◇-fibre y .Iso.sec ((x , Eq.refl) , b) = refl
  ◇-fibre y .Iso.ret (x , Eq.refl , b)   = refl

  □-fibre : {B : TheoryTy ℓA t} (y : X t) → Iso (□ B y) (Fibre y → B y)
  □-fibre y .Iso.fun h (x , Eq.refl) = h x Eq.refl
  □-fibre y .Iso.inv g x Eq.refl     = g (x , Eq.refl)
  □-fibre y .Iso.sec g = funExt λ { (x , Eq.refl) → refl }
  □-fibre y .Iso.ret h = funExt λ x → funExt λ { Eq.refl → refl }

  -- THE AMBIGUITY MONAD, on the source side.
  Ker : TheoryTy ℓA s → TheoryTy (ℓ-max ℓX ℓA) s
  Ker A = δ (Σact A)

  Ker-η : {A : TheoryTy ℓA s} → A ⊢ Ker A
  Ker-η x a = x , Eq.refl , a

  -- trivial exactly when the action is mono
  Ker-triv : {A : TheoryTy ℓA s}
           → ((x x' : X s) → act x Eq.≡ act x' → x Eq.≡ x')
           → Ker A ⊢ A
  Ker-triv {A = A} inj x (x' , e , a) = go (inj x' x e) a
    where go : x' Eq.≡ x → A x' → A x
          go Eq.refl a' = a'

  -- THEOREM. `δ` commutes with EVERY additive connective, on the nose.
  module δ-laws {Y : Type ℓY}
                {B : TheoryTy ℓA t} {C : TheoryTy ℓB t}
                {F : Y → TheoryTy ℓA t} where

    δ-⊤  : δ {ℓA = ℓ-zero} ⊤G ≡ ⊤G
    δ-⊤  = refl

    δ-⊥  : δ {ℓA = ℓ-zero} ⊥G ≡ ⊥G
    δ-⊥  = refl

    δ-&  : δ (B & C) ≡ (δ B & δ C)
    δ-&  = refl

    δ-⊕  : δ (B ⊕ C) ≡ (δ B ⊕ δ C)
    δ-⊕  = refl

    δ-⇒  : δ (B ⇒ C) ≡ (δ B ⇒ δ C)
    δ-⇒  = refl

    δ-⊕ᴰ : δ (⊕ᴰ Y F) ≡ ⊕ᴰ Y (λ y → δ (F y))
    δ-⊕ᴰ = refl

    δ-&ᴰ : δ (&ᴰ Y F) ≡ &ᴰ Y (λ y → δ (F y))
    δ-&ᴰ = refl

-- The actions worth differentiating along.
module ActOf {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
             (Fib : Fibered σ ℓX (ℓ-max ℓ' ℓX)) (P : LaxPoint Fib)
             (o : σ .ops) (i : σ .arities o) (As : Assembly Fib o i)
             (a⃗ : (r : As .Rest) → Fib .carrier (σ .sortOf o (As .restOf r)))
  where

  open FibNotation Fib
  open Canon Fib P o i As

  act : Fib .carrier (σ .sortOf o i) → Fib .carrier (σ .resultSort o)
  act x = P .op o (As .tuple x a⃗)

  open Deriv (Fib .carrier) act public

  -- The residual maps to the derivative: `⊸ᶠ A B` is "B once the hole is
  -- filled by ANY complement", `δ B` is "B once it is filled by a⃗".
  δ-plug : {A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a)}
           {B : TheoryTy ℓB (σ .resultSort o)}
         → ((r : As .Rest) → A (As .restOf r) (a⃗ r))
         → ⊸ᶠ A B ⊢ δ B
  δ-plug {A = A} {B = B} pt = plug {A = A} {B = B} a⃗ pt

-- The one law that is NOT free: differentiating a composite. δ (⊗ˢ o' A) x
-- = Σ[ sp ∈ Split o' (act x) ] (payloads) so everything turns on
-- describing `Split o' (act x)` in terms of `x` -- an INVERSION PRINCIPLE
-- for the action, i.e.
module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
         (Fib : Fibered σ ℓX (ℓ-max ℓ' ℓX)) (P : LaxPoint Fib)
         (o : σ .ops) (i : σ .arities o) (As : Assembly Fib o i)
         (a⃗ : (r : As .Rest) → Fib .carrier (σ .sortOf o (As .restOf r)))
  where

  open FibNotation Fib
  open ActOf Fib P o i As a⃗

  -- `R` is the instance's answer: what the derivative of this composite
  -- unfolds to.
  DerivTensor : (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
                (R : TheoryTy ℓB (σ .sortOf o i))
              → Type (ℓ-max ℓ' (ℓ-max ℓX (ℓ-max ℓA ℓB)))
  DerivTensor A R =
    (x : Fib .carrier (σ .sortOf o i)) → Iso (δ (⊗ˢ o A) x) (R x)

  -- Having it, the derivative of a composite is a grammar map both ways.
  fromDerivTensor : {A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a)}
                    {R : TheoryTy ℓB (σ .sortOf o i)}
                  → DerivTensor A R → (δ (⊗ˢ o A) ⊢ R)
  fromDerivTensor h x = h x .Iso.fun

  intoDerivTensor : {A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a)}
                    {R : TheoryTy ℓB (σ .sortOf o i)}
                  → DerivTensor A R → (R ⊢ δ (⊗ˢ o A))
  intoDerivTensor h x = h x .Iso.inv
