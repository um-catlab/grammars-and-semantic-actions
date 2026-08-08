{- BASE CHANGE ALONG A RELATION -- and the modalities it generates. -}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.BaseChange where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)

private variable ℓI ℓJ ℓR ℓA ℓB : Level

-- THE PRINCIPLE, at its actual level of generality.

Σ-det : {F : Type ℓI} (P : F → Type ℓA) (Q : F → Type ℓB) → Type _
Σ-det {F = F} P Q = (f f' : F) → P f → Q f' → f ≡ f'

Σ-&-conv : {F : Type ℓI} {P : F → Type ℓA} {Q : F → Type ℓB}
         → Σ-det P Q → (Σ F P × Σ F Q) → Σ F (λ f → P f × Q f)
Σ-&-conv {Q = Q} det ((f , p) , (f' , q)) =
  f , p , subst Q (sym (det f f' p q)) q

module Rel {I : Type ℓI} {J : Type ℓJ} (R : I → J → Type ℓR) where

  Σᴿ : (I → Type ℓA) → (J → Type (ℓ-max ℓI (ℓ-max ℓR ℓA)))
  Σᴿ A j = Σ[ i ∈ I ] (R i j × A i)

  Πᴿ : (J → Type ℓB) → (I → Type (ℓ-max ℓJ (ℓ-max ℓR ℓB)))
  Πᴿ B i = (j : J) → R i j → B j

  -- THE ADJUNCTION.  `Σᴿ ⊣ Πᴿ`, and it is currying -- both round trips
  -- are `refl`, with no hypothesis on `R` whatsoever.

  Σ⊣Π : {A : I → Type ℓA} {B : J → Type ℓB}
       → Iso ((j : J) → Σᴿ A j → B j) ((i : I) → A i → Πᴿ B i)
  Σ⊣Π .Iso.fun f i a j r     = f j (i , r , a)
  Σ⊣Π .Iso.inv g j (i , r , a) = g i a j r
  Σ⊣Π .Iso.sec _ = refl
  Σ⊣Π .Iso.ret _ = refl

  -- ... and hence the modalities, generated rather than posited.

  -- the COMONAD on J-families
  ◇ᴿ : (J → Type ℓB) → (J → Type _)
  ◇ᴿ B = Σᴿ (Πᴿ B)

  ◇-counit : {B : J → Type ℓB} (j : J) → ◇ᴿ B j → B j
  ◇-counit j (i , r , h) = h j r

  ◇-comult : {B : J → Type ℓB} (j : J) → ◇ᴿ B j → ◇ᴿ (◇ᴿ B) j
  ◇-comult j (i , r , h) = i , r , λ j' r' → i , r' , h

  -- the MONAD on I-families
  □ᴿ : (I → Type ℓA) → (I → Type _)
  □ᴿ A = Πᴿ (Σᴿ A)

  □-unit : {A : I → Type ℓA} (i : I) → A i → □ᴿ A i
  □-unit i a j r = i , r , a

  □-mult : {A : I → Type ℓA} (i : I) → □ᴿ (□ᴿ A) i → □ᴿ A i
  □-mult i h j r = h j r .snd .snd j (h j r .snd .fst)

  -- PRESERVATION. A left adjoint preserves coproducts; a right adjoint
  -- preserves products.

  Πᴿ-& : {B : J → Type ℓA} {C : J → Type ℓB} (i : I)
       → Iso (Πᴿ (λ j → B j × C j) i) (Πᴿ B i × Πᴿ C i)
  Πᴿ-& i .Iso.fun h       = (λ j r → h j r .fst) , (λ j r → h j r .snd)
  Πᴿ-& i .Iso.inv (f , g) = λ j r → f j r , g j r
  Πᴿ-& i .Iso.sec _ = refl
  Πᴿ-& i .Iso.ret _ = refl

  Σᴿ-⊕ : {A : I → Type ℓA} {B : I → Type ℓB} (j : J)
       → Iso (Σᴿ (λ i → A i ⊎ B i) j) (Σᴿ A j ⊎ Σᴿ B j)
  Σᴿ-⊕ j .Iso.fun (i , r , inl a)   = inl (i , r , a)
  Σᴿ-⊕ j .Iso.fun (i , r , inr b)   = inr (i , r , b)
  Σᴿ-⊕ j .Iso.inv (inl (i , r , a)) = i , r , inl a
  Σᴿ-⊕ j .Iso.inv (inr (i , r , b)) = i , r , inr b
  Σᴿ-⊕ j .Iso.sec (inl _) = refl
  Σᴿ-⊕ j .Iso.sec (inr _) = refl
  Σᴿ-⊕ j .Iso.ret (_ , _ , inl _) = refl
  Σᴿ-⊕ j .Iso.ret (_ , _ , inr _) = refl

  Σᴿ-& : {A : I → Type ℓA} {B : I → Type ℓB} (j : J)
       → Σᴿ (λ i → A i × B i) j → (Σᴿ A j × Σᴿ B j)
  Σᴿ-& j (i , r , (a , b)) = (i , r , a) , (i , r , b)

  -- WHEN DOES Σ DISTRIBUTE BACK IN? The general principle.

  FibreR : J → Type (ℓ-max ℓI ℓR)
  FibreR j = Σ[ i ∈ I ] R i j

  DetPair : (I → Type ℓA) → (I → Type ℓB) → J → Type _
  DetPair A B j = (p q : FibreR j) → A (p .fst) → B (q .fst) → p ≡ q

  -- the converse of `Σᴿ-&`, exactly under that hypothesis
  Σᴿ-&-conv : {A : I → Type ℓA} {B : I → Type ℓB} (j : J)
            → DetPair A B j
            → (Σᴿ A j × Σᴿ B j) → Σᴿ (λ i → A i × B i) j
  -- ... which is `Σ-&-conv` at `F = FibreR j`, modulo reassociating
  -- `Σ[ i ] R i j × A i` as `Σ[ p ∈ FibreR j ] A (p .fst)`.
  Σᴿ-&-conv {B = B} j det ((i , r , a) , (i' , r' , b)) =
    i , r , a , subst B (cong fst (sym (det (i , r) (i' , r') a b))) b

  -- unambiguity is inherited by refinement
  DetPair-mono : {A A' : I → Type ℓA} {B B' : I → Type ℓB} (j : J)
               → ((i : I) → A' i → A i) → ((i : I) → B' i → B i)
               → DetPair A B j → DetPair A' B' j
  DetPair-mono j fa fb det p q a' b' = det p q (fa (p .fst) a') (fb (q .fst) b')

  -- THE COMPARISON, and what it measures. `Σᴿ A j → Πᴿ`-style universality
  -- needs the accessibility structure to be a PROPOSITION -- "at most one
  -- way to reach j".

  Σ→all : {A : I → Type ℓA} (j : J)
        → ((i i' : I) → R i j → R i' j → i ≡ i')
        → Σᴿ A j → ((i : I) → R i j → A i)
  Σ→all {A = A} j uniq (i , r , a) i' r' = subst A (uniq i i' r r') a
