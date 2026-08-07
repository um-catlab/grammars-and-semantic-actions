{-
  BASE CHANGE ALONG A RELATION -- and the modalities it generates.

  Every modality in this development has been built by hand and then
  recognised, afterwards, as Σ or Π over some fibre:

      Σact / Πact   (Derivative)  -- over the fibre of an action
      ⊗ˢ   / Allˢ   (Par)         -- over `Split o m`
      ▷            (Later)        -- over `j ≺ i`

  They are all one construction.  A relation `R : I → J → Type` -- an
  ACCESSIBILITY STRUCTURE on worlds -- induces

      Σᴿ A j = Σ[ i ] R i j × A i      "some R-predecessor of j is an A"
      Πᴿ B i = (j) → R i j → B j       "every R-successor of i is a B"

  and `Σᴿ ⊣ Πᴿ`.  The adjunction is CURRYING: both round trips are
  `refl`, and no hypothesis on `R` is used.  So the modalities are not
  chosen, they are the (co)monads this adjunction generates, exactly as
  they should be.

  THE THREE INSTANCES.

  * `R` = the graph of a function `act`.  Then `Πᴿ` is precomposition,
    i.e. `δ` -- which is why the derivative has a THREE-fold adjunction
    where the others have two.  A function is a relation with a middle
    functor.

  * `R m⃗ m` = "m splits as m⃗".  Then `Σᴿ` is `⊗ˢ` and `Πᴿ` is `Allˢ`,
    modulo the external product turning a slot-family into a
    tuple-family.

  * `R j i` = `j ≺ i`.  Then `Πᴿ` is `▷`, and `löb` is its fixed point.

  What this buys beyond tidiness: the (co)monads below are defined once,
  so `◇`/`□` at an action, "the ambiguity of a splitting", and the
  guarded modality are the same object at three relations -- and a fact
  proved here holds for all of them.
-}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.BaseChange where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)

private variable ℓI ℓJ ℓR ℓA ℓB : Level

module Rel {I : Type ℓI} {J : Type ℓJ} (R : I → J → Type ℓR) where

  Σᴿ : (I → Type ℓA) → (J → Type (ℓ-max ℓI (ℓ-max ℓR ℓA)))
  Σᴿ A j = Σ[ i ∈ I ] (R i j × A i)

  Πᴿ : (J → Type ℓB) → (I → Type (ℓ-max ℓJ (ℓ-max ℓR ℓB)))
  Πᴿ B i = (j : J) → R i j → B j

  -- ================================================================
  -- THE ADJUNCTION.  `Σᴿ ⊣ Πᴿ`, and it is currying -- both round trips
  -- are `refl`, with no hypothesis on `R` whatsoever.
  -- ================================================================

  Σ⊣Π : {A : I → Type ℓA} {B : J → Type ℓB}
       → Iso ((j : J) → Σᴿ A j → B j) ((i : I) → A i → Πᴿ B i)
  Σ⊣Π .Iso.fun f i a j r     = f j (i , r , a)
  Σ⊣Π .Iso.inv g j (i , r , a) = g i a j r
  Σ⊣Π .Iso.sec _ = refl
  Σ⊣Π .Iso.ret _ = refl

  -- ================================================================
  -- ... and hence the modalities, generated rather than posited.
  -- ================================================================

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

  -- ================================================================
  -- PRESERVATION.  A left adjoint preserves coproducts; a right adjoint
  -- preserves products.  Proved ONCE here, they hold for every instance
  -- -- the guarded modality, the derivative's adjoints, and the
  -- convolution -- which is the point of having the general form.
  --
  -- Neither preserves the other side, and the asymmetry is real:
  -- `Σᴿ (A & B)` is strictly stronger than `Σᴿ A & Σᴿ B` once `R i j`
  -- has more than one inhabitant, because the left says ONE witness
  -- serves both.  `Σᴿ-&` is that one-way comparison.
  -- ================================================================

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

  -- ================================================================
  -- THE COMPARISON, and what it measures.
  --
  -- `Σᴿ A j → Πᴿ`-style universality needs the accessibility structure
  -- to be a PROPOSITION -- "at most one way to reach j".  That single
  -- statement is `splitProp` for a splitting, injectivity for an
  -- action, and antisymmetry-of-reachability for an order: the three
  -- unique-readability hypotheses in this development are one
  -- condition on `R`.
  -- ================================================================

  Σ→all : {A : I → Type ℓA} (j : J)
        → ((i i' : I) → R i j → R i' j → i ≡ i')
        → Σᴿ A j → ((i : I) → R i j → A i)
  Σ→all {A = A} j uniq (i , r , a) i' r' = subst A (uniq i i' r r') a
