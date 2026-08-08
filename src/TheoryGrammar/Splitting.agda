{- MANY THEORIES ON ONE CARRIER. `Fibered` bundles the carrier with the
   splittings, so two theories over one carrier can only be stated as two
   `Fibered`s plus an EQUATION between their carriers -- green slime, and a
   coercion on every `parts` access thereafter (`Refinement`'s
   `SplitH`/`partsH` is... -}
module TheoryGrammar.Splitting where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sum using (_⊎_; inl; inr)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.ChangeOfTheory using (SigMor; onSort; onOp; onAr;
                                                resEq; sortEq)

private variable ℓS ℓ ℓ' ℓX ℓP ℓA : Level

-- THE SPLITTINGS, OFF THE CARRIER.

record Splitting {S : Type ℓS} (σ : SortedSig S ℓ ℓ') (X : S → Type ℓX) ℓP
  : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓX (ℓ-suc ℓP)))) where
  field
    Split : (o : σ .ops) → X (σ .resultSort o) → Type ℓP
    parts : (o : σ .ops) (m : X (σ .resultSort o))
          → Split o m → (a : σ .arities o) → X (σ .sortOf o a)

open Splitting public

-- `Fibered` is unchanged; these two are the only bridge, and both
-- round-trips are `refl` by record η.

⟪_,_⟫ : {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
        (X : S → Type ℓX) → Splitting σ X ℓP → Fibered σ ℓX ℓP
⟪ X , Sp ⟫ .carrier = X
⟪ X , Sp ⟫ .Split   = Sp .Split
⟪ X , Sp ⟫ .parts   = Sp .parts

splittingOf : {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (Fib : Fibered σ ℓX ℓP)
            → Splitting σ (Fib .carrier) ℓP
splittingOf Fib .Split = Fib .Split
splittingOf Fib .parts = Fib .parts

module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} where

  ⟪⟫-η : (Fib : Fibered σ ℓX ℓP) → ⟪ Fib .carrier , splittingOf Fib ⟫ ≡ Fib
  ⟪⟫-η Fib = refl

  splittingOf-η : {X : S → Type ℓX} (Sp : Splitting σ X ℓP)
                → splittingOf ⟪ X , Sp ⟫ ≡ Sp
  splittingOf-η Sp = refl

-- THE COPRODUCT OF TWO SIGNATURES, at one sort set.

module _ {S : Type ℓS} (σ τ : SortedSig S ℓ ℓ') where

  SumOps : Type ℓ
  SumOps = σ .ops ⊎ τ .ops

  SumAr : SumOps → Type ℓ'
  SumAr (inl o) = σ .arities o
  SumAr (inr o) = τ .arities o

  SumSortOf : (o : SumOps) → SumAr o → S
  SumSortOf (inl o) a = σ .sortOf o a
  SumSortOf (inr o) a = τ .sortOf o a

  SumResult : SumOps → S
  SumResult (inl o) = σ .resultSort o
  SumResult (inr o) = τ .resultSort o

infixr 5 _⊎Sig_

_⊎Sig_ : {S : Type ℓS} → SortedSig S ℓ ℓ' → SortedSig S ℓ ℓ' → SortedSig S ℓ ℓ'
(σ ⊎Sig τ) .ops        = SumOps σ τ
(σ ⊎Sig τ) .arities    = SumAr σ τ
(σ ⊎Sig τ) .sortOf     = SumSortOf σ τ
(σ ⊎Sig τ) .resultSort = SumResult σ τ

-- The two inclusions. Both coherence fields are `Eq.refl`, which IS the
-- statement that the coproduct introduces no coercion: `ChangeOfTheory`'s
-- `restrict` transports along `resEq`/`sortEq`, and here it transports
-- along nothing.
module _ {S : Type ℓS} (σ τ : SortedSig S ℓ ℓ') where

  inlSig : SigMor σ (σ ⊎Sig τ)
  inlSig .onSort  = λ s → s
  inlSig .onOp    = inl
  inlSig .onAr    = λ _ a → a
  inlSig .resEq   = λ _ → Eq.refl
  inlSig .sortEq  = λ _ _ → Eq.refl

  inrSig : SigMor τ (σ ⊎Sig τ)
  inrSig .onSort  = λ s → s
  inrSig .onOp    = inr
  inrSig .onAr    = λ _ a → a
  inrSig .resEq   = λ _ → Eq.refl
  inrSig .sortEq  = λ _ _ → Eq.refl

-- ... AND OF TWO SPLITTINGS OVER ONE CARRIER.

infixr 5 _⊎Spl_

_⊎Spl_ : {S : Type ℓS} {σ τ : SortedSig S ℓ ℓ'} {X : S → Type ℓX}
       → Splitting σ X ℓP → Splitting τ X ℓP → Splitting (σ ⊎Sig τ) X ℓP
(Sp ⊎Spl Sq) .Split (inl o) m       = Sp .Split o m
(Sp ⊎Spl Sq) .Split (inr o) m       = Sq .Split o m
(Sp ⊎Spl Sq) .parts (inl o) m sp a  = Sp .parts o m sp a
(Sp ⊎Spl Sq) .parts (inr o) m sp a  = Sq .parts o m sp a

-- The ergonomic form: take a `Fibered` you already have and ADD a second
-- theory's splittings on its carrier.  Note what is NOT asked for -- an
-- equation between two carriers.
infixr 5 _⊎Fib_

_⊎Fib_ : {S : Type ℓS} {σ τ : SortedSig S ℓ ℓ'} (Fib : Fibered σ ℓX ℓP)
       → Splitting τ (Fib .carrier) ℓP → Fibered (σ ⊎Sig τ) ℓX ℓP
Fib ⊎Fib Sq = ⟪ Fib .carrier , splittingOf Fib ⊎Spl Sq ⟫

-- THE MEASUREMENT. A derivation in a summand's calculus IS a derivation in
-- the sum's, with nothing to translate -- the same claim
-- `ChangeOfTheory.reinterpretTerm` makes for a signature morphism, but
-- here it extends to the MULTIPLICATIVES, which that one cannot do.

module _ {S : Type ℓS} {σ τ : SortedSig S ℓ ℓ'} {X : S → Type ℓX}
         (Sp : Splitting σ X ℓP) (Sq : Splitting τ X ℓP) where

  private
    module Mσ = FibNotation ⟪ X , Sp ⟫
    module Mτ = FibNotation ⟪ X , Sq ⟫
    module M⊎ = FibNotation ⟪ X , Sp ⊎Spl Sq ⟫

  -- the additives never saw an operation, so they are literally equal
  TheoryTy-⊎ : (s : S) → Mσ.TheoryTy ℓA s ≡ M⊎.TheoryTy ℓA s
  TheoryTy-⊎ _ = refl

  ⊢-⊎ : {s : S} (A B : Mσ.TheoryTy ℓA s) → (A Mσ.⊢ B) ≡ (A M⊎.⊢ B)
  ⊢-⊎ _ _ = refl

  -- and the multiplicative at an INJECTED operation is the summand's
  ⊗ˢ-inl : (o : σ .ops)
           (A : (a : σ .arities o) → Mσ.TheoryTy ℓA (σ .sortOf o a))
         → M⊎.⊗ˢ (inl o) A ≡ Mσ.⊗ˢ o A
  ⊗ˢ-inl o A = refl

  ⊗ˢ-inr : (o : τ .ops)
           (A : (a : τ .arities o) → Mτ.TheoryTy ℓA (τ .sortOf o a))
         → M⊎.⊗ˢ (inr o) A ≡ Mτ.⊗ˢ o A
  ⊗ˢ-inr o A = refl

  -- the residual too, so a whole program transports and not just a type
  ⊸ˢ-inl : (o : σ .ops) (i : σ .arities o)
           (A : (a : σ .arities o) → Mσ.TheoryTy ℓA (σ .sortOf o a))
           (B : Mσ.TheoryTy ℓA (σ .resultSort o))
         → M⊎.⊸ˢ (inl o) i A B ≡ Mσ.⊸ˢ o i A B
  ⊸ˢ-inl o i A B = refl

  -- ... hence a term of the summand's calculus needs no coercion at all
  transportsInl : (o : σ .ops)
                  (A : (a : σ .arities o) → Mσ.TheoryTy ℓA (σ .sortOf o a))
                  (B : Mσ.TheoryTy ℓA (σ .resultSort o))
                → (Mσ.⊗ˢ o A Mσ.⊢ B) → (M⊎.⊗ˢ (inl o) A M⊎.⊢ B)
  transportsInl o A B f = f
