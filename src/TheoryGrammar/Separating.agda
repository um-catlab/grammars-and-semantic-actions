{-
  UNIQUE READABILITY MAKES ⊗ SEPARATING.

      (⊗ˢ o A & ⊗ˢ o B)  ⊢  ⊗ˢ o (λ a → A a & B a)

  The additive conjunction of two o-tensors is the o-tensor of the
  slotwise conjunctions, because the two splittings of the same `m` are
  the same splitting.  This is `⊗-refute`'s positive twin: both are
  consequences of `splitProp` alone, and both are what an instance uses
  to compare two derivations of the same term.
-}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Separating where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import TheoryGrammar.Base
open import TheoryGrammar.Substrate

private variable ℓS ℓ ℓ' ℓX ℓP ℓA ℓB : Level

module Sep {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (Sub : Substrate σ ℓX ℓP)
           (splitProp : (o : σ .ops) (m : Sub .carrier (σ .resultSort o))
                        (p q : Sub .Split o m) → p ≡ q)
  where

  open SubNotation Sub

  ⊗-merge : (o : σ .ops)
            (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
            (B : (a : σ .arities o) → TheoryTy ℓB (σ .sortOf o a))
          → (⊗ˢ o A & ⊗ˢ o B) ⊢ ⊗ˢ o (λ a → A a & B a)
  ⊗-merge o A B m (x , y) =
    x .fst , λ a → x .snd a
                 , subst (λ z → B a (Sub .parts o m z a))
                         (splitProp o m (y .fst) (x .fst)) (y .snd a)
