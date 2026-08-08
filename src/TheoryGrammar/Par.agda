{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The product over decompositions -- AUW's `G` -- and the currying law
   that lets enumerability be stated internally. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Par where

open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥*)

import Cubical.Data.Equality as Eq
open import Cubical.Foundations.Isomorphism
open import TheoryGrammar.BaseChange
open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Rules
open import TheoryGrammar.RulesFib

private variable ℓS ℓ ℓ' ℓX ℓP ℓA ℓB : Level

module ParS {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (Fib : Fibered σ ℓX ℓP) where

  open RulesF Fib public

  private variable s : S

  -- internal negation
  ¬G_ : TheoryTy ℓA s → TheoryTy ℓA s
  ¬G A = A ⇒ ⊥G

  infix 32 ¬G_

  -- The product over decompositions, where ⊗ is the sum.  AUW's `G` at
  -- an arbitrary theory; needs no hypotheses.  See the header for why
  -- this is not called `⅋`.
  Allˢ : (o : σ .ops)
     → ((a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
     → TheoryTy (ℓ-max ℓP (ℓ-max ℓ' ℓA)) (σ .resultSort o)
  Allˢ o A m = (sp : Fib .Split o m)
           → ((a : σ .arities o) → A a (Fib .parts o m sp a))

  -- ⊗ˢ AND Allˢ ARE Σ AND Π OVER THE SAME FIBRE.

  -- ⊗ˢ IS Σᴿ, on the nose up to one singleton contraction.

  Splits : σ .ops → Type (ℓ-max ℓX ℓP)
  Splits o = Σ[ m ∈ Fib .carrier (σ .resultSort o) ] Fib .Split o m

  ⊗ˢ≅Σᴿ : (o : σ .ops)
          {A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a)}
          (m : Fib .carrier (σ .resultSort o))
        → Iso (⊗ˢ o A m)
              (Rel.Σᴿ (λ (s : Splits o) (m' : Fib .carrier (σ .resultSort o))
                         → s .fst Eq.≡ m')
                      (λ s → (a : σ .arities o) → A a (Fib .parts o (s .fst) (s .snd) a))
                      m)
  ⊗ˢ≅Σᴿ o m .Iso.fun (sp , h)                    = (m , sp) , Eq.refl , h
  ⊗ˢ≅Σᴿ o m .Iso.inv ((_ , sp) , Eq.refl , h)    = sp , h
  ⊗ˢ≅Σᴿ o m .Iso.sec ((_ , sp) , Eq.refl , h)    = refl
  ⊗ˢ≅Σᴿ o m .Iso.ret (sp , h)                    = refl

  -- THE RESIDUAL IS Πᴿ, AND THE ADJUNCTION IS FREE: `⊗ ⊣ ⊸` needs no new
  -- `Fibered` law, only the relational residual below.

  R⊸ : (o : σ .ops) (i : σ .arities o)
       (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
     → Fib .carrier (σ .sortOf o i)
     → Fib .carrier (σ .resultSort o) → Type (ℓ-max ℓP (ℓ-max ℓ' (ℓ-max ℓX ℓA)))
  R⊸ o i A x m =
    Σ[ sp ∈ Fib .Split o m ]
      ((Fib .parts o m sp i ≡ x)
       × ((a : σ .arities o) → A a (Fib .parts o m sp a)))

  ⊸ˢ≅Πᴿ : (o : σ .ops) (i : σ .arities o)
          {A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a)}
          {B : TheoryTy ℓB (σ .resultSort o)}
          (x : Fib .carrier (σ .sortOf o i))
        → Iso (⊸ˢ o i A B x) (Rel.Πᴿ (R⊸ o i A) B x)
  ⊸ˢ≅Πᴿ o i x .Iso.fun f m (sp , e , h) = f m sp e h
  ⊸ˢ≅Πᴿ o i x .Iso.inv g m sp e h       = g m (sp , e , h)
  ⊸ˢ≅Πᴿ o i x .Iso.sec _ = refl
  ⊸ˢ≅Πᴿ o i x .Iso.ret _ = refl

  ⊗ˢ→Allˢ : (o : σ .ops)
            {A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a)}
            (m : Fib .carrier (σ .resultSort o))
          → isProp (Fib .Split o m)
          → ⊗ˢ o A m → Allˢ o A m
  ⊗ˢ→Allˢ o {A = A} m pr (sp , h) sp' =
    subst (λ s → (a : σ .arities o) → A a (Fib .parts o m s a)) (pr sp sp') h

  module _ (o : σ .ops)
           (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a)) where

    -- the slotwise refutation at one decomposition
    Miss : TheoryTy (ℓ-max ℓP (ℓ-max ℓ' ℓA)) (σ .resultSort o)
    Miss m = (sp : Fib .Split o m)
           → ((a : σ .arities o) → A a (Fib .parts o m sp a)) → ⊥* {ℓ-zero}

    -- Refuting a tensor is a PRODUCT of refutations, one per
    -- decomposition.

    ¬⊗-curry : (m : Fib .carrier (σ .resultSort o)) → Iso ((¬G (⊗ˢ o A)) m) (Miss m)
    ¬⊗-curry m .Iso.fun f sp h = f (sp , h)
    ¬⊗-curry m .Iso.inv g (sp , h) = g sp h
    ¬⊗-curry m .Iso.sec _ = refl
    ¬⊗-curry m .Iso.ret _ = refl

  -- ENUMERABILITY, STATED INTERNALLY. Note this does NOT depend on the
  -- product above being well behaved: the refuting side is `∀sp. ¬(∏
  -- slots)`, which is fine whatever happens to associativity.

  ⊗-EM : (o : σ .ops)
       → ((a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
       → Type (ℓ-max ℓX (ℓ-max ℓP (ℓ-max ℓ' ℓA)))
  ⊗-EM o A = ⊤G ⊢ ((⊗ˢ o A) ⊕ (¬G (⊗ˢ o A)))

  -- the same, with the refuting side displayed as the product
  ⊗-EM' : (o : σ .ops)
        → ((a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
        → Type (ℓ-max ℓX (ℓ-max ℓP (ℓ-max ℓ' ℓA)))
  ⊗-EM' o A = ⊤G ⊢ ((⊗ˢ o A) ⊕ Miss o A)

  -- the two are interchangeable, by De Morgan
  EM→EM' : (o : σ .ops) (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
         → ⊗-EM o A → ⊗-EM' o A
  EM→EM' o A e m t = shift (e m t)
    where shift : ((⊗ˢ o A) ⊕ (¬G (⊗ˢ o A))) m → ((⊗ˢ o A) ⊕ Miss o A) m
          shift (inl x) = inl x
          shift (inr k) = inr (¬⊗-curry o A m .Iso.fun k)

  EM'→EM : (o : σ .ops) (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
         → ⊗-EM' o A → ⊗-EM o A
  EM'→EM o A e m t = shift (e m t)
    where shift : ((⊗ˢ o A) ⊕ Miss o A) m → ((⊗ˢ o A) ⊕ (¬G (⊗ˢ o A))) m
          shift (inl x) = inl x
          shift (inr g) = inr (¬⊗-curry o A m .Iso.inv g)
