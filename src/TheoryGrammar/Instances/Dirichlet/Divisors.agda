{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- DIVISORS FOR FREE. The point of this file is that almost nothing happens
   in it. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Dirichlet.Divisors where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered

open import TheoryGrammar.Instances.Dirichlet.Connectives public

-- The two constants.

-- ζ: every index, exactly once.  The constant Dirichlet series 1.
ζ : Gr
ζ = ⊤'

-- δ is `⊗ˢ oneop`; that it is also the representable at 1 is the
-- `Fibered`'s unit law, and both directions are phase 2.
δ→⌈1⌉ : δ ⊢ ⌈ one₊ ⌉
δ→⌈1⌉ (zero , ())
δ→⌈1⌉ (suc zero , p) _ = Eq.refl
δ→⌈1⌉ (suc (suc m) , p) (() , _)

⌈1⌉→δ : ⌈ one₊ ⌉ ⊢ δ
⌈1⌉→δ = ⌈⌉-E δ-mk                       -- ⌈⌉-UP, i.e. Yoneda

-- THE DIVISOR GRAMMAR.  τ = ζ ⊗ ζ, and this is DEFINITIONALLY the
-- type of factorisations.

τ : Gr
τ = ζ ⊗' ζ

-- The same convolution with the arity family written CONSTANTLY rather
-- than by `if`.
τᶜ : Gr
τᶜ = ⊗ˢ mulop (λ _ → ζ)

-- Not an isomorphism to be constructed: an equality of types, by refl.
-- `(ζ ⊗ ζ) n` IS the type of factorisations of n (times a contractible
-- tail, one `Unit` per slot).
divisorsAreFactorisations : (n : ℕ₊) → τᶜ n ≡ (DirSplit mulop n × (Bool → Unit))
divisorsAreFactorisations n = refl

-- and the contractible tail really does collapse.  Only `ret` is not
-- `refl`, and only because of the stuck `if`.
τIso : (n : ℕ₊) → Iso (τ n) (DirSplit mulop n)
τIso n .Iso.fun            = fst
τIso n .Iso.inv sp         = sp , λ { true → tt ; false → tt }
τIso n .Iso.sec _          = refl
τIso n .Iso.ret (sp , h)   =
  cong (sp ,_) (funExt λ { true → refl ; false → refl })

-- ORDERED k-FACTORISATIONS: the k-fold convolution power of ζ.
-- τ[ 0 ] = δ, τ[ 1 ] ≅ ζ, τ[ 2 ] = τ.
τ[_] : ℕ → Gr
τ[ zero  ] = δ
τ[ suc k ] = ζ ⊗' τ[ k ]

-- divisibility, as a grammar: `Div d` holds at n iff d divides n
Div : ℕ₊ → Gr
Div d = ⌈ d ⌉ ⊗' ⊤'

-- ... and it computes.  6 = 2 · 3.
_ : Div (2 , tt) (6 , tt)
_ = ⊗-mk (2 , tt) (3 , tt) (timesAll 2 3) Eq.refl tt

_ : τ (6 , tt)
_ = ⊗-mk (2 , tt) (3 , tt) (timesAll 2 3) tt tt

-- THE UNIT LAW. One primitive, and then the two maps are `⊗ˢ-UP` and
-- `⌈⌉-UP` applied to it.

-- PRIMITIVE (phase 1): a factorisation with a unit on one side has its
-- other factor equal to the whole.
unitL : {e n : ℕ₊} → Times 1 (val e) (val n) → e ≡ n
unitL {e} t = ℕ₊≡ (sym (·-identityˡ (val e)) ∙ timesPath t)

unitR : {d n : ℕ₊} → Times (val d) 1 (val n) → d ≡ n
unitR {d} t = ℕ₊≡ (sym (·-identityʳ (val d)) ∙ timesPath t)

⊗-unit-l : {A : Gr} → (⌈ one₊ ⌉ ⊗' A) ⊢ A
⊗-unit-l {A} = ⊗-elim λ { Eq.refl a t → subst A (unitL t) a }

⊗-unit-r : {A : Gr} → (A ⊗' ⌈ one₊ ⌉) ⊢ A
⊗-unit-r {A} = ⊗-elim λ { a Eq.refl t → subst A (unitR t) a }

⊗-unit-l⁻ : {A : Gr} → A ⊢ (⌈ one₊ ⌉ ⊗' A)
⊗-unit-l⁻ n a = ⊗-mk one₊ n (times1L (val n)) Eq.refl a

⊗-unit-r⁻ : {A : Gr} → A ⊢ (A ⊗' ⌈ one₊ ⌉)
⊗-unit-r⁻ n a = ⊗-mk n one₊ (times1R (val n)) a Eq.refl

isSetℕ₊ : isSet ℕ₊
isSetℕ₊ = isSetΣ isSetℕ (λ n → isProp→isSet (isPropNonZero n))

-- the round trip that Instances/Strings/Laws also proves.
⊗-unit-ll⁻ : {A : Gr} → ∀ n (a : A n) → ⊗-unit-l n (⊗-unit-l⁻ {A = A} n a) ≡ a
⊗-unit-ll⁻ {A} n a =
  cong (λ q → subst A q a) (isSetℕ₊ n n (unitL (times1L (val n))) refl)
  ∙ substRefl {B = A} a

⊗-unit-rr⁻ : {A : Gr} → ∀ n (a : A n) → ⊗-unit-r n (⊗-unit-r⁻ {A = A} n a) ≡ a
⊗-unit-rr⁻ {A} n a =
  cong (λ q → subst A q a) (isSetℕ₊ n n (unitR (times1R (val n))) refl)
  ∙ substRefl {B = A} a

-- COMMUTATIVITY.  ⊗ is symmetric here, unlike in the string instance.
-- The proof is `·-comm` transported across `Times`, once.

-- PRIMITIVE (phase 1): factorisations can be reversed.
timesSwap : {d e n : ℕ} → Times d e n → Times e d n
timesSwap {d} {e} {n} t =
  subst (Times e d) (·-comm e d ∙ timesPath t) (timesAll e d)

⊗-swap : {A B : Gr} → (A ⊗' B) ⊢ (B ⊗' A)
⊗-swap = ⊗-elim λ {d} {e} a b t → ⊗-mk e d (timesSwap t) b a
