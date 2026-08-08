{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- THE CONNECTIVES AT (ℕ, +): ε, ⊗, the generator x, and the residual ⟜. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Nat.Connectives where

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

open import TheoryGrammar.Instances.Nat.Base public

-- The multiplicative unit and product.

ε' : Gr
ε' = ⊗ˢ nilop (λ ())

-- NOT `MonSep._∗_`, and the reason is measured rather than assumed: this
-- file spells the slot family `λ b → if b then A else B`, `MonSep` uses
-- `boolΠ`, and arities have no η -- both are stuck on `b`, at different
-- definitions, so the two are NOT definitionally equal.
_⊗'_ : Gr → Gr → Gr
A ⊗' B = ⊗ˢ appop (λ b → if b then A else B)

infixr 20 _⊗'_

-- THE GENERATOR.  ℕ is the free monoid on one letter and `x` is that
-- letter: the analogue of `literal c`, with the alphabet a singleton.
x : Gr
x = ⌈ 1 ⌉

⊤' : Gr
⊤' = ⊤G

-- ⊗ intro and elim.  These two are the only places below that mention
-- an `Add3`; everything after composes them.

-- PRIMITIVE (phase 1): ⊗-intro.
⊗-mk : {A B : Gr} {i j n : ℕ} → Add3 i j n → A i → B j → (A ⊗' B) n
⊗-mk {i = i} {j} a p q = (i , j , a) , λ { true → p ; false → q }

-- PRIMITIVE (phase 1): ⊗-elim.
⊗-elim : {A B C : Gr}
       → (∀ {i j n} → A i → B j → Add3 i j n → C n)
       → (A ⊗' B) ⊢ C
⊗-elim f n ((i , j , a) , h) = f (h true) (h false) a

-- PRIMITIVE (phase 1): ε-intro, the unique point of the unit.
ε-mk : ε' 0
ε-mk = tt , λ ()

-- The arity-generic forms, matching `Bags/Connectives.agda` field for
-- field, for code that has to talk about `Sh`/`⟦_⟧c` directly.
⊗I : {P : Bool → ℕ → Type₀} {i j n : ℕ}
   → Add3 i j n → P true i → P false j
   → Σ[ sp ∈ MonSplit appop n ] ((a : Bool) → P a (MonParts appop n sp a))
⊗I {i = i} {j} a p q = (i , j , a) , λ { true → p ; false → q }

⊗E : {P : Bool → ℕ → Type₀} {R : Type₀} {n : ℕ}
   → ((i j : ℕ) → Add3 i j n → P true i → P false j → R)
   → Σ[ sp ∈ MonSplit appop n ] ((a : Bool) → P a (MonParts appop n sp a)) → R
⊗E f ((i , j , a) , h) = f i j a (h true) (h false)

⊗-map : {A A' B B' : Gr} → A ⊢ A' → B ⊢ B' → (A ⊗' B) ⊢ (A' ⊗' B')
⊗-map f g n ((i , j , a) , h) = ⊗-mk a (f i (h true)) (g j (h false))

-- Additive combinators.  `RulesF` already supplies `idg`, `_∘g_`,
-- `⊕-E`, `⊕ᴰ-I`, `⊕ᴰ-E`, `&-I`, `⊤-I`, `⌈⌉-E`; these are the aliases
-- the `Bags` instance uses, kept so the two read alike.

⊕-elim : {A B C : Gr} → A ⊢ C → B ⊢ C → (A ⊕ B) ⊢ C
⊕-elim = ⊕-E

⊕ᴰ-in : {Y : Type₀} {A : Y → Gr} (y : Y) → A y ⊢ ⊕ᴰ Y A
⊕ᴰ-in {Y = Y} y = ⊕ᴰ-I Y y

⊕ᴰ-elim : {Y : Type₀} {A : Y → Gr} {B : Gr}
        → ((y : Y) → A y ⊢ B) → ⊕ᴰ Y A ⊢ B
⊕ᴰ-elim = ⊕ᴰ-E

-- PRIMITIVE (phase 1): the universe shuffle.

-- `Add3 i j n` IS the equation `i + j = n` -- the Cauchy-product
-- coefficient count.

add3→+ : {i j n : ℕ} → Add3 i j n → i + j Eq.≡ n
add3→+ z     = Eq.refl
add3→+ (s a) = Eq.ap suc (add3→+ a)

+→add3 : (i j : ℕ) {n : ℕ} → i + j Eq.≡ n → Add3 i j n
+→add3 i j Eq.refl = addAll i j

-- The residual, at slot `false` (the right factor), exactly as
-- Strings/Connectives.  `C ⟜' A` is "C divided by A on the left".

focR : Focus natFib appop false
focR .SplitAt j  = Σ[ i ∈ ℕ ] Σ[ n ∈ ℕ ] Add3 i j n
focR .whole (i , n , _) = n
focR .Rest       = Unit
focR .restOf _   = true
focR .restSlot (i , n , _) _ = i

module R = FocusNotation focR

_⟜'_ : Gr → Gr → Gr
C ⟜' A = R.⊸ᶠ (λ b → if b then A else C) C

-- ⟜-app: no transport, because the splitting already names the whole.
⟜-app : {A C : Gr} → (A ⊗' (C ⟜' A)) ⊢ C
⟜-app n ((i , j , a) , h) = h false (i , n , a) (λ _ → h true)

-- THE ADJUNCTION.
module _ {A B C : Gr} where

  ⟜-intro : (A ⊗' B) ⊢ C → B ⊢ (C ⟜' A)
  ⟜-intro f j bj (i , n , a) g = f n (⊗-mk a (g tt) bj)

  ⟜-intro⁻ : B ⊢ (C ⟜' A) → (A ⊗' B) ⊢ C
  ⟜-intro⁻ h = ⊗-elim λ p bj a → h _ bj (_ , _ , a) (λ _ → p)

  -- β is definitional (Unit has η, so `λ _ → g tt` IS `g`)
  ⟜-β : (h : B ⊢ (C ⟜' A)) → ⟜-intro (⟜-intro⁻ h) ≡ h
  ⟜-β h = refl

  -- η needs funExt over the ARITY, because Bool has no η.  Same single
  -- cost as in the string instance, from the same cause.
  ⟜-η : (f : (A ⊗' B) ⊢ C) → ⟜-intro⁻ (⟜-intro f) ≡ f
  ⟜-η f = funExt λ n → funExt λ { ((i , j , a) , h) →
    cong (λ k → f n ((i , j , a) , k)) (funExt λ { true → refl ; false → refl }) }

  ⟜UMP : Iso ((A ⊗' B) ⊢ C) (B ⊢ (C ⟜' A))
  ⟜UMP .Iso.fun = ⟜-intro
  ⟜UMP .Iso.inv = ⟜-intro⁻
  ⟜UMP .Iso.sec = ⟜-β
  ⟜UMP .Iso.ret = ⟜-η
