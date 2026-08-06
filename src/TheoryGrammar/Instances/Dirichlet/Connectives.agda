{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  LambekD's connectives at the Dirichlet substrate.

  This file is, deliberately, Instances/Strings/Connectives with `Split3`
  replaced by `Times`.  That it can be is the whole content: the calculus
  never knew it was about strings.  The dictionary is

      ε' = ⊗ˢ nilop (λ ())        δ = ⊗ˢ oneop (λ ())     "the index is 1"
      A ⊗ B  over cuts            A ⊗ B  over factorings
      literal c = ⌈ c ∷ [] ⌉      ⌈ p ⌉                    a fixed number
      C ⟜ A  = left quotient      C ⟜ A  = DIVISION

  and only the last entry has any surprise in it.  `C ⟜ A` at e is

      (sa : Σ[ d , n ] d · e = n) → A d → C n,

  i.e. "however you multiply me by something satisfying A, the result
  satisfies C".  For strings that reads "however you extend me on the
  left"; here it reads "for every multiple of me by an A".  So the
  residual of Dirichlet convolution is division, and the `Focus` record
  supplies the one-hole factorisation d · [-] = n directly rather than
  reconstructing it from an equation -- which is why `⟜-app` below, like
  its string counterpart, needs no transport at all.

  ------------------------------------------------------------------
  PHASE.  Everything in this file is phase 1: it builds the language.
  The pointful definitions are all NAMED PRIMITIVES with a `⊢` type or a
  stated intro/elim shape, and they are the only pointful things any
  later file is allowed to use.  `⊗-mk`, `⊗I`, `⊗E`, `⊗-elim` are the
  intro/elim pair for `⊗ˢ mulop`; `⊕-elim`, `⊕ᴰ-in`, `⊕ᴰ-elim`, `liftg`
  are Gr-monomorphic spellings of the polymorphic rules from `RulesS`,
  present only because grammar-valued implicits are not inferrable
  (CLAUDE.md, "Known traps").

  ONE INFERENCE NOTE.  `⊗-mk` and `⊗I` take the two factors EXPLICITLY,
  where the string versions leave them implicit.  The reason is exact:
  in `Split3 u v w` the parts appear as bare indices and unify, but in
  `Times (val d) (val e) (val n)` they appear under `val`, i.e. under a
  projection of a Σ, and `val d =?= suc (suc k)` has no solution for d.
  The output index `n` stays implicit because it is fixed by the expected
  type `(A ⊗' B) n`.  This is the ℕ₊-as-a-Σ tax, and it is the only one.
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Dirichlet.Connectives where

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
open import TheoryGrammar.Substrate

open import TheoryGrammar.Instances.Dirichlet.Base public

-- ==================================================================
-- The multiplicatives.
-- ==================================================================

-- the ⊗-unit: "the index is 1".  Dirichlet's δ.
δ : Gr
δ = ⊗ˢ oneop (λ ())

-- DIRICHLET CONVOLUTION.
_⊗'_ : Gr → Gr → Gr
A ⊗' B = ⊗ˢ mulop (λ b → if b then A else B)

infixr 20 _⊗'_

-- the analogue of `literal`: a single number, the representable
num : ℕ₊ → Gr
num n = ⌈ n ⌉

-- PRIMITIVE (phase 1): ⊗ intro.  d and e explicit -- see the header.
⊗-mk : {A B : Gr} (d e : ℕ₊) {n : ℕ₊}
     → Times (val d) (val e) (val n) → A d → B e → (A ⊗' B) n
⊗-mk d e t a b = (d , e , t) , λ { true → a ; false → b }

-- PRIMITIVE (phase 1): ⊗ elim.
⊗-elim : {A B C : Gr}
       → (∀ {d e n} → A d → B e → Times (val d) (val e) (val n) → C n)
       → (A ⊗' B) ⊢ C
⊗-elim f n ((d , e , t) , h) = f (h true) (h false) t

-- PRIMITIVE (phase 1): the same pair at an arbitrary Bool-indexed
-- motive, so that descriptions (whose slot family is not `if`-shaped)
-- can be built and consumed without matching a splitting.
⊗I : {P : Bool → ℕ₊ → Type₀} (d e : ℕ₊) {n : ℕ₊}
   → Times (val d) (val e) (val n) → P true d → P false e
   → Σ[ sp ∈ DirSplit mulop n ] ((a : Bool) → P a (DirParts mulop n sp a))
⊗I d e t p q = (d , e , t) , λ { true → p ; false → q }

⊗E : {P : Bool → ℕ₊ → Type₀} {R : Type₀} {n : ℕ₊}
   → ((d e : ℕ₊) → Times (val d) (val e) (val n) → P true d → P false e → R)
   → Σ[ sp ∈ DirSplit mulop n ] ((a : Bool) → P a (DirParts mulop n sp a)) → R
⊗E f ((d , e , t) , h) = f d e t (h true) (h false)

δ-mk : δ one₊
δ-mk = tt , λ ()

-- ==================================================================
-- Combinators.  Gr-monomorphic spellings of the rules in `RulesS`;
-- programs downstream use these and nothing else.
-- ==================================================================

⊤' : Gr
⊤' _ = Unit

⊕-elim : {P Q R : Gr} → P ⊢ R → Q ⊢ R → (P ⊕ Q) ⊢ R
⊕-elim f g n (inl p) = f n p
⊕-elim f g n (inr q) = g n q

⊕ᴰ-in : {Y : Type₀} {P : Y → Gr} (y : Y) → P y ⊢ ⊕ᴰ Y P
⊕ᴰ-in y n p = y , p

⊕ᴰ-elim : {Y : Type₀} {P : Y → Gr} {R : Gr}
        → ((y : Y) → P y ⊢ R) → ⊕ᴰ Y P ⊢ R
⊕ᴰ-elim f n (y , p) = f y n p

liftg : {P : Gr} → P ⊢ (λ n → Lift ℓ-zero (P n))
liftg _ p = lift p

⊗-map : {P P' Q Q' : Gr} → P ⊢ P' → Q ⊢ Q' → (P ⊗' Q) ⊢ (P' ⊗' Q')
⊗-map f g n ((d , e , t) , h) = ⊗-mk d e t (f d (h true)) (g e (h false))

-- ==================================================================
-- The residual at slot `false` -- DIVISION.
--
-- `Focus` asks for the one-hole factorisations viewed from the right
-- factor: given e, the pairs (d , n) with d · e = n.  Because that is
-- supplied as data, `⟜-app` is a projection and not a transport.
-- ==================================================================

focR : Focus dirSub mulop false
focR .SplitAt e = Σ[ d ∈ ℕ₊ ] Σ[ n ∈ ℕ₊ ] Times (val d) (val e) (val n)
focR .whole (d , n , _)      = n
focR .Rest                   = Unit
focR .restOf _               = true
focR .restSlot (d , n , _) _ = d

module R = FocusNotation focR

-- "C after dividing out an A"
_⟜'_ : Gr → Gr → Gr
C ⟜' A = R.⊸ᶠ (λ b → if b then A else C) C

⟜-app : {A C : Gr} → (A ⊗' (C ⟜' A)) ⊢ C
⟜-app n ((d , e , t) , h) = h false (d , n , t) (λ _ → h true)

module _ {A B C : Gr} where

  ⟜-intro : (A ⊗' B) ⊢ C → B ⊢ (C ⟜' A)
  ⟜-intro f e be (d , n , t) g = f n (⊗-mk d e t (g tt) be)

  ⟜-intro⁻ : B ⊢ (C ⟜' A) → (A ⊗' B) ⊢ C
  ⟜-intro⁻ h = ⊗-elim λ {d} {e} {n} a be t → h e be (d , n , t) (λ _ → a)

  -- β is definitional: Unit has η, so `λ _ → g tt` IS `g`.
  ⟜-β : (h : B ⊢ (C ⟜' A)) → ⟜-intro (⟜-intro⁻ h) ≡ h
  ⟜-β h = refl

  -- η needs funExt over the ARITY, because Bool has no η.  Exactly the
  -- same one cost the string instance pays.
  ⟜-η : (f : (A ⊗' B) ⊢ C) → ⟜-intro⁻ (⟜-intro f) ≡ f
  ⟜-η f = funExt λ n → funExt λ { ((d , e , t) , h) →
    cong (λ k → f n ((d , e , t) , k)) (funExt λ { true → refl ; false → refl }) }

  ⟜UMP : Iso ((A ⊗' B) ⊢ C) (B ⊢ (C ⟜' A))
  ⟜UMP .Iso.fun = ⟜-intro
  ⟜UMP .Iso.inv = ⟜-intro⁻
  ⟜UMP .Iso.sec = ⟜-β
  ⟜UMP .Iso.ret = ⟜-η
