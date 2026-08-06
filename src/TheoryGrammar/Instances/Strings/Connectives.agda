{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- LambekD's connectives at strings: ε, ⊗, literal, and the residual ⟜. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Strings.Connectives (Char : Type₀) where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.List
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import Cubical.Foundations.Isomorphism

open import TheoryGrammar.Instances.Strings.Base Char public

ε' : Gr
ε' = ⊗ˢ nilop (λ ())

_⊗'_ : Gr → Gr → Gr
A ⊗' B = ⊗ˢ appop (λ b → if b then A else B)

literal : Char → Gr
literal c = ⌈ c ∷ [] ⌉

infixr 20 _⊗'_

-- The level coercion the constant former `⌜_⌝` of a description carries
-- (`Inductive.⟦ ⌜ B ⌝ ⟧c A w = Lift _ (B w)`).  Pure bookkeeping, and
-- both directions are maps of the calculus, so a description's constants
-- are discharged by composition rather than by `lift`/`lower` surgery.
Liftg : Gr → Gr
Liftg A w = Lift ℓ-zero (A w)

liftg : {A : Gr} → A ⊢ Liftg A
liftg _ = lift

lowerg : {A : Gr} → Liftg A ⊢ A
lowerg _ = lower

-- intro and elim for ⊗
⊗-mk : {A B : Gr} {u v w : String} → Split3 u v w → A u → B v → (A ⊗' B) w
⊗-mk {u = u} {v} s a b = (u , v , s) , λ { true → a ; false → b }

⊗-elim : {A B C : Gr}
       → (∀ {u v w} → A u → B v → Split3 u v w → C w)
       → (A ⊗' B) ⊢ C
⊗-elim f w ((u , v , s) , h) = f (h true) (h false) s

ε-mk : ε' []
ε-mk = tt , λ ()

-- The residual, at slot `false` (the right factor).

focR : Focus strFib appop false
focR .SplitAt v  = Σ[ u ∈ String ] Σ[ w ∈ String ] Split3 u v w
focR .whole (u , w , _) = w
focR .Rest       = Unit
focR .restOf _   = true
focR .restSlot (u , w , _) _ = u

module R = FocusNotation focR

_⟜'_ : Gr → Gr → Gr
C ⟜' A = R.⊸ᶠ (λ b → if b then A else C) C

-- ⟜-app.  LambekD's has `Eq.transport B (Eq.sym w≡w'++w'')`; this has
-- nothing, because the splitting already names the whole.
⟜-app : {A C : Gr} → (A ⊗' (C ⟜' A)) ⊢ C
⟜-app w ((u , v , s) , h) = h false (u , w , s) (λ _ → h true)

-- THE ADJUNCTION, as LambekD states it.
module _ {A B C : Gr} where

  ⟜-intro : (A ⊗' B) ⊢ C → B ⊢ (C ⟜' A)
  ⟜-intro f v bv (u , w , s) g = f w (⊗-mk s (g tt) bv)

  ⟜-intro⁻ : B ⊢ (C ⟜' A) → (A ⊗' B) ⊢ C
  ⟜-intro⁻ h = ⊗-elim λ a bv s → h _ bv (_ , _ , s) (λ _ → a)

  -- β is definitional (Unit has η, so `λ _ → g tt` IS `g`)
  ⟜-β : (h : B ⊢ (C ⟜' A)) → ⟜-intro (⟜-intro⁻ h) ≡ h
  ⟜-β h = refl

  -- η needs funExt over the ARITY, because Bool has no η.  This is the
  -- one cost of encoding a binary operation as a Bool-indexed family.
  ⟜-η : (f : (A ⊗' B) ⊢ C) → ⟜-intro⁻ (⟜-intro f) ≡ f
  ⟜-η f = funExt λ w → funExt λ { ((u , v , s) , h) →
    cong (λ k → f w ((u , v , s) , k)) (funExt λ { true → refl ; false → refl }) }

  ⟜UMP : Iso ((A ⊗' B) ⊢ C) (B ⊢ (C ⟜' A))
  ⟜UMP .Iso.fun = ⟜-intro
  ⟜UMP .Iso.inv = ⟜-intro⁻
  ⟜UMP .Iso.sec = ⟜-β
  ⟜UMP .Iso.ret = ⟜-η
