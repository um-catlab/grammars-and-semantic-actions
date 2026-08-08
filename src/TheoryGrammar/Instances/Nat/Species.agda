{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- ONE GENERATING-FUNCTION IDENTITY, DONE INTERNALLY: CATALAN. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Nat.Species where

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
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded

open import TheoryGrammar.Instances.Nat.Graded public

-- THE DESCRIPTION.  `⊗e` is binary (its arity is `Bool`), so the
-- four-factor body  x ⊗ D ⊗ x ⊗ D  is three nested `⊗e`s, read
-- right-associated exactly as `_⊗'_` is.

-- x ⊗ D
dyck₄ : Bool → Functor tt
dyck₄ true  = ⌜ x ⌝
dyck₄ false = Var tt

-- D ⊗ (x ⊗ D)
dyck₃ : Bool → Functor tt
dyck₃ true  = Var tt
dyck₃ false = ⊗e appop dyck₄

-- x ⊗ (D ⊗ (x ⊗ D))
dyck₂ : Bool → Functor tt
dyck₂ true  = ⌜ x ⌝
dyck₂ false = ⊗e appop dyck₃

dyckAlt : Bool → Functor tt
dyckAlt true  = ⌜ ε' ⌝
dyckAlt false = ⊗e appop dyck₂

dyckF : Unit → Functor tt
dyckF _ = ⊕e Bool dyckAlt

-- GUARDEDNESS. The recursive slots are `dyck₃ true` (the first D) and
-- `dyck₄ false` (the second D); both live inside the right factor of a
-- product whose LEFT factor is the generator `x`, and `x` at degree i
-- forces i = 1.

dyckGuarded : (u : Unit) → Guarded (dyckF u)
dyckGuarded tt = <⊕e Bool dyckAlt alt
  where
    ≤₄ : Guarded≤ (⊗e appop dyck₄)
    ≤₄ = ≤⊗e appop dyck₄ (λ { true → ≤⌜⌝ x ; false → ≤Var tt })

    ≤₃ : Guarded≤ (⊗e appop dyck₃)
    ≤₃ = ≤⊗e appop dyck₃ (λ { true → ≤Var tt ; false → ≤₄ })

    go : (n : ℕ) (sp : MonSplit appop n)
         (sh : (a : Bool) → Sh (dyck₂ a) (MonParts appop n sp a))
         (a : Bool) (p : Pos (dyck₂ a) _ (sh a))
       → degIx (nx (dyck₂ a) _ (sh a) p) < n
    go n sp sh true ()
    go n (i , j , a) sh false p =
      slotProper appop n (i , j , a) false ≤₃ (degNT (lower (sh true))) (sh false) p

    alt : (b : Bool) → Guarded (dyckAlt b)
    alt true  = <⌜⌝ ε'
    alt false = ⊗-guard appop dyck₂ go

-- THE GRAMMAR, and the fixpoint primitives.

D : Gr
D n = μ dyckF (tt , n)

-- `rollg` / `unrollg` USED TO BE DEFINED HERE, with a comment saying they
-- were generic and belonged upstream.

-- The description's body, spelled in the connectives.

Body : Gr
Body n = ⟦ dyckF tt ⟧c (μ dyckF) n

BodyAlt : Bool → Gr
BodyAlt b n = ⟦ dyckAlt b ⟧c (μ dyckF) n

Body₂ : Bool → Gr
Body₂ a n = ⟦ dyck₂ a ⟧c (μ dyckF) n

Body₃ : Bool → Gr
Body₃ a n = ⟦ dyck₃ a ⟧c (μ dyckF) n

Body₄ : Bool → Gr
Body₄ a n = ⟦ dyck₄ a ⟧c (μ dyckF) n

-- THE SURFACE FORM.  `_⊗'_` is infixr 20, so this reads
-- `x ⊗ (D ⊗ (x ⊗ D))` -- the same association as the description.
DyckBody : Gr
DyckBody = ε' ⊕ (x ⊗' D ⊗' x ⊗' D)

-- Crossing between the surface form and the description, in phase 2.

to₄ : (x ⊗' D) ⊢ ⊗ˢ appop Body₄
to₄ = ⊗ˢ-map appop {A = λ b → if b then x else D} {B = Body₄}
        (λ { true → liftg ; false → idg })

to₃ : (D ⊗' x ⊗' D) ⊢ ⊗ˢ appop Body₃
to₃ = ⊗ˢ-map appop {A = λ b → if b then D else (x ⊗' D)} {B = Body₃}
        (λ { true → idg ; false → to₄ })

to₂ : (x ⊗' D ⊗' x ⊗' D) ⊢ ⊗ˢ appop Body₂
to₂ = ⊗ˢ-map appop {A = λ b → if b then x else (D ⊗' x ⊗' D)} {B = Body₂}
        (λ { true → liftg ; false → to₃ })

toDesc : DyckBody ⊢ Body
toDesc = ⊕-E (⊕ᴰ-in {A = BodyAlt} true  ∘g liftg)
             (⊕ᴰ-in {A = BodyAlt} false ∘g to₂)

from₄ : ⊗ˢ appop Body₄ ⊢ (x ⊗' D)
from₄ = ⊗ˢ-map appop {A = Body₄} {B = λ b → if b then x else D}
          (λ { true → lowerg ; false → idg })

from₃ : ⊗ˢ appop Body₃ ⊢ (D ⊗' x ⊗' D)
from₃ = ⊗ˢ-map appop {A = Body₃} {B = λ b → if b then D else (x ⊗' D)}
          (λ { true → idg ; false → from₄ })

from₂ : ⊗ˢ appop Body₂ ⊢ (x ⊗' D ⊗' x ⊗' D)
from₂ = ⊗ˢ-map appop {A = Body₂} {B = λ b → if b then x else (D ⊗' x ⊗' D)}
          (λ { true → lowerg ; false → from₃ })

fromDesc : Body ⊢ DyckBody
fromDesc = ⊕ᴰ-elim {A = BodyAlt} (λ { true  → ⊕-I₁ ∘g lowerg
                                    ; false → ⊕-I₂ ∘g from₂ })

-- THE CATALAN RECURRENCE, as two terms. D ≅ 1 ⊕ x·D·x·D i.e.

dyck-roll : DyckBody ⊢ D
dyck-roll = rollg dyckF tt ∘g toDesc

dyck-unroll : D ⊢ DyckBody
dyck-unroll = fromDesc ∘g unrollg dyckF tt

-- The three constructors, as corollaries, so the grammar can be USED
-- without ever mentioning its description again.

dyck-nil : ε' ⊢ D
dyck-nil = dyck-roll ∘g ⊕-I₁

dyck-node : (x ⊗' D ⊗' x ⊗' D) ⊢ D
dyck-node = dyck-roll ∘g ⊕-I₂
