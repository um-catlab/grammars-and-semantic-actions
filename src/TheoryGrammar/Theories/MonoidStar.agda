{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The star, generic in a monoid `Fibered`. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Theories.MonoidStar where

open import Cubical.Data.Bool using (Bool; true; false; if_then_else_)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded
open import TheoryGrammar.RulesFib
open import TheoryGrammar.Theories.Monoid

-- Levels are pinned at ℓ-zero: that is what every monoid instance in
-- this tree uses, and leaving them open costs a `ℓ-max ℓP ℓA` in the
-- type of `ε'` for no gain.
module MonStar (GS : GradedFib monoidSig ℓ-zero ℓ-zero) where

  open Guard GS ℓ-zero Unit (λ _ → tt) public
  -- `RulesF` rather than bare `FibNotation`: it re-exports the same
  -- connectives PLUS the combinators (`⊕ᴰ-I`, `⊗ˢ-map`, `liftg`, `idg`,
  -- `_∘g_`), which is what lets `nil*`/`cons*` below be terms.
  open RulesF (GS .fib) public

  Gr : Type₁
  Gr = TheoryTy ℓ-zero tt

  -- the unit and the product, generic in the `Fibered`
  ε' : Gr
  ε' = ⊗ˢ nilop (λ ())

  _⊗'_ : Gr → Gr → Gr
  A ⊗' B = ⊗ˢ appop (λ b → if b then A else B)

  infixr 20 _⊗'_

  -- The star description.

  starSlot : Gr → Bool → Functor tt
  starSlot A true  = ⌜ A ⌝
  starSlot A false = Var tt

  starAlt : Gr → Bool → Functor tt
  starAlt A true  = ⌜ ε' ⌝
  starAlt A false = ⊗e appop (starSlot A)

  starF : Gr → Unit → Functor tt
  starF A _ = ⊕e Bool (starAlt A)

  -- THE HYPOTHESIS. "The body is a proper resource" -- generically what
  -- non-nullability says.
  ProperBody : Gr → Type₀
  ProperBody A = (m : GS .fib .carrier tt) (sp : GS .fib .Split appop m)
               → A (GS .fib .parts appop m sp true)
               → GS .Proper appop m sp false

  starGuarded : (A : Gr) → ProperBody A → (x : Unit) → Guarded (starF A x)
  starGuarded A pb tt = <⊕e Bool (starAlt A) alt
    where
      go : (m : GS .fib .carrier tt) (sp : GS .fib .Split appop m)
           (sh : (a : Bool) → Sh (starSlot A a) (GS .fib .parts appop m sp a))
           (a : Bool) (p : Pos (starSlot A a) _ (sh a))
         → degIx (nx (starSlot A a) _ (sh a) p) < GS .deg tt m
      go m sp sh true ()
      go m sp sh false p =
        slotProper appop m sp false (≤Var tt)
                   (pb m sp (lower (sh true))) (sh false) p

      alt : (b : Bool) → Guarded (starAlt A b)
      alt true  = <⌜⌝ ε'
      alt false = ⊗-guard appop (starSlot A) go

  -- ... and the star itself, with its intro and elim rules.

  KL* : Gr → Gr
  KL* A w = μ (starF A) (tt , w)

  module _ {A : Gr} where

    -- THE FUNCTOR, SPELLED IN THE CONNECTIVES, AT AN ARBITRARY MOTIVE. ⟦
    -- starF A ⟧ M ≅ ε' ⊕ (A ⊗' M) Both directions are composites:
    -- `⊕e`/`⊗e`/`⌜⌝` ARE `⊕ᴰ`/`⊗ˢ`/ `Liftg` definitionally (`Inductive`'s
    -- `⟦_⟧c`), so the only content is picking the alternative and moving
    -- the constant slots across the `Lift`.

    module _ (M : Gr) where

      StarBody : Bool → Gr
      StarBody b = ⟦ starAlt A b ⟧ᴳ (λ _ → M)

      StarSlot : Bool → Gr
      StarSlot a = ⟦ starSlot A a ⟧ᴳ (λ _ → M)

      starOut : ⟦ starF A tt ⟧ᴳ (λ _ → M) ⊢ (ε' ⊕ (A ⊗' M))
      starOut =
        ⊕ᴰ-E {A = StarBody}
          (λ { true  → ⊕-I₁ ∘g lowerg
             ; false → ⊕-I₂
                       ∘g ⊗ˢ-map appop {A = StarSlot}
                                       {B = λ b → if b then A else M}
                                  (λ { true → lowerg ; false → idg }) })

      starIn : (ε' ⊕ (A ⊗' M)) ⊢ ⟦ starF A tt ⟧ᴳ (λ _ → M)
      starIn =
        ⊕-E (⊕ᴰ-I Bool {A = StarBody} true ∘g liftg)
            (⊕ᴰ-I Bool {A = StarBody} false
             ∘g ⊗ˢ-map appop {A = λ b → if b then A else M}
                             {B = StarSlot}
                        (λ { true → liftg ; false → idg }))

    -- ... AND THE FIXED POINT'S FOUR MAPS, AS COROLLARIES.

    roll* : (ε' ⊕ (A ⊗' KL* A)) ⊢ KL* A
    roll* = rollg (starF A) tt ∘g starIn (KL* A)

    unroll* : KL* A ⊢ (ε' ⊕ (A ⊗' KL* A))
    unroll* = starOut (KL* A) ∘g unrollg (starF A) tt

    nil* : ε' ⊢ KL* A
    nil* = roll* ∘g ⊕-I₁

    cons* : (A ⊗' KL* A) ⊢ KL* A
    cons* = roll* ∘g ⊕-I₂
