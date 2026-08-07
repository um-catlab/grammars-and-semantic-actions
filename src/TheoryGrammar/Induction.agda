{-
  The DEPENDENT eliminator of `μ`.

  `Inductive.agda` exports `fold`, whose motive is `Ix → Type` — enough to
  compute *with* a derivation, not enough to prove anything *about* one.
  Uniqueness statements ("this element is the one `readback` produces")
  need a motive that mentions the element, so every such proof was
  spelling the recursion out again locally.

  `indμ` is that eliminator, once, generically.  `fold` is its instance at
  a constant motive (`foldD`), and `fold≡` proves the two agree -- by
  induction, not by `refl`: they differ at the recursive call, so the step
  needs `funExt` over positions.  So this file adds no strength, only the
  missing generality.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Induction where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive

private variable ℓS ℓ ℓ' ℓX ℓP ℓA ℓM ℓV : Level

module Induct {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
              (Fib : Fibered σ ℓX ℓP) (ℓA : Level)
              (X : Type ℓV) (xs : X → S) where

  open Ind Fib ℓA X xs public

  module _ {F : (x : X) → Functor (xs x)} where

    -- the eliminator: the motive may mention the element
    indμ : (M : (i : Ix) → μ F i → Type ℓM)
         → ((x : X) (m : Fib .carrier (xs x)) (sh : Sh (F x) m)
            (f : (p : Pos (F x) m sh) → μ F (nx (F x) m sh p))
            → ((p : Pos (F x) m sh) → M _ (f p))
            → M (x , m) (sup sh f))
         → (i : Ix) (e : μ F i) → M i e
    indμ M α (x , m) (sup sh f) = α x m sh f (λ p → indμ M α _ (f p))

    -- `fold` is `indμ` at a motive that ignores the element ...
    foldD : (M : Ix → Type ℓM)
          → ((x : X) (m : Fib .carrier (xs x)) (sh : Sh (F x) m)
             → ((p : Pos (F x) m sh) → M (nx (F x) m sh p)) → M (x , m))
          → (i : Ix) → μ F i → M i
    foldD M α = indμ (λ i _ → M i) (λ x m sh _ rc → α x m sh rc)

    -- ... and it is the same function.  NOT `refl`: the two agree only
    -- after their recursive calls do, so this is an induction whose step
    -- lifts pointwise agreement with `funExt`.
    fold≡ : (M : Ix → Type ℓM)
            (α : (x : X) (m : Fib .carrier (xs x)) (sh : Sh (F x) m)
               → ((p : Pos (F x) m sh) → M (nx (F x) m sh p)) → M (x , m))
            (i : Ix) (e : μ F i)
          → foldD M α i e ≡ fold M α i e
    fold≡ M α =
      indμ (λ i e → foldD M α i e ≡ fold M α i e)
           (λ x m sh f rc → cong (α x m sh) (funExt rc))

    -- the η-rule the dependent eliminator buys: any two maps out of `μ`
    -- agreeing on `sup` agree everywhere
    indμ-unique : (M : (i : Ix) → μ F i → Type ℓM)
                  (g h : (i : Ix) (e : μ F i) → M i e)
                → ((x : X) (m : Fib .carrier (xs x)) (sh : Sh (F x) m)
                   (f : (p : Pos (F x) m sh) → μ F (nx (F x) m sh p))
                   → ((p : Pos (F x) m sh) → g _ (f p) ≡ h _ (f p))
                   → g (x , m) (sup sh f) ≡ h (x , m) (sup sh f))
                → (i : Ix) (e : μ F i) → g i e ≡ h i e
    indμ-unique M g h step =
      indμ (λ i e → g i e ≡ h i e) (λ x m sh f rc → step x m sh f rc)
