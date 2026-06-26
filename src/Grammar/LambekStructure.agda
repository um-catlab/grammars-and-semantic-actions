{- `LambekStructure C` — the categorical structure a category needs to
   interpret the dependent Lambek calculus, bundled as a record so that the
   interpretation can be replayed in *any* model (gluing / logical relations
   being a second instance).

   It collects the witnesses recaptured from cubical-categorical-logic and
   scattered through the per-constructor modules:

     * multiplicative (ordered, biclosed): a monoidal structure together with,
       for every object A, the partial tensors `(A ⊗ –)` / `(– ⊗ A)` and their
       right adjoints — the Lambek implications `(– ⟜ A)` / `(A ⊸ –)`;
     * additive (cartesian closed + cocartesian): terminal, initial, binary
       products, binary coproducts, and exponentials.

   `|GRAMMAR|` is the first instance (`|GRAMMAR|-LambekStructure`).  The
   inductive/coinductive (`μ` / `ν`) and modal (`□` / `▷`) structure is provided
   separately — those need the strictly-positive functor *codes* and the suffix
   category, which are not expressible over an arbitrary `C`.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.LambekStructure (Alphabet : hSet ℓ-zero) where

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Monoidal.Base using (MonoidalStr ; MonoidalCategory)
open import Cubical.Categories.Adjoint.UniversalElements using (RightAdjoint)
open import Cubical.Categories.Limits.Terminal.More using (Terminal' ; Initial')
open import Cubical.Categories.Limits.BinProduct.More using (BinProducts ; BinCoProducts)
open import Cubical.Categories.Exponentials.Small using (AllExponentiable)

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Top.Terminal Alphabet
open import Grammar.Bottom.Initial Alphabet
open import Grammar.Product.Binary.AsPrimitive.BinProduct Alphabet
open import Grammar.Sum.Binary.AsPrimitive.BinCoProduct Alphabet
open import Grammar.Function.AsPrimitive.Exponential Alphabet
open import Grammar.LinearFunction.Adjoint Alphabet
open import Term.Category Alphabet

private
  variable
    ℓ ℓC ℓC' : Level

record LambekStructure (C : Category ℓC ℓC') : Type (ℓ-suc (ℓ-max ℓC ℓC')) where
  open Category C
  field
    -- multiplicative: ordered monoidal, biclosed
    monstr   : MonoidalStr C
    fixL     : (A : ob) → Functor C C            -- (A ⊗ –)
    fixR     : (A : ob) → Functor C C            -- (– ⊗ A)
    fixL-ra  : (A : ob) → RightAdjoint (fixL A)  -- right adjoint (– ⟜ A)
    fixR-ra  : (A : ob) → RightAdjoint (fixR A)  -- right adjoint (A ⊸ –)
    -- additive: cartesian closed + cocartesian
    terminal     : Terminal' C
    initial      : Initial' C
    products     : BinProducts C
    coproducts   : BinCoProducts C
    exponentials : AllExponentiable C products

open LambekStructure

-- |GRAMMAR| is a Lambek structure.
|GRAMMAR|-LambekStructure : (ℓ : Level) → LambekStructure (|GRAMMAR| ℓ)
|GRAMMAR|-LambekStructure ℓ .monstr       = MonoidalCategory.monstr (GRAMMAR ℓ)
|GRAMMAR|-LambekStructure ℓ .fixL A       = A⊗- ℓ A
|GRAMMAR|-LambekStructure ℓ .fixR A       = -⊗A ℓ A
|GRAMMAR|-LambekStructure ℓ .fixL-ra A    = RightAdjoint-⟜ ℓ A
|GRAMMAR|-LambekStructure ℓ .fixR-ra A    = RightAdjoint-⊸ ℓ A
|GRAMMAR|-LambekStructure ℓ .terminal     = |GRAMMAR|-Terminal'
|GRAMMAR|-LambekStructure ℓ .initial      = |GRAMMAR|-Initial'
|GRAMMAR|-LambekStructure ℓ .products     = |GRAMMAR|-BinProducts
|GRAMMAR|-LambekStructure ℓ .coproducts   = |GRAMMAR|-BinCoProducts
|GRAMMAR|-LambekStructure ℓ .exponentials = |GRAMMAR|-AllExponentiable
