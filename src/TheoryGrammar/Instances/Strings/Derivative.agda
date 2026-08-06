{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The Brzozowski derivative, as an instance of the generic one.

   Two things are being checked here.

   (1) `act` is `c ∷ _` DEFINITIONALLY.  It is assembled as "appop with
   the left slot pinned to `c`", so it unfolds to `(c ∷ []) ++ x`, and
   `act-β` is `refl`.  Nothing in `Derivative.agda` mentions strings;
   the string-ness is entirely in the `Assembly`.

   (2) The tensor law -- the one thing the generic layer cannot prove --
   is a PATTERN MATCH.  `Split3` is indexed by its output, so a
   splitting of `c ∷ x` is inverted by matching its two constructors:
   `nil` says the left factor is empty, `cons` says the left factor
   absorbed the `c`.  That is Levi's lemma for free monoids, and it is
   four lines.  The `split++` inversion lemma the old
   `Grammar/Derivative/String.agda` needed does not appear. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Strings.Derivative (Char : Type₀) where

open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.List

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.CanonicalFocus
open import TheoryGrammar.Derivative

open import TheoryGrammar.Instances.Strings.Base Char public

private variable ℓA : Level

-- Pin the LEFT slot of `appop`; the focus is the right slot, which is
-- the remainder being differentiated.
consAs : Assembly strFib appop false
consAs .Rest       = Unit
consAs .restOf _   = true
consAs .tuple x f a = if a then f tt else x

module Derivᶜ (c : Char) where

  open ActOf strFib strPoint appop false consAs (λ _ → c ∷ []) public

  -- (1) the action is `c ∷ _` on the nose
  act-β : (x : String) → act x ≡ (c ∷ x)
  act-β x = refl

  -- ================================================================
  -- (2) THE TENSOR LAW.
  --
  --   δ (A ⊗ B)  ≅  (A ε × δ B)  ⊕  (δ A ⊗ B)
  --
  -- the classical Brzozowski rule, with the left disjunct saying the
  -- `c` went to the right factor (so the left factor is empty and
  -- contributes its nullability) and the right disjunct saying the left
  -- factor absorbed it.
  -- ================================================================
  module _ (A : (a : monoidSig .arities appop) → TheoryTy ℓA tt) where

    -- the derivative of the left factor, in the same slot shape
    δA : (a : monoidSig .arities appop) → TheoryTy ℓA tt
    δA a = if a then δ (A true) else A false

    δ⊗ : TheoryTy ℓA tt
    δ⊗ x = (A true [] × δ (A false) x) ⊎ ⊗ˢ appop δA x

    -- The inversion.  `nil` and `cons` are the ONLY ways a splitting of
    -- `c ∷ x` can arise, and Agda sees that because `Split3` is indexed
    -- by its output.
    δ⊗-fun : δ (⊗ˢ appop A) ⊢ δ⊗
    δ⊗-fun x ((.[]     , .(c ∷ x) , nil)     , h) = inl (h true , h false)
    δ⊗-fun x ((.(c ∷ _) , v       , cons s') , h) =
      inr ((_ , v , s') , λ { true → h true ; false → h false })

    δ⊗-inv : δ⊗ ⊢ δ (⊗ˢ appop A)
    δ⊗-inv x (inl (p , q)) =
      ([] , c ∷ x , nil) , λ { true → p ; false → q }
    δ⊗-inv x (inr ((u' , v , s') , h)) =
      (c ∷ u' , v , cons s') , λ { true → h true ; false → h false }

    δ⊗-Iso : DerivTensor strFib strPoint appop false consAs (λ _ → c ∷ [])
                         A δ⊗
    δ⊗-Iso x .Iso.fun = δ⊗-fun x
    δ⊗-Iso x .Iso.inv = δ⊗-inv x
    δ⊗-Iso x .Iso.sec (inl (p , q)) = refl
    δ⊗-Iso x .Iso.sec (inr ((u' , v , s') , h)) =
      cong inr (ΣPathP (refl , funExt λ { true → refl ; false → refl }))
    δ⊗-Iso x .Iso.ret ((.[]      , .(c ∷ x) , nil)     , h) =
      ΣPathP (refl , funExt λ { true → refl ; false → refl })
    δ⊗-Iso x .Iso.ret ((.(c ∷ _) , v        , cons s') , h) =
      ΣPathP (refl , funExt λ { true → refl ; false → refl })
