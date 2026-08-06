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
open import TheoryGrammar.Enumerable
open import TheoryGrammar.Decidable.Rule

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

-- ==================================================================
-- CONSTRUCTOR 3 for the tensor decision rule: decide by
-- DIFFERENTIATING.
--
-- `Decidable/Rule.agda` names three ways to establish `⊗-EM`, of which
-- two were built.  This is the third, and it is the one that does no
-- search: at `c ∷ x` the law offers exactly two cases -- the `c` went
-- left or it went right -- where the enumerating decider builds and
-- scans all `length w + 1` cuts.  Those cuts ARE the unfolding of this
-- two-case law along the word.
--
-- The recursion is structural on the string, but the SLOT FAMILY moves:
-- the recursive call is at `δA`, not `A`.  That is why the decider is
-- indexed by decisions at every string rather than at the parts of one
-- splitting -- and why the enumerating route, which cannot re-index,
-- has to pay for the list.
-- ==================================================================

SlotDec : ((a : MonAr appop) → TheoryTy ℓA tt) → Type _
SlotDec A = (a : MonAr appop) (w : String) → A a w ⊎ No (A a w)

private
  -- decisions transport to the differentiated family for free: `δ` is
  -- precomposition, so a decision at `c ∷ w` IS a decision of `δ` at `w`
  dδ : (c : Char) (A : (a : MonAr appop) → TheoryTy ℓA tt)
     → SlotDec A → SlotDec (Derivᶜ.δA c A)
  dδ c A d true  w = d true (c ∷ w)
  dδ c A d false w = d false w

  -- refutation travels through the Iso the same way evidence does
  killδ : (c : Char) (x : String) (A : (a : MonAr appop) → TheoryTy ℓA tt)
        → No (A true [] × A false (c ∷ x))
        → No (⊗ˢ appop (Derivᶜ.δA c A) x)
        → No (⊗ˢ appop A (c ∷ x))
  killδ c x A n m z with Derivᶜ.δ⊗-fun c A x z
  ... | inl pq = n pq
  ... | inr t  = m t

  goCons : (c : Char) (x : String) (A : (a : MonAr appop) → TheoryTy ℓA tt)
         → (A true [] ⊎ No (A true []))
         → (A false (c ∷ x) ⊎ No (A false (c ∷ x)))
         → (⊗ˢ appop (Derivᶜ.δA c A) x ⊎ No (⊗ˢ appop (Derivᶜ.δA c A) x))
         → ⊗ˢ appop A (c ∷ x) ⊎ No (⊗ˢ appop A (c ∷ x))
  goCons c x A (inl p) (inl q) _       = inl (Derivᶜ.δ⊗-inv c A x (inl (p , q)))
  goCons c x A _       _       (inl t) = inl (Derivᶜ.δ⊗-inv c A x (inr t))
  goCons c x A (inr n) _       (inr m) = inr (killδ c x A (λ pq → n (pq .fst)) m)
  goCons c x A _       (inr n) (inr m) = inr (killδ c x A (λ pq → n (pq .snd)) m)

-- THE DECIDER.  Two clauses, and neither builds a list.
decδ⊗ : (A : (a : MonAr appop) → TheoryTy ℓA tt) → SlotDec A
      → (m : String) → ⊗ˢ appop A m ⊎ No (⊗ˢ appop A m)
decδ⊗ A d []      = goNil (d true []) (d false [])
  where
    goNil : (A true [] ⊎ No (A true [])) → (A false [] ⊎ No (A false []))
          → ⊗ˢ appop A [] ⊎ No (⊗ˢ appop A [])
    goNil (inl p) (inl q) = inl (([] , [] , nil) , λ { true → p ; false → q })
    goNil (inr n) _       = inr λ { ((_ , _ , nil) , h) → n (h true) }
    goNil _       (inr n) = inr λ { ((_ , _ , nil) , h) → n (h false) }
decδ⊗ A d (c ∷ x) =
  goCons c x A (d true []) (d false (c ∷ x))
         (decδ⊗ (Derivᶜ.δA c A) (dδ c A d) x)

-- ==================================================================
-- ... and hence the rule, by the third route.
--
-- `Strings/Decidable.agda` already proves this same `DecTensorRule` by
-- enumeration.  That both routes reach the identical interface is the
-- point of stating `⊗-EM` as the conclusion and the witnesses as
-- constructors: a client cannot tell which was used.
-- ==================================================================

-- the slotwise decisions `DecTensorRule` supplies are at the parts of a
-- splitting; `w ++ []` split at `(w , [])` has `w` as its `true` part,
-- ON THE NOSE, so decisions at every string are recovered with no
-- transport.  (Only the split's own index moves, and `Dec⟨_⟩` does not
-- mention it.)
strDecTensorδ : DecTensorRule strFib {ℓA = ℓA}
strDecTensorδ nilop A d []      _ = inl (tt , λ ())
strDecTensorδ nilop A d (c ∷ x) _ = inr λ { (() , _) }
strDecTensorδ appop A d m       _ = decδ⊗ A slot m
  where
    slot : SlotDec A
    slot true  w = d (w ++ [])  (w , [] , splitAll w [])  true
    slot false w = d ([] ++ w)  ([] , w , splitAll [] w)  false
