{-
  WHAT ASSOCIATIVITY IS ACTUALLY NEEDED?

  `Fibered` has three fields -- `carrier`, `Split`, `parts` -- and no
  equations.  The one-step divisibility relation

      n ◃₁ m   =   n is the a-th part of some o-splitting of m

  is therefore a bare relation.  `Direct/Divisibility.agda` builds the
  category on its reflexive-transitive CLOSURE, and this file says
  exactly what that closure costs and what would remove it.

  ------------------------------------------------------------------
  THE ANSWER IN ONE LINE.

      NOTHING is needed for the direct-category theorem.
      TRANSITIVITY OF `◃₁` is needed to drop the closure, and it is
      FALSE -- not unproven, false -- for the paradigm instances.

  The direct structure, the degree monotonicity, the well-foundedness of
  proper divisibility: all of `Divisibility.agda` goes through with no
  hypothesis at all, because the closure is a list and `≤` is transitive,
  so `mono` is a fold.  Associativity buys exactly one thing: it lets
  `≼` collapse back to `◃₁` (`collapse` below), i.e. it makes "factor"
  and "immediate factor" the same relation.

  ------------------------------------------------------------------
  WHY IT IS FALSE.

  Take strings with binary concatenation.  `n ◃₁ m` says "n is a prefix
  or a suffix of m".  Then

      "a"  ◃₁ "ab"   and   "ab" ◃₁ "cab"   but not   "a" ◃₁ "cab".

  The closure `≼` is the INFIX relation, strictly larger than `◃₁`, and
  the development already knows this: `Grammar/Later/SuffixOrder.agda`
  and `Grammar/Later/Infix.agda` are two different files for exactly
  these two relations, and `Later/Ordered.agda` is generic in the order
  precisely so that both fit.

  `no-flat` below formalises the failure on the smallest promodel that
  exhibits it -- ℕ with the predecessor splitting, where `◃₁` is "is the
  predecessor of" and the closure is `<`.  One counterexample suffices
  and this one needs no alphabet.

  ------------------------------------------------------------------
  WHAT WOULD IMPLY IT: `SlotComp`.

  Transitivity of `◃₁` says: a slot of a slot is a slot.  Unfolded, given

      sp  : Split o m               with a-th part  p = parts o m sp a
      sp' : Split o' p              with a'-th part q

  we must produce ONE splitting of `m` having `q` as a slot.  That is
  exactly the FLATTENING of a two-level tree into a one-level one, and at
  the level of the signature it is the associativity equation

      o( … , o'( … ) , … )  =  (o ∘ₐ o')( … )

  together with the demand that the composite `o ∘ₐ o'` be an operation
  of the signature and that the composite splitting be one of ITS
  splittings.  `SlotComp` below is that data, stated at the level
  `Fibered` can see it, and `flatten` proves `SlotComp → Flat`.

  ------------------------------------------------------------------
  WHY `Equations.agda` DOES NOT SUPPLY IT.  Three gaps, all real.

  1.  WRONG LAYER.  `Equations.agda` is stated for a `Model` -- it needs
      `op` to define `eval` and `⊗ᶠ` -- and `Fibered` has no `op`.  A
      `LaxPoint` supplies one, but `Fibered.agda` split it off precisely
      so the multiplicative layer would be available to PARTIAL algebras
      (separation logic), where no total `op` exists.

  2.  WRONG DIRECTION.  `eqn→Iso` lifts an equation to an isomorphism of
      CONNECTIVES, `⟪ t ⟫ A ≅ ⟪ t' ⟫ A`.  That is a statement about
      `⊗[ o ]`, which convolves over the OPERATION.  Programs are written
      against `⊗ˢ`, which convolves over the SPLITTINGS, and the bridge
      between them (`Fibered.Bridge`) needs `Honest` -- every splitting
      recomposes to its own whole.  `Bags` is the standing
      counterexample: `Ilv u v w` does not imply `u ++ v ≡ w`.  So even
      with a total point, an associativity equation does not descend to
      the splittings.

  3.  LINEARITY IS NOT THE OBSTACLE.  Associativity IS linear, so it is
      inside `Equations.agda`'s remit; the failure above is not the
      linearity side condition.  It is that a Split-level flattening is
      DATA (which composite splitting?) and an equation is a proposition
      about the operation.  `SlotComp` is the data; nothing weaker is.

  ------------------------------------------------------------------
  RECOMMENDATION.  Do not add associativity to `Fibered`.  The closure
  costs one `≤-trans` and the direct-category theorem is unconditional;
  adding `SlotComp` would exclude strings, which is the wrong trade.  If
  a future development wants `◃₁` itself to be the hom-relation of the
  category -- for a Reedy factorisation, say, where the maps must be
  generated in one step -- `SlotComp` is the hypothesis to ask for, and
  it should be asked for on the side, not put into the record.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Direct.Associativity where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Empty as E using (⊥)
open import Cubical.Relation.Nullary using (¬_)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Direct.Divisibility
open import TheoryGrammar.Direct.Proper using (predSig ; predFib)

private variable ℓS ℓ ℓ' ℓX ℓP : Level

-- ==================================================================
-- PART A.  `Flat`, and what it buys.
-- ==================================================================

module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (Fib : Fibered σ ℓX ℓP) where

  open Div Fib

  -- "a slot of a slot is a slot"
  Flat : Type (ℓ-max ℓS (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓX ℓP))))
  Flat = {n k m : Elt} → n ◃₁ k → k ◃₁ m → n ◃₁ m

  -- THEOREM.  Under `Flat`, the closure collapses: divisibility is
  -- either the identity or a single splitting.  This -- and only this --
  -- is what associativity would buy.
  collapse : Flat → {n m : Elt} → n ≼ m → (n ≡ m) ⊎ (n ◃₁ m)
  collapse fl nil     = inl refl
  collapse fl (s ∷ p) with collapse fl p
  ... | inl e = inr (subst (λ z → _ ◃₁ z) e s)
  ... | inr t = inr (fl s t)

-- ==================================================================
-- PART B.  `SlotComp` -- the data that implies `Flat`.
--
-- Stated single-sorted, so the sort side conditions (`sortOf o a` must
-- be `resultSort o'`) are discharged by `Unit`'s η rather than by a
-- pile of coercions.  Nothing about the phenomenon is single-sorted;
-- the multi-sorted statement is the same with `Eq.≡` guards on sorts.
-- ==================================================================

module _ {σ : SortedSig Unit ℓ ℓ'} (Fib : Fibered σ ℓX ℓP) where

  open Div Fib

  -- the one-step relation on CARRIER elements: the same thing as `◃₁`,
  -- packaged as a Σ so it can be built and destructed without matching
  -- on a green-slime index
  ◃ᶜ : Fib .carrier tt → Fib .carrier tt → Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓX ℓP)))
  ◃ᶜ n m = Σ[ o ∈ σ .ops ] Σ[ sp ∈ Fib .Split o m ] Σ[ a ∈ σ .arities o ]
             (Fib .parts o m sp a Eq.≡ n)

  ◃₁→◃ᶜ : {n m : Elt} → n ◃₁ m → ◃ᶜ (n .snd) (m .snd)
  ◃₁→◃ᶜ (slot o m sp a) = o , sp , a , Eq.refl

  ◃ᶜ→◃₁ : {n m : Fib .carrier tt} → ◃ᶜ n m → (tt , n) ◃₁ (tt , m)
  ◃ᶜ→◃₁ (o , sp , a , Eq.refl) = slot o _ sp a

  -- THE ASSOCIATIVITY, at the only level `Fibered` can state it.
  record SlotComp : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓX ℓP))) where
    field
      -- the composite operation: `o` with `o'` plugged into slot `a`
      _∘[_]_ : (o : σ .ops) → σ .arities o → σ .ops → σ .ops
      -- where the inner slot ends up in the composite's arity
      inner  : (o : σ .ops) (a : σ .arities o) (o' : σ .ops)
             → σ .arities o' → σ .arities (o ∘[ a ] o')
      -- the flattened splitting ...
      flat   : (o : σ .ops) (a : σ .arities o) (o' : σ .ops)
               (m : Fib .carrier tt) (sp : Fib .Split o m)
               (sp' : Fib .Split o' (Fib .parts o m sp a))
             → Fib .Split (o ∘[ a ] o') m
      -- ... has the inner slot's content where it should
      flatEq : (o : σ .ops) (a : σ .arities o) (o' : σ .ops)
               (a' : σ .arities o')
               (m : Fib .carrier tt) (sp : Fib .Split o m)
               (sp' : Fib .Split o' (Fib .parts o m sp a))
             → Fib .parts (o ∘[ a ] o') m (flat o a o' m sp sp') (inner o a o' a')
               Eq.≡ Fib .parts o' (Fib .parts o m sp a) sp' a'

  open SlotComp

  -- THEOREM.  `SlotComp` gives `Flat`.
  flattenᶜ : SlotComp → {n k m : Fib .carrier tt} → ◃ᶜ n k → ◃ᶜ k m → ◃ᶜ n m
  flattenᶜ SC (o' , sp' , a' , e') (o , sp , a , Eq.refl) =
      SC ._∘[_]_ o a o'
    , SC .flat o a o' _ sp sp'
    , SC .inner o a o' a'
    , (SC .flatEq o a o' a' _ sp sp' Eq.∙ e')

  flatten : SlotComp → Flat Fib
  flatten SC s t = ◃ᶜ→◃₁ (flattenᶜ SC (◃₁→◃ᶜ s) (◃₁→◃ᶜ t))

-- ==================================================================
-- PART C.  `Flat` IS FALSE.
--
-- ℕ with the predecessor splitting (`Direct/Proper.agda`'s `predFib`).
-- `0 ◃₁ 1` and `1 ◃₁ 2` but not `0 ◃₁ 2`, because `2` is not the
-- successor of `0`.  The same shape as prefix-then-suffix on strings,
-- with the alphabet removed.
-- ==================================================================

module P = Div predFib

s01 : (tt , 0) P.◃₁ (tt , 1)
s01 = P.slot tt 1 (0 , refl) tt

s12 : (tt , 1) P.◃₁ (tt , 2)
s12 = P.slot tt 2 (1 , refl) tt

-- 0 is not an IMMEDIATE factor of 2 ...
no02 : ¬ ((tt , 0) P.◃₁ (tt , 2))
no02 s with ◃₁→◃ᶜ predFib s
... | (o , (k , p) , a , e) = snotz (injSuc (p ∙ cong suc (Eq.eqToPath e)))

-- ... though it is a factor: the chain is real, and irremovable.
yes02 : (tt , 0) P.≼ (tt , 2)
yes02 = s01 P.∷ s12 P.∷ P.nil

no-flat : ¬ (Flat predFib)
no-flat fl = no02 (fl s01 s12)
