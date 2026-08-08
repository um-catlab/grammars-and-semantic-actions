{- THE RESIDUAL EVERY POINTED SUBSTRATE ALREADY HAS. -}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.CanonicalFocus where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered

private variable ℓS ℓ ℓ' ℓX ℓP ℓA ℓB : Level

-- SINGLETON INDUCTION IN Eq-WORLD. `Eq.J` eliminates the RIGHT endpoint of
-- `_Eq.≡_`; a representable, `⌈ a ⌉ y = y Eq.≡ a`, varies the LEFT one.

singJ : ∀ {ℓM} {X : Type ℓ} {a : X} (M : (y : X) → y Eq.≡ a → Type ℓM)
      → M a Eq.refl → (y : X) (e : y Eq.≡ a) → M y e
singJ M m y e =
  Eq.transport (M y) (Eq.sym-invol e) (Eq.J (λ y' p → M y' (Eq.sym p)) m (Eq.sym e))

singJ-refl : ∀ {ℓM} {X : Type ℓ} {a : X} (M : (y : X) → y Eq.≡ a → Type ℓM)
             (m : M a Eq.refl) → singJ M m a Eq.refl ≡ m
singJ-refl M m = refl

-- An `Assembly Fib o i` denotes a NAMING of the slots other than `i`,
-- together with the way a full argument tuple is rebuilt from the focused
-- element and a filling of those.
record Assembly {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
                (Fib : Fibered σ ℓX ℓP) (o : σ .ops) (i : σ .arities o)
  : Type (ℓ-max ℓS (ℓ-max ℓ (ℓ-max (ℓ-suc ℓ') ℓX))) where
  field
    -- an index set for "the other slots" -- not required to be the
    -- complement of `i`, nor even to miss it
    Rest   : Type ℓ'
    -- ... naming which slot each of them is
    restOf : Rest → σ .arities o
    -- ... and how a focused element plus a filling of the rest make a
    -- tuple.  Nothing forces this to agree with `restOf` at `i`; the
    -- laws that need it take it as `restJ` instead.
    tuple  : Fib .carrier (σ .sortOf o i)
           → ((r : Rest) → Fib .carrier (σ .sortOf o (restOf r)))
           → (a : σ .arities o) → Fib .carrier (σ .sortOf o a)

open Assembly public

module Canon {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
             (Fib : Fibered σ ℓX (ℓ-max ℓ' ℓX)) (P : LaxPoint Fib)
             (o : σ .ops) (i : σ .arities o) (As : Assembly Fib o i) where

  open FibNotation Fib

  -- the rest-tuples, and the argument the residual takes at them
  Tup : Type (ℓ-max ℓ' ℓX)
  Tup = (r : As .Rest) → Fib .carrier (σ .sortOf o (As .restOf r))

  Slots : ((a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a)) → Tup → Type (ℓ-max ℓ' ℓA)
  Slots A f = (r : As .Rest) → A (As .restOf r) (f r)

  focus : Focus Fib o i
  focus .SplitAt _  = Tup
  focus .whole {x} f = P .op o (As .tuple x f)
  focus .Rest       = As .Rest
  focus .restOf     = As .restOf
  focus .restSlot f = f

  open FocusNotation focus public

  -- ⊸-ELIM at a chosen rest-tuple: plug the hole.  No hypotheses -- the
  -- focus IS the algebra, so applying the residual is application of the
  -- operation.
  plug : {A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a)}
         {B : TheoryTy ℓB (σ .resultSort o)}
         (a⃗ : Tup) → Slots A a⃗
       → ⊸ᶠ A B ⊢ (λ x → B (P .op o (As .tuple x a⃗)))
  plug a⃗ pt _ h = h a⃗ pt

  -- ⊸-INTRO AND THE TWO ROUND TRIPS. THE HYPOTHESIS, in full: the rest
  -- argument is singleton-inductive at `(a⃗ , pt)`.

  module Residual
    {A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a)}
    (a⃗ : Tup) (pt : Slots A a⃗)
    (restJ : ∀ {ℓM} (M : (f : Tup) → Slots A f → Type ℓM)
           → M a⃗ pt → (f : Tup) (q : Slots A f) → M f q)
    (restJ-pt : ∀ {ℓM} (M : (f : Tup) → Slots A f → Type ℓM) (m : M a⃗ pt)
              → restJ M m a⃗ pt ≡ m)
    where

    -- "B, with the hole already filled by a⃗" -- what `plug` lands in
    Shift : TheoryTy ℓB (σ .resultSort o) → TheoryTy ℓB (σ .sortOf o i)
    Shift B x = B (P .op o (As .tuple x a⃗))

    module _ {B : TheoryTy ℓB (σ .resultSort o)} where

      -- `plug` at this rest-tuple, named for symmetry with its inverse
      plug-at : ⊸ᶠ A B ⊢ Shift B
      plug-at = plug a⃗ pt

      -- No transport is written here: the hypothesis IS the eliminator,
      -- so abstracting the hole is one appeal to it.
      unplug : Shift B ⊢ ⊸ᶠ A B
      unplug x b = restJ (λ f _ → B (P .op o (As .tuple x f))) b

      ⊸-β : (x : Fib .carrier (σ .sortOf o i)) (b : Shift B x)
          → plug-at x (unplug x b) ≡ b
      ⊸-β x b = restJ-pt _ b

      ⊸-η : (x : Fib .carrier (σ .sortOf o i)) (h : ⊸ᶠ A B x)
          → unplug x (plug-at x h) ≡ h
      ⊸-η x h = funExt λ f → funExt λ q →
        restJ (λ f' q' → unplug x (plug-at x h) f' q' ≡ h f' q')
              (restJ-pt _ (h a⃗ pt)) f q

      ⊸-UP : (x : Fib .carrier (σ .sortOf o i)) → Iso (⊸ᶠ A B x) (Shift B x)
      ⊸-UP x .Iso.fun = plug-at x
      ⊸-UP x .Iso.inv = unplug x
      ⊸-UP x .Iso.sec = ⊸-β x
      ⊸-UP x .Iso.ret = ⊸-η x

-- CONJECTURE (not proved; stated so it can be attacked or refuted).
