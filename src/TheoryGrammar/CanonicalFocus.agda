{-
  THE RESIDUAL EVERY SUBSTRATE ALREADY HAS.

  A promodel owns one family of splittings for free: `split o m⃗`, the
  canonical splitting of a tuple's own composite.  Fixing a slot `i` and
  NAMING the complement (`Assembly`) turns those into a `Focus`, so

      (A ⊸ B) x  =  (rest) → A(rest) → B (op o (tuple x rest)).

  NO HYPOTHESIS: `focus`, `plug` (⊸-elim at a chosen rest-tuple).  ONE
  HYPOTHESIS -- `restJ`/`restJ-pt`, the rest argument is singleton-
  inductive at `(a⃗ , pt)`, i.e. holding one NAMES its own tuple --
  gives `unplug`, `⊸-β` (refl), `⊸-η` (funExt, the cost of equating two
  functions) and the `Iso`.  Freeness, `unsplit` and `Fib .Split` itself
  are UNUSED, so the laws hold over a quotient substrate as well.

  NOT proved: that this focus computes the residual of `⊗ˢ`.  Stated
  precisely, with its refuted hypothesis, as `CONJECTURE` below.
-}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.CanonicalFocus where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered

private variable ℓS ℓ ℓ' ℓX ℓP ℓA ℓB : Level

-- ==================================================================
-- SINGLETON INDUCTION IN Eq-WORLD.
--
-- `Eq.J` eliminates the RIGHT endpoint of `_Eq.≡_`; a representable,
-- `⌈ a ⌉ y = y Eq.≡ a`, varies the LEFT one.  Symmetrising costs one
-- `sym-invol` -- and, the whole point, costs it in Eq-world, so
-- `singJ M m a Eq.refl` still reduces to `m` DEFINITIONALLY
-- (`singJ-refl` is `refl`).  A cubical `subst` here would not reduce,
-- and every `refl` test downstream would go inert.
-- ==================================================================

singJ : ∀ {ℓM} {X : Type ℓ} {a : X} (M : (y : X) → y Eq.≡ a → Type ℓM)
      → M a Eq.refl → (y : X) (e : y Eq.≡ a) → M y e
singJ M m y e =
  Eq.transport (M y) (Eq.sym-invol e) (Eq.J (λ y' p → M y' (Eq.sym p)) m (Eq.sym e))

singJ-refl : ∀ {ℓM} {X : Type ℓ} {a : X} (M : (y : X) → y Eq.≡ a → Type ℓM)
             (m : M a Eq.refl) → singJ M m a Eq.refl ≡ m
singJ-refl M m = refl

-- The only datum: how to reassemble a full tuple from the focused
-- element and a naming of the other slots.
record Assembly {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
                (Fib : Fibered σ ℓX ℓP) (o : σ .ops) (i : σ .arities o)
  : Type (ℓ-max ℓS (ℓ-max ℓ (ℓ-max (ℓ-suc ℓ') ℓX))) where
  field
    Rest   : Type ℓ'
    restOf : Rest → σ .arities o
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

  -- ================================================================
  -- ⊸-INTRO AND THE TWO ROUND TRIPS.
  --
  -- THE HYPOTHESIS, in full: the rest argument is singleton-inductive
  -- at `(a⃗ , pt)`.  Reading it as an eliminator, "to prove something of
  -- an arbitrary rest-bundle it suffices to prove it of `(a⃗ , pt)`" --
  -- i.e. holding a rest argument NAMES the tuple it was taken at, which
  -- is what "the other slots are representable" means.  Nothing weaker
  -- can do: `unplug` must move `B` across `tuple x f` vs `tuple x a⃗`.
  --
  -- Note the shape: the identification is of the tuple AS A WHOLE.  A
  -- slotwise hypothesis would have to be glued by function
  -- extensionality for `Eq`, which does not reduce, and the transport
  -- in `unplug` would then be inert.  When `Rest` is a unit type the
  -- whole-tuple form is free (η), which is the case `Modes/` is in.
  -- ================================================================

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

-- ==================================================================
-- CONJECTURE (not proved; stated so it can be attacked or refuted).
--
-- `Canon.focus` never mentions `Fib .Split`, so nothing above compares
-- `⊸ᶠ` with the residual of the substrate's OWN tensor `⊗ˢ`.  That
-- comparison is the claim
--
--     (A i ⊢ ⊸ᶠ A B)  ≅  (⊗ˢ o A ⊢ B),
--
-- and it needs three data this file does not have:
--
--   (1) cover   : (a : arities o) → (a Eq.≡ i) ⊎ (Σ[ r ] restOf r Eq.≡ a)
--                 -- i and restOf between them reach every slot;
--   (2) unsplit : op o (parts o m sp) Eq.≡ m       (as in Representable);
--   (3) gen     : every `sp : Split o m` is `split o (parts o m sp)`,
--                 modulo (2) -- "the splittings are generated by split".
--
-- MEASUREMENT, and the reason the conjecture is stated rather than
-- proved: (2) is FALSE for the quotient substrates.  For `Interleave`,
-- `op mul = _++_` while `Split mul` is `Ilv`, which is strictly bigger
-- than the graph of `++`; `Modes/Laws.agda`'s `no-unsplit` exhibits a
-- splitting of `y ∷ x ∷ []` whose parts concatenate to `x ∷ y ∷ []`.
-- So the conjecture is not merely open there, its hypothesis fails --
-- while `Residual`'s β and η hold at that same substrate, being proved
-- without it.  The two claims are genuinely independent.
-- ==================================================================
