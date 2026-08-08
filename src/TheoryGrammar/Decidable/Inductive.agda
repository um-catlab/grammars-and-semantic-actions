{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  T4.  EVERY GUARDED DESCRIPTION IS DECIDED.

      (i : Ix) → μ F i ⊎ No (μ F i)

  generic in the theory, in the description, and in the grammar.  One
  `löb` over a structural recursion, and the recursion is the whole file.

  ==================================================================
  THE LAYERING.

      Inductive.Dual         the layers exclude          -- no hypotheses
      Inductive.Consistent   μ and μ⁻ exclude            -- + guarded
      HERE                   ... and μ is decided        -- + listed

  Each row depends only on the ones above.  A consumer that wants only
  "an error report cannot lie" depends on `Consistent` and never pays for
  enumeration.

  THREE HYPOTHESES, THREE OWNERS:

      Listed (Split o m), Listed (arities o)     the THEORY      (once)
      GuardedD                                   the DESCRIPTION
      DecDesc: listed indices, decided constants the GRAMMAR

  ==================================================================
  THE ⊗ CLAUSE is the only one that consumes the theory, and it is where
  the ε-ban does its work.  Properness of a slot is conditional on its
  siblings being real, so the guarded call is unavailable at a trivial
  splitting and a slotwise hypothesis could never be discharged.  But
  `Sh` does NOT mention the motive, so "is this slot inhabited" is a
  separate, NON-RECURSIVE question (`decSh`).  Ask it first:

    every slot inhabited   their shapes discharge `GuardedD`, so the
                           recursive call at each slot is legal;
    some slot empty        the splitting has no shape and is refuted with
                           no recursive call at all.

  That is why no resource grammar appears here.  `Decidable.Guarded`'s
  `resourceOf` derives the same fact from `probeR`/`cert`/`rProper`; that
  route stays convenient for a hand-written step, but generically the
  shapes already carry it.

  ==================================================================
  WHY THE REFUTATION IS `No (μ F)` AND NOT `μ⁻ F`.

  `Inductive.Dual` builds refutations as DATA, and the intended statement
  of this theorem is `μ F ⊎ μ⁻ F`.  It is not proved here, and the
  obstruction is worth recording rather than leaving as a hole:

    A `μ⁻` at a tensor must, for EVERY splitting, name a refuted slot and
    recurse there.  For that recursion to descend, the named slot must be
    a PROPER part -- and which slot is proper depends on the splitting.
    At `(ε , m)` the empty slot is the small one; at `(m , ε)` it is the
    other.  So the negative side is guarded only if the refutation
    CHOOSES the smaller blamed slot, and the obvious implementation --
    take the first slot the shape search rejects -- does not.

  So `μ⁻` needs a hypothesis of the form "blame can always be assigned to
  a proper slot", which is strictly more than `GuardedD` and is not
  implied by it.  Naming it is the next piece of work; asserting it would
  have been wrong.

  PRIMITIVE: none.
-}
module TheoryGrammar.Decidable.Inductive where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order using (_<_)
open import Cubical.Data.Empty as E using (⊥; ⊥*)

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded
open import TheoryGrammar.Enumerable
open import TheoryGrammar.Enumerable.Listed
open import TheoryGrammar.Decidable.Additive
open import TheoryGrammar.Decidable.Listable
open import TheoryGrammar.View
open import TheoryGrammar.Inductive.Dual
open import TheoryGrammar.Inductive.Consistent

private variable ℓS ℓ ℓ' ℓX ℓP ℓA ℓB ℓV ℓM ℓN ℓO : Level

module DecInd {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
              (GS : GradedFib σ ℓX ℓP) (ℓA : Level)
              (X : Type ℓV) (xs : X → S)
              -- THE THEORY'S ONLY OBLIGATION
              (enumSplit : (o : σ .ops) (m : GS .fib .carrier (σ .resultSort o))
                         → Listed (GS .fib .Split o m))
              (enumAr    : (o : σ .ops) → Listed (σ .arities o))
              where

  open Consistent GS ℓA X xs public

  private
    Car : (s : S) → Type ℓX
    Car = GS .fib .carrier

  open CarrierNotation Car using (TheoryTy; _⊢_; ⊤G; _&_; ⊕ᴰ) public
  open DecAdd  Car using (Dec⟨_⟩; ¬G_; dec-yes; dec-no; dec-elim; dec-map) public
  open DecList Car using (dec-⊕ᴰ; dec-&ᴰL) public
  open CompleteViews Car using (Probe) public

  -- WHAT A GRAMMAR OWES.  One clause per former; `Var` owes nothing --
  -- the recursive position is löb's business.

  -- the `Lift` on the constant clause is bookkeeping: the ⊗ clause
  -- quantifies over the arity (level ℓ'), which the constant clause does
  -- not mention, and `Type` is not cumulative The constant clause is a
  -- `Probe` -- `⊤G ⊢ Dec⟨ B ⟩` -- and not a metalanguage decision
  -- function.
  DecDesc : {s : S} → Functor s → Type (ℓ-max ℓX (ℓ-max ℓA ℓ'))
  DecDesc {s} (⌜ B ⌝) = Lift ℓ' (Probe B)
  DecDesc (Var x)     = Unit*
  DecDesc (⊕e Y G)    = Listed Y × ((y : Y) → DecDesc (G y))
  DecDesc (&e Y G)    = Listed Y × ((y : Y) → DecDesc (G y))
  DecDesc (⊗e o G)    = (a : σ .arities o) → DecDesc (G a)

  -- IS THIS LAYER INHABITED?  A structural recursion that never mentions
  -- the motive -- which is exactly why the ⊗ clause may run it BEFORE
  -- recursing, and why it needs no guardedness.

  decSh : {s : S} (F : Functor s) → DecDesc F
        → (m : Car s) → Sh F m ⊎ No (Sh F m)

  decSh (⌜ B ⌝) dB m = mapD lift lower (lower dB m tt)

  decSh (Var x) _ m = inl tt*

  -- `Sh (⊕e Y G) m` IS `Σ y, Sh (G y) m` definitionally, so `decΣ`'s
  -- answer is already the right type -- no reshuffle
  decSh (⊕e Y G) (lY , dG) m =
    decΣ (lY .elts) (lY .complete) λ y → decSh (G y) (dG y) m

  -- ... and `Sh (&e Y G) m` IS the Π, so `findΠ` is, modulo turning the
  -- offending index into a refutation
  decSh (&e Y G) (lY , dG) m =
    elimD inl missΠ (findΠ (lY .elts) (lY .complete)
                           λ y → decSh (G y) (dG y) m)

  decSh (⊗e o G) dG m =
    decΣ (enumSplit o m .elts) (enumSplit o m .complete) λ sp →
      elimD inl missΠ (findΠ (enumAr o .elts) (enumAr o .complete)
                             λ a → decSh (G a) (dG a) (GS .fib .parts o m sp a))

  -- THE LAYER, DECIDED -- against the DIRECT interpretation.

  decC : {s : S} (F : Functor s) → DecDesc F
       → {A : Ix → Type ℓM} {Ok : Ix → Type ℓO}
       → (m : Car s) → Reaches F m Ok
       → ((j : Ix) → Ok j → A j ⊎ No (A j))
       → DirC _ F A m ⊎ No (DirC _ F A m)

  -- the probe, transported across the constant former's `Lift` -- and
  -- `dec-map` is a term, so this clause is a composite
  decC (⌜ B ⌝) dB {A = A} m _ rec =
    dec-map B (DirC _ (⌜ B ⌝) A) (λ _ → lift) (λ _ → lower) m (lower dB m tt)

  decC (Var x) _ m rp rec = mapD lift lower (rec (x , m) (lower rp))

  -- `DirC _ (⊕e Y G) A` IS `⊕ᴰ Y (λ y → DirC _ (G y) A)` definitionally,
  -- so `Decidable.Listable`'s rule applies on the nose.  The list is a
  -- WITNESS for that `⊢`-term, not the interface.
  decC (⊕e Y G) (lY , dG) {A = A} m rp rec =
    dec-⊕ᴰ Y (λ y → DirC _ (G y) A) (lY .elts) (lY .complete) m
           λ y → decC (G y) (dG y) m (rp y) rec

  -- ... and dually, `⟦ &e Y G ⟧` IS `&ᴰ Y`
  decC (&e Y G) (lY , dG) {A = A} m rp rec =
    dec-&ᴰL Y (λ y → DirC _ (G y) A) (lY .elts) (lY .complete) m
            λ y → decC (G y) (dG y) m (rp y) rec

  -- THE ONE CLAUSE THAT CONSUMES THE THEORY.  The shape pre-pass runs
  -- first, so a splitting with an empty slot dies with no recursive call;
  -- a splitting whose slots all have shapes hands those to `Reaches`.
  decC (⊗e o G) dG {A = A} m rp rec =
    decΣ (enumSplit o m .elts) (enumSplit o m .complete) atSplit
    where
      Slots : GS .fib .Split o m → Type _
      Slots sp = (a : σ .arities o) → DirC _ (G a) A (GS .fib .parts o m sp a)

      atSplit : (sp : GS .fib .Split o m) → Slots sp ⊎ No (Slots sp)
      atSplit sp =
        elimD withShapes
              (λ y h → missΠ y (λ a → layerFrom (G a) _ (h a) .fst))
              (findΠ (enumAr o .elts) (enumAr o .complete)
                     λ a → decSh (G a) (dG a) (GS .fib .parts o m sp a))
        where
          withShapes : ((a : σ .arities o) → Sh (G a) (GS .fib .parts o m sp a))
                     → Slots sp ⊎ No (Slots sp)
          withShapes ws =
            elimD inl missΠ (findΠ (enumAr o .elts) (enumAr o .complete)
                                   λ a → decC (G a) (dG a) _ (rp sp ws a) rec)

  -- ... and the ONE conversion, from the direct interpretation to the
  -- container form `μ`'s `sup` consumes.
  decLayer : {s : S} (F : Functor s) → DecDesc F
           → {A : Ix → Type ℓM} {Ok : Ix → Type ℓO}
           → (m : Car s) → Reaches F m Ok
           → ((j : Ix) → Ok j → A j ⊎ No (A j))
           → Layer⁺ F A m ⊎ No (Layer⁺ F A m)
  decLayer F dF m rp rec =
    mapD (layerFrom F m) (layerTo F m) (decC F dF m rp rec)

  -- T4.  THE FIXED POINT.

  module _ {F : (x : X) → Functor (xs x)}
           (dF : (x : X) → DecDesc (F x))
           (gF : (x : X) (m : Car (xs x)) → GuardedD (F x) m)
    where

    DecMot : Ix → Type ℓμ
    DecMot i = μ F i ⊎ No (μ F i)

    -- THE FIXPOINT, as terms. `Inductive`'s header explains why these
    -- cannot be stated generically -- `⟦_⟧c` and `μ` sit at different
    -- levels -- and must be given where the levels are concrete.
    MuG : (x : X) → TheoryTy ℓμ (xs x)
    MuG x m = μ F (x , m)

    LayG : (x : X) → TheoryTy _ (xs x)
    LayG x m = Layer⁺ (F x) (μ F) m

    rollᴳ : (x : X) → LayG x ⊢ MuG x
    rollᴳ x m (sh , f) = sup sh f

    unrollᴳ : (x : X) → MuG x ⊢ LayG x
    unrollᴳ x m t = unroll t

    -- THE STEP. The decision is eliminated with `dec-elim` and
    -- reintroduced with `dec-yes` / `dec-no` -- `Decidable.Additive`'s
    -- rules, which it is explicit are the ONLY sanctioned way to take a
    -- decision apart.
    decStep : (i : Ix) → ▷g DecMot i → DecMot i
    decStep (x , m) rec =
      dec-elim (LayG x) m
        (λ l → dec-yes (MuG x) m (rollᴳ x m l))
        (λ k → dec-no  (MuG x) m λ t → k (unrollᴳ x m t))
        (decLayer (F x) (dF x) m (gF x m) (λ j q → rec j q))

    decμ : (i : Ix) → DecMot i
    decμ = löb decStep

    -- T5.  UNIQUENESS.  Any solution of the same recurrence IS `decμ`,
    -- so a tabulated implementation is correct by one appeal rather than
    -- by re-verification.  `DP` consumes exactly this.

    decμ-unfold : (i : Ix) → decμ i ≡ decStep i (λ j _ → decμ j)
    decμ-unfold = löb-unfold decStep

    decμ-unique : (h : (i : Ix) → DecMot i)
                → ((i : Ix) → h i ≡ decStep i (λ j _ → h j))
                → (i : Ix) → h i ≡ decμ i
    decμ-unique = löb-unique decStep
