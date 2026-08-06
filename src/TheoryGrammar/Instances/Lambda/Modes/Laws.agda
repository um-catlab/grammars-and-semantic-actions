{-
  WHAT THE DSL GAVE, MEASURED.

  Every equation the mode development actually leans on, with its cost:

    ⊗ˢ β/η at a context promodel .............. refl
    ⊸ᶠ β/η at the canonical focus .............. refl
    ⟜ β at a representable (`⟜-app ∘ ⟜-lam`) ... refl
    ⟜ η at a representable (`⟜-lam ∘ ⟜-app`) ... funExt, and nothing else
    parts-split (in the three promodel files) . funExt (Bool arity)

  Both ⟜ lines are now CITATIONS of `CanonicalFocus.Canon.Residual`, not
  proofs, and they are repeated at all three substrates below: the cost
  does not depend on which promodel is underneath.  β stays definitional
  (checked: `refl` still proves it here); η cannot be, since it equates
  two functions.  The `Eq.J + sym-invol` this table used to charge η is
  gone -- `singJ` carries it once, generically, and reduces on `refl`.

  Two negative measurements.  `splitNotProp` exhibits two distinct
  splittings of a one-name context, so `DecReadable.splitProp` is FALSE
  for every context promodel here and `Decidable.Tensor.dec-⊗` is
  unavailable -- `Decidable.Splittings` exists because of it.
  `no-unsplit` refutes `Representable.unsplit` at the linear substrate,
  which is why `CanonicalFocus` states a conjecture where it used to
  assert one.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Modes.Laws where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.List.Properties using (¬nil≡cons; cons-inj₁)
open import Cubical.Relation.Nullary.Base using (Discrete)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Fibered
open import TheoryGrammar.Instances.Lambda.Modes.Ctx
open import TheoryGrammar.Instances.Lambda.Modes.Instances

import TheoryGrammar.Instances.Bags.Base as Bg

module Laws (Name : Type₀) (_≟_ : Discrete Name) where

  open Modes Name _≟_
  open Bg Name using (Ilv; nil; left; right)

  -- ================================================================
  -- refl.  The multiplicative and residual universal properties survive
  -- instantiation at a context promodel: neither needs a pattern match.
  -- ================================================================

  module _ where
    open Lin

    ⊗-β : (A : Bool → CtxG) (B : CtxG) (g : MultiHomˢ mul A B)
        → curryˢ mul {A = A} {B = B} (uncurryˢ mul {A = A} {B = B} g) ≡ g
    ⊗-β A B g = refl

    ⊗-η : (A : Bool → CtxG) (B : CtxG) (f : ⊗ˢ mul A ⊢ B)
        → uncurryˢ mul {A = A} {B = B} (curryˢ mul {A = A} {B = B} f) ≡ f
    ⊗-η A B f = refl

    ⊸-η : (A : Bool → CtxG) (B : CtxG) (g : A true ⊢ ⊸ᶠ A B)
        → ⊸ᶠ-lam {A = A} {B = B} (⊸ᶠ-app {A = A} {B = B} g) ≡ g
    ⊸-η A B g = refl

    -- The residual at a REPRESENTABLE, both ways: cited, not reproved.
    -- `Canon.Residual` supplies these for ANY substrate, from one
    -- hypothesis (`Core.repJ`); β is still `refl` there, so it is `refl`
    -- here.  Note the substrate this module is instantiated at, `Lin`,
    -- is `Interleave` -- the QUOTIENT case -- so these two lines are the
    -- test that the generic laws survive a non-free promodel.
    ⟜-β-lin : (B : CtxG) (Δ Γ : Ctx) (b : shift B Δ Γ)
            → ⟜-app B Δ Γ (⟜-lam B Δ Γ b) ≡ b
    ⟜-β-lin = ⟜-β

  -- ================================================================
  -- funExt, and the reason is not the substrate: `⟜-η` equates two
  -- FUNCTIONS of the rest-tuple, so extensionality is the statement's
  -- own cost, not the residual's.  Inside it there is now no `Eq.sym`
  -- to undo by hand -- `singJ` absorbed that -- and the same two lines
  -- hold for the ordered and relevant substrates, where `Split` is a
  -- different type altogether.
  -- ================================================================

  module _ where
    open Lin

    ⟜-η-lin : (B : CtxG) (Δ Γ : Ctx) (h : (B ⟜ᶜ Δ) Γ)
            → ⟜-lam B Δ Γ (⟜-app B Δ Γ h) ≡ h
    ⟜-η-lin = ⟜-η

  module _ where
    open Ord renaming (⟜-β to ⟜-βᴼ; ⟜-η to ⟜-ηᴼ)

    ⟜-β-ord : (B : CtxG) (Δ Γ : Ctx) (b : shift B Δ Γ)
            → ⟜-app B Δ Γ (⟜-lam B Δ Γ b) ≡ b
    ⟜-β-ord = ⟜-βᴼ

    ⟜-η-ord : (B : CtxG) (Δ Γ : Ctx) (h : (B ⟜ᶜ Δ) Γ)
            → ⟜-lam B Δ Γ (⟜-app B Δ Γ h) ≡ h
    ⟜-η-ord = ⟜-ηᴼ

  module _ where
    open Rel renaming (⟜-β to ⟜-βᴿ; ⟜-η to ⟜-ηᴿ)

    ⟜-β-rel : (B : CtxG) (Δ Γ : Ctx) (b : shift B Δ Γ)
            → ⟜-app B Δ Γ (⟜-lam B Δ Γ b) ≡ b
    ⟜-β-rel = ⟜-βᴿ

    ⟜-η-rel : (B : CtxG) (Δ Γ : Ctx) (h : (B ⟜ᶜ Δ) Γ)
            → ⟜-lam B Δ Γ (⟜-app B Δ Γ h) ≡ h
    ⟜-η-rel = ⟜-ηᴿ

  -- ================================================================
  -- THE NEGATIVE MEASUREMENT.
  --
  -- A one-name context splits two ways, so `Split` is not a proposition
  -- and unique readability -- the hypothesis `Decidable.Tensor` runs on --
  -- fails.  The same two splittings exist for `Split3` (ordered) and, with
  -- a third, for `Ilv3` (relevant).  Deciding the tensor therefore cannot
  -- go through `DecReadable`; it goes through `DecSplittings`, whose only
  -- field is `dec-⊗`'s conclusion.
  -- ================================================================

  -- ... and the OTHER negative measurement, the one that keeps
  -- `CanonicalFocus`'s conjecture a conjecture.  `Representable.unsplit`
  -- -- `op o (parts o m sp) Eq.≡ m`, the hypothesis a comparison of the
  -- canonical focus with the residual of `⊗ˢ` would need -- is FALSE at
  -- the quotient substrates: `Ilv` is strictly bigger than the graph of
  -- `++`, and one splitting of `y ∷ x ∷ []` has parts `x ∷ []`, `y ∷ []`.
  -- The residual's β and η hold at this very substrate regardless (they
  -- never mention `Split`), which is what makes the two claims
  -- independent rather than one being evidence for the other.

  swapped : (x y : Name) → Il.fib .Split mul (y ∷ x ∷ [])
  swapped x y = (x ∷ []) , (y ∷ []) , right (left nil)

  no-unsplit : (x y : Name) → (x ≡ y → ⊥)
             → Il.point .op mul (Il.fib .parts mul (y ∷ x ∷ []) (swapped x y))
                 Eq.≡ (y ∷ x ∷ [])
             → ⊥
  no-unsplit x y x≢y e = x≢y (cons-inj₁ (Eq.eqToPath e))

  splitNotProp : (x : Name)
               → Path (Il.CSplit mul (x ∷ []))
                      ([] , x ∷ [] , right nil) (x ∷ [] , [] , left nil)
               → ⊥
  splitNotProp x p = ¬nil≡cons (cong fst p)
