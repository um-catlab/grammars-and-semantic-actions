{-
  WHAT THE DSL GAVE, MEASURED.  Every equation the mode development
  leans on, with its cost:

    ⊗-β/⊗-η    curry/uncurry at a context promodel ..... refl
    ⊸-η        `⊸ᶠ` at the canonical focus ............. refl
    ⟜-β-{ord,lin,rel}  `⟜-app ∘ ⟜-lam` ....... refl, all three
    ⟜-η-{ord,lin,rel}  `⟜-lam ∘ ⟜-app` ....... funExt, all three
    parts-split (in `Modes.Substrate`) ....... funExt (Bool arity)

  Both ⟜ lines CITE `CanonicalFocus.Canon.Residual`: the cost does not
  depend on which promodel is underneath.
  And two REFUTATIONS.  `splitR≢splitL` kills unique readability for
  every context promodel -- why `Decidable.Splittings` exists -- and
  `no-unsplit` kills `Representable.unsplit` -- why `CanonicalFocus`
  states a conjecture where it once asserted.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Modes.Laws where

open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.List.Properties using (¬nil≡cons; cons-inj₁)
open import Cubical.Data.Sigma
open import Cubical.Foundations.Prelude
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
  -- The substrate they are read at here, `Lin`, is `Interleave` -- the
  -- QUOTIENT case -- so these are the test that the generic laws survive
  -- a non-free promodel.
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

  -- The residual at a REPRESENTABLE, forward direction, at each of the
  -- three substrates.  `Canon.Residual` supplies it from one hypothesis
  -- (`Core.repJ`) and it is `refl` there, so it is `refl` here -- for
  -- `Split3`, `Ilv` and `Ilv3` alike, which are three different types.

  ⟜-β-ord : (B : Ord.CtxG) (Δ Γ : Ord.Ctx) (b : Ord.shift B Δ Γ)
          → Ord.⟜-app B Δ Γ (Ord.⟜-lam B Δ Γ b) ≡ b
  ⟜-β-ord = Ord.⟜-β

  ⟜-β-lin : (B : Lin.CtxG) (Δ Γ : Lin.Ctx) (b : Lin.shift B Δ Γ)
          → Lin.⟜-app B Δ Γ (Lin.⟜-lam B Δ Γ b) ≡ b
  ⟜-β-lin = Lin.⟜-β

  ⟜-β-rel : (B : Rel.CtxG) (Δ Γ : Rel.Ctx) (b : Rel.shift B Δ Γ)
          → Rel.⟜-app B Δ Γ (Rel.⟜-lam B Δ Γ b) ≡ b
  ⟜-β-rel = Rel.⟜-β

  -- ================================================================
  -- funExt, and the reason is not the substrate: `⟜-η` equates two
  -- FUNCTIONS of the rest-tuple, so extensionality is the statement's
  -- own cost, not the residual's.  Inside it there is no `Eq.sym` to
  -- undo by hand -- `singJ` absorbed that -- and the cost is the same at
  -- all three substrates, exactly as β's is.
  -- ================================================================

  ⟜-η-ord : (B : Ord.CtxG) (Δ Γ : Ord.Ctx) (h : (B Ord.⟜ᶜ Δ) Γ)
          → Ord.⟜-lam B Δ Γ (Ord.⟜-app B Δ Γ h) ≡ h
  ⟜-η-ord = Ord.⟜-η

  ⟜-η-lin : (B : Lin.CtxG) (Δ Γ : Lin.Ctx) (h : (B Lin.⟜ᶜ Δ) Γ)
          → Lin.⟜-lam B Δ Γ (Lin.⟜-app B Δ Γ h) ≡ h
  ⟜-η-lin = Lin.⟜-η

  ⟜-η-rel : (B : Rel.CtxG) (Δ Γ : Rel.Ctx) (h : (B Rel.⟜ᶜ Δ) Γ)
          → Rel.⟜-lam B Δ Γ (Rel.⟜-app B Δ Γ h) ≡ h
  ⟜-η-rel = Rel.⟜-η

  -- ================================================================
  -- NEGATIVE MEASUREMENT 1: `Split` IS NOT A PROPOSITION.
  --
  -- A one-name context splits two ways, so unique readability -- the
  -- hypothesis `Decidable.Tensor` runs on -- fails.  The same two
  -- splittings exist for `Split3` (ordered) and, with a third, for
  -- `Ilv3` (relevant).  Deciding the tensor therefore cannot go through
  -- `DecReadable`; it goes through `DecSplittings`, whose only field is
  -- `dec-⊗`'s conclusion.
  -- ================================================================

  -- the two splittings of a one-name context, as WITNESSES: `x` all on
  -- the right, and `x` all on the left
  splitR splitL : (x : Name) → Il.CSplit mul (x ∷ [])
  splitR x = [] , x ∷ [] , right nil
  splitL x = x ∷ [] , [] , left nil

  splitR≢splitL : (x : Name) → splitR x ≡ splitL x → ⊥
  splitR≢splitL x p = ¬nil≡cons (cong fst p)

  -- ================================================================
  -- NEGATIVE MEASUREMENT 2: `unsplit` IS FALSE AT A QUOTIENT.
  --
  -- `Representable.unsplit` -- `op o (parts o m sp) Eq.≡ m`, the
  -- hypothesis a comparison of the canonical focus with the residual of
  -- `⊗ˢ` would need -- fails at the quotient substrates: `Ilv` is
  -- strictly bigger than the graph of `++`, and one splitting of
  -- `y ∷ x ∷ []` has parts `x ∷ []`, `y ∷ []`.  The residual's β and η
  -- hold at this very substrate regardless (they never mention `Split`),
  -- which is what makes the two claims independent rather than one
  -- being evidence for the other.
  -- ================================================================

  swapped : (x y : Name) → Il.fib .Split mul (y ∷ x ∷ [])
  swapped x y = (x ∷ []) , (y ∷ []) , right (left nil)

  no-unsplit : (x y : Name) → (x ≡ y → ⊥)
             → Il.point .op mul (Il.fib .parts mul (y ∷ x ∷ []) (swapped x y))
                 Eq.≡ (y ∷ x ∷ [])
             → ⊥
  no-unsplit x y x≢y e = x≢y (cons-inj₁ (Eq.eqToPath e))
