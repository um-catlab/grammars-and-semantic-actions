{-
  EACH EQUATION OF THE THEORY LIFTS TO AN ISOMORPHISM OF CONNECTIVES.

  The mechanism, and why linearity is exactly the side condition.

  A term `t : Tm V vs s` of the signature denotes a COMPOSITE connective:

      ⟪ var v ⟫   A = A v
      ⟪ node o ts ⟫ A = ⊗[ o ] (λ a → ⟪ ts a ⟫ A)

  For a LINEAR term (each variable used exactly once) this composite
  collapses: a point of `⟪ t ⟫ A m` is a valuation ρ of the variables,
  a proof that t evaluates at ρ to m, and an element of `A v (ρ v)` for
  each v.  Nothing else survives -- the nesting of the ⊗s has been
  flattened away.  So `⟪ t ⟫` depends on t ONLY through the function

      eval t : (valuations) → carrier

  and therefore two terms with the same denotation in the model give
  ISOMORPHIC connectives.  That is the lifting theorem: `eqn→Iso`.

  This is where linearity earns its keep.  If a variable occurred twice
  the flattening would need two independent valuations for it and a
  diagonal to identify them, and the collapse fails; if it occurred zero
  times the valuation is unconstrained and the collapse fails the other
  way.  Linear equations lift, non-linear ones (idempotence, inverses)
  do not -- which is the same boundary as "expressible by an operad".

  Below, the flattened form `⊗ᶠ` is taken as PRIMARY and the lifting
  theorem is proved about it, so no linearity predicate on terms is
  needed: `⊗ᶠ` is by construction the flattening, and `⊗[ o ]` is the
  instance at a single operation (`⊗ᶠ≡⊗`).
-}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Equations where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base

private variable ℓS ℓ ℓ' ℓX ℓA ℓB ℓV : Level

-- ==================================================================
-- Terms of the signature (mirrors Cubical.Algebra.Theory.Sorted.Tm).
-- ==================================================================

data Tm {S : Type ℓS} (σ : SortedSig S ℓ ℓ') (V : Type ℓV) (vs : V → S)
  : S → Type (ℓ-max ℓS (ℓ-max ℓ (ℓ-max ℓ' ℓV))) where
  var  : (v : V) → Tm σ V vs (vs v)
  node : (o : σ .ops) → ((a : σ .arities o) → Tm σ V vs (σ .sortOf o a))
       → Tm σ V vs (σ .resultSort o)

module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (M : Model σ ℓX) where

  open Notation M

  -- valuations of a variable context in the model
  Val : {V : Type ℓV} (vs : V → S) → Type (ℓ-max ℓV ℓX)
  Val {V = V} vs = (v : V) → M .carrier (vs v)

  eval : {V : Type ℓV} {vs : V → S} {s : S} → Val vs → Tm σ V vs s → M .carrier s
  eval ρ (var v)     = ρ v
  eval ρ (node o ts) = M .op o (λ a → eval ρ (ts a))

  -- ================================================================
  -- The flattened convolution along an arbitrary "shape function".
  -- ================================================================

  ⊗ᶠ : {V : Type ℓV} {vs : V → S} {s : S}
     → (Val vs → M .carrier s)                 -- the shape
     → ((v : V) → TheoryTy ℓA (vs v))
     → TheoryTy (ℓ-max ℓV (ℓ-max ℓX ℓA)) s
  ⊗ᶠ {vs = vs} f A m = Σ[ ρ ∈ Val vs ] ((f ρ Eq.≡ m) × ((v : _) → A v (ρ v)))

  -- the composite connective denoted by a term
  ⟪_⟫ : {V : Type ℓV} {vs : V → S} {s : S}
      → Tm σ V vs s → ((v : V) → TheoryTy ℓA (vs v)) → TheoryTy _ s
  ⟪ t ⟫ = ⊗ᶠ (λ ρ → eval ρ t)

  -- ================================================================
  -- THE REASSOCIATED FORM, and why it is the one to build maps INTO.
  --
  -- `⊗ᶠ` pairs a valuation with a payload indexed by it.  That is fine
  -- to consume but bad to produce, because `Val vs` is a Π and Π has no
  -- η at a variable context: a valuation reassembled slotwise, as
  -- `λ { x → … ; y → … }`, is only PROPOSITIONALLY the valuation it came
  -- from.  The equation component `f ρ Eq.≡ m` then sits over a `funExt`,
  -- i.e. a `PathP` over a family Agda cannot see is constant, and the
  -- bridge stalls.
  --
  -- Reassociating moves the payload inside the Π:
  --
  --     Σ[ ρ ∈ Π v. carrier (vs v) ] Π v. A v (ρ v)
  --          ≅   Π v. Σ[ c ∈ carrier (vs v) ] A v c
  --
  -- and now the funExt is over a family that does NOT mention the
  -- payload, so `f (fst ∘ θ)` IS definitionally constant along it and
  -- the equation component is `refl` again.
  --
  -- This is the same move `Fibered.agda` makes one level down -- split
  -- the data apart from the equation, expose the pieces as projections --
  -- and it is made for the same reason.  `⊗ᶠ` remains the definition;
  -- `⊗ᶠ'` is the form to target.
  -- ================================================================

  ⊗ᶠ' : {V : Type ℓV} {vs : V → S} {s : S}
      → (Val vs → M .carrier s)
      → ((v : V) → TheoryTy ℓA (vs v))
      → TheoryTy (ℓ-max ℓV (ℓ-max ℓX ℓA)) s
  ⊗ᶠ' {V = V} {vs = vs} f A m =
    Σ[ θ ∈ ((v : V) → Σ[ c ∈ M .carrier (vs v) ] A v c) ]
      (f (λ v → θ v .fst) Eq.≡ m)

  -- Both round trips are `refl`: Σ-η and Π-η, nothing else.
  ⊗ᶠ-reassoc : {V : Type ℓV} {vs : V → S} {s : S}
               (f : Val vs → M .carrier s)
               (A : (v : V) → TheoryTy ℓA (vs v))
               (m : M .carrier s)
             → Iso (⊗ᶠ f A m) (⊗ᶠ' f A m)
  ⊗ᶠ-reassoc f A m .Iso.fun (ρ , e , k) = (λ v → ρ v , k v) , e
  ⊗ᶠ-reassoc f A m .Iso.inv (θ , e) = (λ v → θ v .fst) , e , (λ v → θ v .snd)
  ⊗ᶠ-reassoc f A m .Iso.sec _ = refl
  ⊗ᶠ-reassoc f A m .Iso.ret _ = refl

  -- ================================================================
  -- Equality of shapes gives isomorphism of connectives.
  -- ================================================================

  private
    -- Eq groupoid, by matching (so the round trips compute)
    _∙ᵉ_ : {X : Type ℓX} {x y z : X} → x Eq.≡ y → y Eq.≡ z → x Eq.≡ z
    Eq.refl ∙ᵉ q = q

    ∙ᵉ-symˡ : {X : Type ℓX} {x y z : X} (p : x Eq.≡ y) (e : y Eq.≡ z)
            → Eq.sym p ∙ᵉ (p ∙ᵉ e) ≡ e
    ∙ᵉ-symˡ Eq.refl e = refl

    ∙ᵉ-symʳ : {X : Type ℓX} {x y z : X} (p : x Eq.≡ y) (e : x Eq.≡ z)
            → p ∙ᵉ (Eq.sym p ∙ᵉ e) ≡ e
    ∙ᵉ-symʳ Eq.refl e = refl

  module _ {V : Type ℓV} {vs : V → S} {s : S}
           {f g : Val vs → M .carrier s}
           {A : (v : V) → TheoryTy ℓA (vs v)} where

    -- THEOREM.  Shapes that agree pointwise give isomorphic connectives.
    ⊗ᶠ-cong : ((ρ : Val vs) → g ρ Eq.≡ f ρ) → ∀ m → Iso (⊗ᶠ f A m) (⊗ᶠ g A m)
    ⊗ᶠ-cong p m .Iso.fun (ρ , e , h) = ρ , (p ρ ∙ᵉ e) , h
    ⊗ᶠ-cong p m .Iso.inv (ρ , e , h) = ρ , (Eq.sym (p ρ) ∙ᵉ e) , h
    ⊗ᶠ-cong p m .Iso.sec (ρ , e , h) i = ρ , ∙ᵉ-symʳ (p ρ) e i , h
    ⊗ᶠ-cong p m .Iso.ret (ρ , e , h) i = ρ , ∙ᵉ-symˡ (p ρ) e i , h

  -- ================================================================
  -- THE LIFTING THEOREM.  An equation of the theory, satisfied by the
  -- model, gives an isomorphism between the two composite connectives.
  -- ================================================================

  module _ {V : Type ℓV} {vs : V → S} {s : S}
           (lhs rhs : Tm σ V vs s)
           {A : (v : V) → TheoryTy ℓA (vs v)} where

    eqn→Iso : ((ρ : Val vs) → eval ρ lhs Eq.≡ eval ρ rhs)
            → ∀ m → Iso (⟪ rhs ⟫ A m) (⟪ lhs ⟫ A m)
    eqn→Iso sat = ⊗ᶠ-cong {A = A} sat

  -- ================================================================
  -- ⊗[ o ] is the instance of ⊗ᶠ at a single operation.
  -- ================================================================

  module _ (o : σ .ops) {A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a)} where

    ⊗ᶠ≡⊗ : ∀ m → Iso (⊗ᶠ {vs = σ .sortOf o} (M .op o) A m) (⊗[ o ] A m)
    ⊗ᶠ≡⊗ m .Iso.fun x = x
    ⊗ᶠ≡⊗ m .Iso.inv x = x
    ⊗ᶠ≡⊗ m .Iso.sec _ = refl
    ⊗ᶠ≡⊗ m .Iso.ret _ = refl
