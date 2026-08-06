{-
  THE DERIVATIVE IS PRECOMPOSITION.

  Brzozowski's `δ_c A w = A (c ∷ w)` is not a construction on grammars at
  all -- it is restriction along a map of carriers.  Saying it that way
  buys three things at once:

  * `δ` is DEFINITIONALLY precomposition, so there is no proof component
    and no green slime.  Contrast the `Grammar/Derivative/String.agda`
    being replaced, where ~45 lines of `Eq.ap` exist only to push a
    `w ≡ c ∷ w'` through the connectives.

  * Every ADDITIVE law is `refl`, uniformly and with no case analysis
    (`δ-laws` below).  That is not luck: the additive connectives are
    pointwise in the index, and precomposition is exactly what commutes
    with pointwise structure.  A derivative that had to inspect its
    argument would be evidence the connective was not additive.

  * Which map you differentiate along becomes a parameter.  For strings
    it is `c ∷ _`; that is `appop` with the LEFT slot pinned to `c`, and
    pinning all-but-one slot of an operation is precisely `Assembly`
    (TheoryGrammar.CanonicalFocus).  So `δ` exists for any theory, once
    per (operation, focused slot, choice of the other slots) -- rather
    than only for signatures with a literally unary operation.

  What is NOT here, and cannot be: the law for `⊗`.  Differentiating a
  composite has to decide which slot absorbed the action, and that is
  equidivisibility (Levi's lemma) -- true of free monoids, false of
  commutative ones.  It appears below as `DerivTensor`, a hypothesis to
  be discharged per promodel, stated as what it actually is: an
  INVERSION PRINCIPLE for `Split o' (act x)`.
-}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Derivative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.CanonicalFocus

private variable ℓS ℓ ℓ' ℓX ℓP ℓA ℓB ℓC ℓY : Level

-- ==================================================================
-- The derivative, along an arbitrary map of carriers.
--
-- Nothing about the signature is used.  `δ` is a functor
-- `TheoryTy _ t → TheoryTy _ s` for each `act : X s → X t`, and it is
-- the identity on the underlying data.
-- ==================================================================
module Deriv {S : Type ℓS} (X : S → Type ℓX) {s t : S} (act : X s → X t)
  where

  open CarrierNotation X

  δ : TheoryTy ℓA t → TheoryTy ℓA s
  δ B x = B (act x)

  -- functorial, with both laws refl -- `δ` does not touch the payload
  δ-map : {B : TheoryTy ℓA t} {C : TheoryTy ℓB t} → B ⊢ C → δ B ⊢ δ C
  δ-map f x = f (act x)

  δ-map-id : {B : TheoryTy ℓA t} → δ-map (id⊢ {A = B}) ≡ id⊢
  δ-map-id = refl

  δ-map-∘ : {B : TheoryTy ℓA t} {C : TheoryTy ℓB t} {D : TheoryTy ℓC t}
            (g : C ⊢ D) (f : B ⊢ C)
          → δ-map (g ∘⊢ f) ≡ (δ-map g ∘⊢ δ-map f)
  δ-map-∘ g f = refl

  -- ================================================================
  -- THEOREM.  `δ` commutes with EVERY additive connective, on the nose.
  --
  -- Each of these is the corresponding line of `Grammar/Derivative/`,
  -- where it was a lemma with a proof.  Here they are all `refl`,
  -- because both sides are literally the same function.
  -- ================================================================
  module δ-laws {Y : Type ℓY}
                {B : TheoryTy ℓA t} {C : TheoryTy ℓB t}
                {F : Y → TheoryTy ℓA t} where

    δ-⊤  : δ {ℓA = ℓ-zero} ⊤G ≡ ⊤G
    δ-⊤  = refl

    δ-⊥  : δ {ℓA = ℓ-zero} ⊥G ≡ ⊥G
    δ-⊥  = refl

    δ-&  : δ (B & C) ≡ (δ B & δ C)
    δ-&  = refl

    δ-⊕  : δ (B ⊕ C) ≡ (δ B ⊕ δ C)
    δ-⊕  = refl

    δ-⇒  : δ (B ⇒ C) ≡ (δ B ⇒ δ C)
    δ-⇒  = refl

    δ-⊕ᴰ : δ (⊕ᴰ Y F) ≡ ⊕ᴰ Y (λ y → δ (F y))
    δ-⊕ᴰ = refl

    δ-&ᴰ : δ (&ᴰ Y F) ≡ &ᴰ Y (λ y → δ (F y))
    δ-&ᴰ = refl

-- ==================================================================
-- The actions worth differentiating along.
--
-- `Assembly Fib o i` is "an operation with a named complement at slot
-- `i`"; choosing a tuple `a⃗` for that complement pins it to a map
-- `carrier (sortOf o i) → carrier (resultSort o)`.  For strings,
-- `o = appop`, `i` the right slot and `a⃗ = c` gives `c ∷ _`.
--
-- This is the same datum `CanonicalFocus` uses to build the residual --
-- which is the statement that the derivative and the residual are two
-- readings of one structure, and `δ-plug` below is the comparison.
-- ==================================================================
module ActOf {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
             (Fib : Fibered σ ℓX (ℓ-max ℓ' ℓX)) (P : LaxPoint Fib)
             (o : σ .ops) (i : σ .arities o) (As : Assembly Fib o i)
             (a⃗ : (r : As .Rest) → Fib .carrier (σ .sortOf o (As .restOf r)))
  where

  open FibNotation Fib
  open Canon Fib P o i As

  act : Fib .carrier (σ .sortOf o i) → Fib .carrier (σ .resultSort o)
  act x = P .op o (As .tuple x a⃗)

  open Deriv (Fib .carrier) act public

  -- The residual maps to the derivative: `⊸ᶠ A B` is "B once the hole is
  -- filled by ANY complement", `δ B` is "B once it is filled by a⃗".  So
  -- the comparison is application at `a⃗`, and it is `Canon.plug`
  -- verbatim -- no new content, which is the point.
  δ-plug : {A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a)}
           {B : TheoryTy ℓB (σ .resultSort o)}
         → ((r : As .Rest) → A (As .restOf r) (a⃗ r))
         → ⊸ᶠ A B ⊢ δ B
  δ-plug {A = A} {B = B} pt = plug {A = A} {B = B} a⃗ pt

-- ==================================================================
-- The one law that is NOT free: differentiating a composite.
--
--   δ (⊗ˢ o' A) x  =  Σ[ sp ∈ Split o' (act x) ] (payloads)
--
-- so everything turns on describing `Split o' (act x)` in terms of `x`.
-- That is an INVERSION PRINCIPLE for the action, and it is exactly the
-- content of Levi's lemma: for strings, a decomposition of `c ∷ w` is a
-- decomposition of `w` together with which slot took the `c`, and with
-- the inductive `Split` family that inversion is a PATTERN MATCH.  For
-- bags it is false, which is why there is no bag derivative.
--
-- Stated as an Iso rather than a bare map in both directions, so that a
-- discharge cannot forget a decomposition and still typecheck.
-- ==================================================================
module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
         (Fib : Fibered σ ℓX (ℓ-max ℓ' ℓX)) (P : LaxPoint Fib)
         (o : σ .ops) (i : σ .arities o) (As : Assembly Fib o i)
         (a⃗ : (r : As .Rest) → Fib .carrier (σ .sortOf o (As .restOf r)))
  where

  open FibNotation Fib
  open ActOf Fib P o i As a⃗

  -- `R` is the instance's answer: what the derivative of this composite
  -- unfolds to.  The point of the record is that `R` is data supplied by
  -- the promodel, not something the generic layer can guess.
  --
  -- The composite is of the SAME operation `o` we differentiate along.
  -- That is not a convenience: Levi's lemma is a statement about ONE
  -- binary operation (`uv = u'v'` implies a common refinement), and a
  -- composite of some other operation need not even live at the sort
  -- `δ` acts on.
  DerivTensor : (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
                (R : TheoryTy ℓB (σ .sortOf o i))
              → Type (ℓ-max ℓ' (ℓ-max ℓX (ℓ-max ℓA ℓB)))
  DerivTensor A R =
    (x : Fib .carrier (σ .sortOf o i)) → Iso (δ (⊗ˢ o A) x) (R x)

  -- Having it, the derivative of a composite is a grammar map both ways.
  fromDerivTensor : {A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a)}
                    {R : TheoryTy ℓB (σ .sortOf o i)}
                  → DerivTensor A R → (δ (⊗ˢ o A) ⊢ R)
  fromDerivTensor h x = h x .Iso.fun

  intoDerivTensor : {A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a)}
                    {R : TheoryTy ℓB (σ .sortOf o i)}
                  → DerivTensor A R → (R ⊢ δ (⊗ˢ o A))
  intoDerivTensor h x = h x .Iso.inv
