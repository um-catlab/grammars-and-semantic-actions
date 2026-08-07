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
open import Cubical.Data.Sum using (_⊎_; inl; inr)
import Cubical.Data.Equality as Eq

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
  -- THE ADJOINT TRIPLE.   Σ_act  ⊣  δ  ⊣  Π_act
  --
  -- `δ` is precomposition, and precomposition between families of types
  -- always has BOTH adjoints -- Σ and Π over the FIBRES of the action.
  -- So the derivative's famous left adjoint (tensor with a
  -- representable) and its "amazing" right adjoint are not monoid
  -- facts: they exist for every theory and every action, and this is
  -- the whole construction.
  --
  --   Σact A y = Σ[ x ] (act x ≡ y) × A x   -- y arises by acting on an A
  --   δ    B x = B (act x)                  -- the world after acting
  --   Πact A y = (x) → act x ≡ y → A x      -- EVERY way y could arise
  --
  -- WHAT THEY SAY ABOUT RESOURCES.  The fibre of `act` at `y` is the set
  -- of ways to peel one step off `y`.  So `Σact` is EXISTENTIAL over
  -- that set and `Πact` is UNIVERSAL over it, and the two differ exactly
  -- as much as the peeling is ambiguous:
  --
  --   * strings -- fibres are subsingletons, since `c ∷ v = w` pins `v`.
  --     Σ and Π agree where either is inhabited; peeling is
  --     deterministic; "views from the left" is available.
  --   * bags -- the fibre at `m` for "remove an x" has one element per
  --     occurrence.  `Σact` says SOME removal leaves an A, `Πact` says
  --     EVERY removal does.  These genuinely differ.
  --
  -- `fibreContr→Σ≃Π` below makes that precise: the two adjoints coincide
  -- exactly when the fibres are contractible -- which is the pointwise
  -- form of `Free`, and the reason freeness is what "views from the
  -- left" turns on.
  --
  -- Equalities are `Eq.≡` so both adjunctions COMPUTE: matching
  -- `Eq.refl` collapses the fibre and every unit/counit below is refl.
  -- ================================================================

  Σact : TheoryTy ℓA s → TheoryTy (ℓ-max ℓX ℓA) t
  Σact A y = Σ[ x ∈ X s ] ((act x Eq.≡ y) × A x)

  Πact : TheoryTy ℓA s → TheoryTy (ℓ-max ℓX ℓA) t
  Πact A y = (x : X s) → act x Eq.≡ y → A x

  -- the fibre: the ways `y` can be peeled by this action
  Fibre : X t → Type ℓX
  Fibre y = Σ[ x ∈ X s ] (act x Eq.≡ y)

  -- Σact ⊣ δ
  Σ⊣δ : {A : TheoryTy ℓA s} {B : TheoryTy ℓB t} → Iso (Σact A ⊢ B) (A ⊢ δ B)
  Σ⊣δ .Iso.fun f x a = f (act x) (x , Eq.refl , a)
  Σ⊣δ .Iso.inv g _ (x , Eq.refl , a) = g x a
  Σ⊣δ .Iso.sec _ = refl
  Σ⊣δ .Iso.ret f = funExt λ _ → funExt λ { (x , Eq.refl , a) → refl }

  -- δ ⊣ Πact -- the amazing right adjoint
  δ⊣Π : {A : TheoryTy ℓA s} {B : TheoryTy ℓB t} → Iso (δ B ⊢ A) (B ⊢ Πact A)
  δ⊣Π .Iso.fun f _ b x Eq.refl = f x b
  δ⊣Π .Iso.inv g x b = g (act x) b x Eq.refl
  δ⊣Π .Iso.sec g = funExt λ _ → funExt λ _ → funExt λ _ → funExt λ { Eq.refl → refl }
  δ⊣Π .Iso.ret _ = refl

  -- ... and the gap between the two adjoints is exactly the ambiguity
  -- of the peeling.  Splitting the comparison in two is more telling
  -- than an Iso, because the two halves are the two halves of freeness:
  --
  --   Σ→Π needs the fibre to be a PROPOSITION  -- uniqueness
  --   Π→Σ needs the fibre to be INHABITED      -- existence
  --
  -- Contractible = both = free.  Compare `scanμ` (existence, always)
  -- and `Free` (uniqueness, per theory): the same split, one level up.
  Σ→Π : {A : TheoryTy ℓA s} (y : X t)
      → isProp (Fibre y) → Σact A y → Πact A y
  Σ→Π {A = A} y pr (x , e , a) x' e' =
    subst (λ f → A (f .fst)) (pr (x , e) (x' , e')) a

  Π→Σ : {A : TheoryTy ℓA s} (y : X t)
      → Fibre y → Πact A y → Σact A y
  Π→Σ y (x , e) h = x , e , h x e

  -- ================================================================
  -- WHAT THE TRIPLE BUYS.
  --
  -- (1) It EXPLAINS the refl laws below.  `δ` has a left adjoint, so it
  --     preserves limits (⊤, &, &ᴰ, ⇒); it has a right adjoint, so it
  --     preserves colimits (⊥, ⊕, ⊕ᴰ).  Those are exactly the seven
  --     laws proved by `refl` in `δ-laws`.  They were not a coincidence
  --     of precomposition being pointwise -- they are adjointness.
  --
  -- (2) The adjoints preserve on their own side, and this is the part
  --     that is new rather than a re-reading.  `Σact` is a left adjoint
  --     so it preserves COPRODUCTS; `Πact` is a right adjoint so it
  --     preserves PRODUCTS.  Neither preserves the other side, and that
  --     asymmetry is real: `Σact (A & B)` is strictly stronger than
  --     `Σact A & Σact B` when the fibre has more than one point, since
  --     the left says ONE peeling witnesses both.
  --
  -- (3) Read as parsers: `Σact` is the MAY semantics ("some
  --     decomposition works") and `Πact` the MUST ("every decomposition
  --     does").  For a free theory they agree.  For a commutative one
  --     they are two genuinely different parsers, and until now only
  --     the `Σ` one had a name.
  -- ================================================================

  -- Πact preserves products, on the nose in both directions.
  Πact-& : {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} (y : X t)
         → Iso (Πact (A & B) y) ((Πact A & Πact B) y)
  Πact-& y .Iso.fun h       = (λ x e → h x e .fst) , (λ x e → h x e .snd)
  Πact-& y .Iso.inv (f , g) = λ x e → f x e , g x e
  Πact-& y .Iso.sec _ = refl
  Πact-& y .Iso.ret _ = refl

  -- Σact preserves coproducts.
  Σact-⊕ : {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} (y : X t)
         → Iso (Σact (A ⊕ B) y) ((Σact A ⊕ Σact B) y)
  Σact-⊕ y .Iso.fun (x , e , inl a) = inl (x , e , a)
  Σact-⊕ y .Iso.fun (x , e , inr b) = inr (x , e , b)
  Σact-⊕ y .Iso.inv (inl (x , e , a)) = x , e , inl a
  Σact-⊕ y .Iso.inv (inr (x , e , b)) = x , e , inr b
  Σact-⊕ y .Iso.sec (inl _) = refl
  Σact-⊕ y .Iso.sec (inr _) = refl
  Σact-⊕ y .Iso.ret (_ , _ , inl _) = refl
  Σact-⊕ y .Iso.ret (_ , _ , inr _) = refl

  -- The MAY/MUST comparison in the other direction is free: one
  -- peeling that works is, in particular, evidence at that peeling.
  -- (The converse is `Σ→Π`, and needs unambiguity.)
  Σact-& : {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} (y : X t)
         → Σact (A & B) y → (Σact A & Σact B) y
  Σact-& y (x , e , (a , b)) = (x , e , a) , (x , e , b)

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
