{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Recursion over a guarded description: the strength, the container
   hylomorphism, and the fused connective-form `hyloC`.

   Separate from `Grading` because guardedness is a PROPERTY of a
   description while these are what you DO with it -- and because the
   fusion note below is the subtlest thing in the stack and deserves to
   be findable. -}
module TheoryGrammar.Hylo where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Unit
open import Cubical.Induction.WellFounded

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
open import TheoryGrammar.Later
open import TheoryGrammar.Grading

private variable ℓS ℓ ℓ' ℓX ℓP ℓA ℓM ℓN ℓV : Level

module HyloM {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
             (GS : GradedFib σ ℓX ℓP) (ℓA : Level)
             (X : Type ℓV) (xs : X → S) where

  open Grade GS ℓA X xs public

  -- ================================================================
  -- THE STRENGTH.  This is ccl's `▷HomActionFam`, derived rather than
  -- assumed: a guarded description can transport a LATER function
  -- across its positions, because every position is strictly smaller.
  -- ================================================================

  mapGuarded : {s : S} (F : Functor s) → Guarded F
             → {A : Ix → Type ℓM} {B : Ix → Type ℓN}
               (m : GS .fib .carrier s)
             → ((j : Ix) → degIx j < GS .deg s m → A j → B j)
             → ⟦ F ⟧ A m → ⟦ F ⟧ B m
  mapGuarded F gF m r (sh , f) = sh , λ p → r _ (gF m sh p) (f p)

  -- ================================================================
  -- HYLOMORPHISM.  coalgebra + algebra + guardedness, by löb.
  -- ================================================================

  module _ {F : (x : X) → Functor (xs x)} (gF : (x : X) → Guarded (F x))
           {A : Ix → Type ℓM} {B : Ix → Type ℓN}
           (c : Coalg F A) (alg : Alg F B) where

    hylo : (i : Ix) → A i → B i
    hylo = löb step
      where
        step : (i : Ix) → ▷ (λ j → A j → B j) i → A i → B i
        step (x , m) rec ai =
          alg x m (mapGuarded (F x) (gF x) m (λ j q → rec j q) (c x m ai))

  -- ================================================================
  -- Per-slot guardedness certificates.
  --
  -- `<⊗e` above requires EVERY recursive slot to be a proper part.  That
  -- is too strong once descriptions nest: in quicksort's
  --     b  =  lo ⊗ (piv ⊗ hi)
  -- the slot holding `hi` is not a proper part of `b` for the reason its
  -- sibling `lo` is -- `lo` may be empty.  `hi` decreases because the
  -- PIVOT sits inside its own factor.  So a slot must be dischargeable
  -- two different ways, and the ⊗e rule takes a certificate per slot.
  -- ================================================================

  private
    <≤-tr : {x y z : ℕ} → x < y → y ≤ z → x < z
    <≤-tr p q = ≤-trans p q

    ≤<-tr : {x y z : ℕ} → x ≤ y → y < z → x < z
    ≤<-tr p q = ≤-trans (suc-≤-suc p) q

  ⊗-guard : (o : σ .ops) (G : (a : σ .arities o) → Functor (σ .sortOf o a))
          → ((m : GS .fib .carrier (σ .resultSort o)) (sp : GS .fib .Split o m)
             (sh : (a : σ .arities o) → Sh (G a) (GS .fib .parts o m sp a))
             (a : σ .arities o) (p : Pos (G a) _ (sh a))
             → degIx (nx (G a) _ (sh a) p) < GS .deg _ m)
          → Guarded (⊗e o G)
  ⊗-guard o G h m (sp , sh) (a , p) = h m sp sh a p

  -- Way 1: the slot's own description already strictly decreases.
  slotGuarded : (o : σ .ops) (m : GS .fib .carrier (σ .resultSort o))
                (sp : GS .fib .Split o m) (a : σ .arities o)
                {G : Functor (σ .sortOf o a)} → Guarded G
              → (sh : Sh G (GS .fib .parts o m sp a)) (p : Pos G _ sh)
              → degIx (nx G _ sh p) < GS .deg _ m
  slotGuarded o m sp a g sh p = <≤-tr (g _ sh p) (GS .deg≤ o m sp a)

  -- Way 2: the slot does not grow, and IS a proper part.
  slotProper : (o : σ .ops) (m : GS .fib .carrier (σ .resultSort o))
               (sp : GS .fib .Split o m) (a : σ .arities o)
               {G : Functor (σ .sortOf o a)} → Guarded≤ G → Proper GS o m sp a
             → (sh : Sh G (GS .fib .parts o m sp a)) (p : Pos G _ sh)
             → degIx (nx G _ sh p) < GS .deg _ m
  slotProper o m sp a g pr sh p = ≤<-tr (g _ sh p) (GS .deg< o m sp a pr)

  -- strict versions of the additive formers
  <⌜⌝ : {s : S} (A : FibNotation.TheoryTy (GS .fib) ℓA s) → Guarded ⌜ A ⌝
  <⌜⌝ A m sh ()

  <⊕e : {s : S} (Y : Type ℓA) (G : Y → Functor s)
      → ((y : Y) → Guarded (G y)) → Guarded (⊕e Y G)
  <⊕e Y G g m (y , sh) p = g y m sh p

  <&e : {s : S} (Y : Type ℓA) (G : Y → Functor s)
      → ((y : Y) → Guarded (G y)) → Guarded (&e Y G)
  <&e Y G g m sh (y , p) = g y m (sh y) p

  -- ================================================================
  -- THE INTERNAL HYLOMORPHISM, fused.
  --
  -- `mapC` transports a later-function across a CONNECTIVE-form element
  -- directly, by recursion on the description.  No container round trip
  -- appears -- which matters, because `toC ∘ fromC` is only pointwise
  -- the identity, not definitionally so (its ⊗e case rebuilds a lambda
  -- over the arity, and arities have no η).  Since `löb` consumes the
  -- guardedness proof to descend the Acc structure, a stuck round trip
  -- would stall the entire recursion.
  -- ================================================================

  GuardedAt : {s : S} (F : Functor s) (m : GS .fib .carrier s)
            → Sh F m → ℕ → Type ℓPos
  GuardedAt F m sh n = (p : Pos F m sh) → degIx (nx F m sh p) < n

  mapC : {A B : Ix → Type ℓSh} {s : S} (F : Functor s)
         (m : GS .fib .carrier s) (n : ℕ) (t : ⟦ F ⟧c A m)
       → GuardedAt F m (shapeOf F m t) n
       → ((j : Ix) → degIx j < n → A j → B j)
       → ⟦ F ⟧c B m
  mapC ⌜ B ⌝    m n b       g r = b
  mapC (Var x)  m n a       g r = r (x , m) (g tt*) a
  mapC (⊕e Y G) m n (y , t) g r = y , mapC (G y) m n t g r
  mapC (&e Y G) m n h       g r = λ y → mapC (G y) m n (h y) (λ p → g (y , p)) r
  mapC (⊗e o G) m n (sp , h) g r =
    sp , λ a → mapC (G a) _ n (h a) (λ p → g (a , p)) r

  -- the hom of Ix-families
  _⊢ᴵ_ : (A B : Ix → Type ℓSh) → Type (ℓ-max (ℓ-max ℓV ℓX) ℓSh)
  A ⊢ᴵ B = (i : Ix) → A i → B i

  module _ {F : (x : X) → Functor (xs x)} (gF : (x : X) → Guarded (F x))
           {A B : Ix → Type ℓSh}
           (c : CoalgC F A) (alg : AlgC F B) where

    hyloC : A ⊢ᴵ B
    hyloC = löb λ { (x , m) rec ai →
      alg x m (mapC (F x) m (GS .deg (xs x) m) (c x m ai)
                    (λ p → gF x m _ p) (λ j q → rec j q)) }

  -- ================================================================
  -- THE GENERIC ▷-APP.  A `later` may be consumed at any position of a
  -- GUARDED description, because guardedness is precisely the
  -- strictness the `later` demands.  This is the analogue of
  -- `▷-app-NE` (Grammar/Later/Properties.agda) and is what makes a
  -- point-free löb step writable: without it, the only way to use a
  -- `▷` is to apply it to a hand-supplied `<` proof.
  -- ================================================================

  ▷pos : {A : Ix → Type ℓM} {s : S} (F : Functor s) → Guarded F
       → (m : GS .fib .carrier s) (sh : Sh F m) (p : Pos F m sh)
       → ((j : Ix) → degIx j < GS .deg s m → A j) → A (nx F m sh p)
  ▷pos F g m sh p r = r (nx F m sh p) (g m sh p)

