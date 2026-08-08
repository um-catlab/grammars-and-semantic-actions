{- DEFINITIONAL β AND η FOR THE MULTIPLICATIVES. In TheoryGrammar.Base the
   convolution is defined by an equation, ⊗[ o ] A m = Σ[ m⃗ ] (op o m⃗
   Eq.≡ m) × (∀ a → A a (m⃗ a)), and the currying isomorphism gets β
   definitionally (`sec = refl`) but NOT η: `ret` has to pattern-match
   `Eq.refl`. -}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Fibered where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥*)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base

private variable ℓS ℓ ℓ' ℓX ℓP ℓA ℓB ℓC ℓY : Level

-- A `Fibered`: a model presented with its splittings as DATA rather
-- than as an equation.

record Fibered {S : Type ℓS} (σ : SortedSig S ℓ ℓ') ℓX ℓP
  : Type (ℓ-max ℓS (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max (ℓ-suc ℓX) (ℓ-suc ℓP))))) where
  field
    carrier : S → Type ℓX
    -- ways of seeing m as an o-composite, indexed BY THE OUTPUT
    Split   : (o : σ .ops) → carrier (σ .resultSort o) → Type ℓP
    parts   : (o : σ .ops) (m : carrier (σ .resultSort o))
            → Split o m → (a : σ .arities o) → carrier (σ .sortOf o a)

open Fibered public

-- IS THE SPLITTING A RELATION, OR A STRUCTURE? `Split o m` is Type-valued,
-- deliberately: a parse is DATA, not a truth value.

PartsFaithful : {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (Fib : Fibered σ ℓX ℓP)
              → σ .ops → Type (ℓ-max ℓ' (ℓ-max ℓX ℓP))
PartsFaithful {σ = σ} Fib o =
  (m : Fib .carrier (σ .resultSort o)) (sp sp' : Fib .Split o m)
  → Fib .parts o m sp ≡ Fib .parts o m sp' → sp ≡ sp'

-- A CHOSEN TOTAL POINT, separately. `op`, `split` and `parts-split` used
-- to sit in the record above.

record LaxPoint {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (Fib : Fibered σ ℓX ℓP)
  : Type (ℓ-max ℓS (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓX ℓP)))) where
  field
    op      : (o : σ .ops)
            → ((a : σ .arities o) → Fib .carrier (σ .sortOf o a))
            → Fib .carrier (σ .resultSort o)
    -- every tuple splits its own composite ...
    split   : (o : σ .ops)
              (m⃗ : (a : σ .arities o) → Fib .carrier (σ .sortOf o a))
            → Fib .Split o (op o m⃗)
    -- ... and does so at the tuple you started with
    parts-split : (o : σ .ops)
                  (m⃗ : (a : σ .arities o) → Fib .carrier (σ .sortOf o a))
                → Fib .parts o (op o m⃗) (split o m⃗) ≡ m⃗

open LaxPoint public

-- the underlying model -- available only WITH a total point
⌊_⌋ : {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} {Fib : Fibered σ ℓX ℓP}
    → LaxPoint Fib → Model σ ℓX
⌊_⌋ {Fib = Fib} P .Model.carrier = Fib .carrier
⌊_⌋ {Fib = Fib} P .Model.op = P .op

-- The connectives over a `Fibered`.  NOTE what this module does NOT
-- take: no `LaxPoint`, so everything below is available to a partial
-- algebra.

module FibNotation {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (Fib : Fibered σ ℓX ℓP) where

  open CarrierNotation (Fib .carrier) public

  -- the convolution, with NO proof component
  ⊗ˢ : (o : σ .ops)
     → ((a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
     → TheoryTy (ℓ-max ℓP (ℓ-max ℓ' ℓA)) (σ .resultSort o)
  ⊗ˢ o A m = Σ[ sp ∈ Fib .Split o m ] ((a : σ .arities o) → A a (Fib .parts o m sp a))

  -- THE DEPENDENT TENSOR. `⊗ˢ` above takes a payload SLOTWISE: one grammar
  -- per slot, each reading only its own part.

  Parts : (o : σ .ops) → Type (ℓ-max ℓ' ℓX)
  Parts o = (a : σ .arities o) → Fib .carrier (σ .sortOf o a)

  ⊗ˢᵈ : (o : σ .ops) → (Parts o → Type ℓA)
      → TheoryTy (ℓ-max ℓP ℓA) (σ .resultSort o)
  ⊗ˢᵈ o P m = Σ[ sp ∈ Fib .Split o m ] P (Fib .parts o m sp)

  -- the slotwise tensor IS the dependent one at a slotwise payload
  ⊗ˢ≡ : (o : σ .ops)
        (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
      → ⊗ˢ o A ≡ ⊗ˢᵈ o (λ ps → (a : σ .arities o) → A a (ps a))
  ⊗ˢ≡ o A = refl

  -- `P` is EXPLICIT throughout: it is grammar-valued, and such arguments
  -- cannot be recovered from the unfolded type (`⊗ˢᵈ o P m` is a `Σ`,
  -- which pins nothing).
  module _ (o : σ .ops) (P : Parts o → Type ℓA) where

    ⊗ˢᵈ-I : (m : Fib .carrier (σ .resultSort o)) (sp : Fib .Split o m)
          → P (Fib .parts o m sp) → ⊗ˢᵈ o P m
    ⊗ˢᵈ-I m sp p = sp , p

    ⊗ˢᵈ-E : {B : TheoryTy ℓB (σ .resultSort o)}
          → ((m : Fib .carrier (σ .resultSort o)) (sp : Fib .Split o m)
             → P (Fib .parts o m sp) → B m)
          → ⊗ˢᵈ o P ⊢ B
    ⊗ˢᵈ-E f m (sp , p) = f m sp p

  -- ... AND `⊕ᴰ` COMMUTES WITH IT.

  module _ (o : σ .ops) (Y : Type ℓY) (P : Y → Parts o → Type ℓA) where

    ⊕ᴰ-⊗ˢᵈ-out : ⊕ᴰ Y (λ y → ⊗ˢᵈ o (P y)) ⊢ ⊗ˢᵈ o (λ ps → Σ[ y ∈ Y ] P y ps)
    ⊕ᴰ-⊗ˢᵈ-out m (y , sp , p) = sp , y , p

    ⊕ᴰ-⊗ˢᵈ-in : ⊗ˢᵈ o (λ ps → Σ[ y ∈ Y ] P y ps) ⊢ ⊕ᴰ Y (λ y → ⊗ˢᵈ o (P y))
    ⊕ᴰ-⊗ˢᵈ-in m (sp , y , p) = y , sp , p

    -- and the round trips, both `refl`
    ⊕ᴰ-⊗ˢᵈ-β : (m : Fib .carrier (σ .resultSort o))
               (t : ⊕ᴰ Y (λ y → ⊗ˢᵈ o (P y)) m)
             → ⊕ᴰ-⊗ˢᵈ-in m (⊕ᴰ-⊗ˢᵈ-out m t) ≡ t
    ⊕ᴰ-⊗ˢᵈ-β m t = refl

    ⊕ᴰ-⊗ˢᵈ-η : (m : Fib .carrier (σ .resultSort o))
               (t : ⊗ˢᵈ o (λ ps → Σ[ y ∈ Y ] P y ps) m)
             → ⊕ᴰ-⊗ˢᵈ-out m (⊕ᴰ-⊗ˢᵈ-in m t) ≡ t
    ⊕ᴰ-⊗ˢᵈ-η m t = refl

  MultiHomˢ : (o : σ .ops)
            → ((a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
            → TheoryTy ℓB (σ .resultSort o)
            → Type (ℓ-max ℓX (ℓ-max ℓP (ℓ-max ℓ' (ℓ-max ℓA ℓB))))
  MultiHomˢ o A B =
    (m : Fib .carrier (σ .resultSort o)) (sp : Fib .Split o m)
    → ((a : σ .arities o) → A a (Fib .parts o m sp a))
    → B m

  module _ (o : σ .ops)
           {A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a)}
           {B : TheoryTy ℓB (σ .resultSort o)} where

    curryˢ : (⊗ˢ o A ⊢ B) → MultiHomˢ o A B
    curryˢ f m sp h = f m (sp , h)

    uncurryˢ : MultiHomˢ o A B → (⊗ˢ o A ⊢ B)
    uncurryˢ g m (sp , h) = g m sp h

    -- THEOREM.  Both directions of the multiplicative universal
    -- property hold DEFINITIONALLY.

    ⊗-UP-β : (g : MultiHomˢ o A B) → curryˢ (uncurryˢ g) ≡ g
    ⊗-UP-β g = refl

    ⊗-UP-η : (f : ⊗ˢ o A ⊢ B) → uncurryˢ (curryˢ f) ≡ f
    ⊗-UP-η f = refl                              -- <-- was a pattern match

    ⊗ˢ-UP : Iso (⊗ˢ o A ⊢ B) (MultiHomˢ o A B)
    ⊗ˢ-UP .Iso.fun = curryˢ
    ⊗ˢ-UP .Iso.inv = uncurryˢ
    ⊗ˢ-UP .Iso.sec = ⊗-UP-β
    ⊗ˢ-UP .Iso.ret = ⊗-UP-η

  -- The residual at a slot, likewise proof-free.  Its elimination rule
  -- needs no pattern match either.

  ⊸ˢ : (o : σ .ops) (i : σ .arities o)
     → ((a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
     → TheoryTy ℓB (σ .resultSort o)
     → TheoryTy (ℓ-max ℓX (ℓ-max ℓP (ℓ-max ℓ' (ℓ-max ℓA ℓB)))) (σ .sortOf o i)
  ⊸ˢ o i A B x =
    (m : Fib .carrier (σ .resultSort o)) (sp : Fib .Split o m)
    → (Fib .parts o m sp i ≡ x)
    → ((a : σ .arities o) → A a (Fib .parts o m sp a))
    → B m

  module _ (o : σ .ops) (i : σ .arities o)
           {A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a)}
           {B : TheoryTy ℓB (σ .resultSort o)} where

    -- generic ⊸-app / ⟜-app: no transport, no match
    ⊸ˢ-app : (A i ⊢ ⊸ˢ o i A B) → (⊗ˢ o A ⊢ B)
    ⊸ˢ-app g m (sp , h) = g (Fib .parts o m sp i) (h i) m sp refl h

-- The equational presentation is the FREE choice of Split.

canonical : {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} → Model σ ℓX → Fibered σ ℓX (ℓ-max ℓ' ℓX)
canonical {σ = σ} M .carrier = M .Model.carrier
canonical {σ = σ} M .Split o m =
  Σ[ m⃗ ∈ ((a : σ .arities o) → M .Model.carrier (σ .sortOf o a)) ] (M .Model.op o m⃗ Eq.≡ m)
canonical {σ = σ} M .parts o m sp = sp .fst

-- ... and a model is exactly what points it.
canonicalPoint : {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (M : Model σ ℓX)
               → LaxPoint (canonical M)
canonicalPoint {σ = σ} M .op = M .Model.op
canonicalPoint {σ = σ} M .split o m⃗ = m⃗ , Eq.refl
canonicalPoint {σ = σ} M .parts-split o m⃗ = refl

-- WHEN ⊗ˢ AND ⊗[ o ] AGREE. `⊗ˢ` convolves over the SPLITTINGS; `⊗[ o ]`
-- (Base.agda) convolves over the OPERATION, carrying `op o m⃗ Eq.≡ m`.

Honest : {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} {Fib : Fibered σ ℓX ℓP}
       → LaxPoint Fib → Type (ℓ-max ℓ (ℓ-max ℓX ℓP))
Honest {σ = σ} {Fib = Fib} P =
  (o : σ .ops) (m : Fib .carrier (σ .resultSort o)) (sp : Fib .Split o m)
  → P .op o (Fib .parts o m sp) Eq.≡ m

-- the equational presentation is the FREE honest choice: honesty there
-- is just the proof component of a splitting, handed back
canonicalHonest : {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (M : Model σ ℓX)
                → Honest (canonicalPoint M)
canonicalHonest M o m sp = sp .snd

module Bridge {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} {Fib : Fibered σ ℓX ℓP}
              (P : LaxPoint Fib) (hon : Honest P) where

  open FibNotation Fib
  open Notation ⌊ P ⌋ using (⊗[_])

  module _ (o : σ .ops)
           {A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a)} where

    -- forward: read off the parts, and honesty supplies the equation
    ⊗ˢ→⊗ : ⊗ˢ o A ⊢ ⊗[ o ] A
    ⊗ˢ→⊗ m (sp , h) = Fib .parts o m sp , hon o m sp , h

    -- backward: `split` supplies the splitting and `parts-split` moves
    -- the payload onto it.  Matching `Eq.refl` is what makes the index a
    -- variable, so nothing here transports along the OUTER equation.
    ⊗→⊗ˢ : ⊗[ o ] A ⊢ ⊗ˢ o A
    ⊗→⊗ˢ .(P .op o m⃗) (m⃗ , Eq.refl , h) =
        P .split o m⃗
      , λ a → subst (A a) (sym (λ κ → P .parts-split o m⃗ κ a)) (h a)

-- DEFINITIONAL β/η FOR THE RESIDUAL. `⊸ˢ` above still carries a `parts o m
-- sp i ≡ x` component, so it has the same disease one level down: a Path
-- is not a record, so the residual's η needs a match.

record Focus {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
             (Fib : Fibered σ ℓX ℓP) (o : σ .ops) (i : σ .arities o)
  : Type (ℓ-max ℓS (ℓ-max ℓ (ℓ-max (ℓ-suc ℓ') (ℓ-max ℓX (ℓ-suc ℓP))))) where
  field
    -- splittings viewed from slot i, indexed by what sits in slot i:
    -- the generic one-hole context / zipper.
    SplitAt  : Fib .carrier (σ .sortOf o i) → Type ℓP
    whole    : {x : Fib .carrier (σ .sortOf o i)} → SplitAt x
             → Fib .carrier (σ .resultSort o)
    -- THE COMPLEMENT OF SLOT i, supplied as data.  This is what lets the
    -- residual omit the focused argument without needing `Discrete
    -- (arities o)` to compute "every slot except i".
    Rest     : Type ℓ'
    restOf   : Rest → σ .arities o
    restSlot : {x : Fib .carrier (σ .sortOf o i)} → SplitAt x
             → (r : Rest) → Fib .carrier (σ .sortOf o (restOf r))

open Focus public

module FocusNotation {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
                     {Fib : Fibered σ ℓX ℓP}
                     {o : σ .ops} {i : σ .arities o} (Φ : Focus Fib o i) where

  open FibNotation Fib

  -- The residual.  Note A is used only at `restOf r` -- the focused slot
  -- is genuinely absent, which is what makes this a residual and not a
  -- reassociated hom.
  ⊸ᶠ : ((a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
     → TheoryTy ℓB (σ .resultSort o)
     → TheoryTy (ℓ-max ℓP (ℓ-max ℓ' (ℓ-max ℓA ℓB))) (σ .sortOf o i)
  ⊸ᶠ A B x = (sa : Φ .SplitAt x)
           → ((r : Φ .Rest) → A (Φ .restOf r) (Φ .restSlot sa r))
           → B (Φ .whole sa)

  module _ {A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a)}
           {B : TheoryTy ℓB (σ .resultSort o)} where

    -- the hom-set it classifies: focused argument supplied ONCE
    FocusedHom : Type (ℓ-max ℓX (ℓ-max ℓP (ℓ-max ℓ' (ℓ-max ℓA ℓB))))
    FocusedHom = (x : Fib .carrier (σ .sortOf o i)) (sa : Φ .SplitAt x)
               → A i x
               → ((r : Φ .Rest) → A (Φ .restOf r) (Φ .restSlot sa r))
               → B (Φ .whole sa)

    ⊸ᶠ-lam : FocusedHom → (A i ⊢ ⊸ᶠ A B)
    ⊸ᶠ-lam f x ai sa h = f x sa ai h

    ⊸ᶠ-app : (A i ⊢ ⊸ᶠ A B) → FocusedHom
    ⊸ᶠ-app g x sa ai h = g x ai sa h

    ⊸ᶠ-β : (f : FocusedHom) → ⊸ᶠ-app (⊸ᶠ-lam f) ≡ f
    ⊸ᶠ-β f = refl

    ⊸ᶠ-η : (g : A i ⊢ ⊸ᶠ A B) → ⊸ᶠ-lam (⊸ᶠ-app g) ≡ g
    ⊸ᶠ-η g = refl

    ⊸ᶠ-UP : Iso (A i ⊢ ⊸ᶠ A B) FocusedHom
    ⊸ᶠ-UP .Iso.fun = ⊸ᶠ-app
    ⊸ᶠ-UP .Iso.inv = ⊸ᶠ-lam
    ⊸ᶠ-UP .Iso.sec = ⊸ᶠ-β
    ⊸ᶠ-UP .Iso.ret = ⊸ᶠ-η
