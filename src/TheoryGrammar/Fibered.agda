{-
  DEFINITIONAL β AND η FOR THE MULTIPLICATIVES.

  In TheoryGrammar.Base the convolution is defined by an equation,

      ⊗[ o ] A m = Σ[ m⃗ ] (op o m⃗ Eq.≡ m) × (∀ a → A a (m⃗ a)),

  and the currying isomorphism gets β definitionally (`sec = refl`) but
  NOT η: `ret` has to pattern-match `Eq.refl`.  The obstruction is
  precise and is worth naming, because it is one component:

      Σ has definitional η.  Eq._≡_ is `data`, so it does not.

  So the η-failure is not about ⊗ being a positive connective -- ⊕ᴰ is
  also a Σ and it DOES get definitional η.  It is caused solely by
  carrying a proof term that has no η.

  The fix is to stop carrying the proof.  Index the splitting by the
  OUTPUT and expose the components as projections:

      Split : (o) → carrier (resultSort o) → Type
      parts : (o) (m) → Split o m → (a : arities o) → carrier (sortOf o a)

  Then

      ⊗[ o ] A m = Σ[ sp ∈ Split o m ] (∀ a → A a (parts o m sp a))

  is a Σ of two components neither of which needs matching to eliminate,
  and BOTH β and η become `refl`.  Proved below as `⊗-UP-β` / `⊗-UP-η`.

  This is the same change that removes the green slime (an equation whose
  left side is a defined function applied to a bound variable) -- the two
  problems have one cause and one fix.  `canonical` shows the equational
  presentation is the special case where `Split o m` is the type of
  tuples together with a proof, i.e. it is `Split` chosen freely.
-}
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

-- ==================================================================
-- A promodel: a model presented with its splittings as DATA rather
-- than as an equation.
-- ==================================================================

record Fibered {S : Type ℓS} (σ : SortedSig S ℓ ℓ') ℓX ℓP
  : Type (ℓ-max ℓS (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max (ℓ-suc ℓX) (ℓ-suc ℓP))))) where
  field
    carrier : S → Type ℓX
    -- ways of seeing m as an o-composite, indexed BY THE OUTPUT
    Split   : (o : σ .ops) → carrier (σ .resultSort o) → Type ℓP
    parts   : (o : σ .ops) (m : carrier (σ .resultSort o))
            → Split o m → (a : σ .arities o) → carrier (σ .sortOf o a)

open Fibered public

-- ==================================================================
-- A CHOSEN TOTAL POINT, separately.
--
-- `op`, `split` and `parts-split` used to sit in the record above.  They
-- do not belong there, and the reason is sharp: `⊗ˢ`, `MultiHomˢ`, `⊸ᶠ`
-- -- the whole multiplicative layer -- mention only `Split` and `parts`.
-- The three totality fields are load-bearing for nothing except
-- asserting themselves, while excluding every PARTIAL algebra: separation
-- logic, and anything where combining requires disjoint resources.
--
-- Split out, they are exactly a lax point: an operation together with a
-- proof that the relation CONTAINS its graph.  `Bags` is the instance
-- showing the containment must be allowed to be strict -- `Ilv u v w`
-- does not imply `u ++ v ≡ w` -- so this is never an isomorphism.
-- ==================================================================

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

-- ==================================================================
-- The connectives over a promodel.  NOTE what this module does NOT
-- take: no `LaxPoint`, so everything below is available to a partial
-- algebra.
-- ==================================================================

module FibNotation {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (Fib : Fibered σ ℓX ℓP) where

  open CarrierNotation (Fib .carrier) public

  -- the convolution, with NO proof component
  ⊗ˢ : (o : σ .ops)
     → ((a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
     → TheoryTy (ℓ-max ℓP (ℓ-max ℓ' ℓA)) (σ .resultSort o)
  ⊗ˢ o A m = Σ[ sp ∈ Fib .Split o m ] ((a : σ .arities o) → A a (Fib .parts o m sp a))

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

    -- ==============================================================
    -- THEOREM.  Both directions of the multiplicative universal
    -- property hold DEFINITIONALLY.
    -- ==============================================================

    ⊗-UP-β : (g : MultiHomˢ o A B) → curryˢ (uncurryˢ g) ≡ g
    ⊗-UP-β g = refl

    ⊗-UP-η : (f : ⊗ˢ o A ⊢ B) → uncurryˢ (curryˢ f) ≡ f
    ⊗-UP-η f = refl                              -- <-- was a pattern match

    ⊗ˢ-UP : Iso (⊗ˢ o A ⊢ B) (MultiHomˢ o A B)
    ⊗ˢ-UP .Iso.fun = curryˢ
    ⊗ˢ-UP .Iso.inv = uncurryˢ
    ⊗ˢ-UP .Iso.sec = ⊗-UP-β
    ⊗ˢ-UP .Iso.ret = ⊗-UP-η

  -- ================================================================
  -- The residual at a slot, likewise proof-free.  Its elimination rule
  -- needs no pattern match either.
  -- ================================================================

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

-- ==================================================================
-- The equational presentation is the FREE choice of Split.
-- ==================================================================

canonical : {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} → Model σ ℓX → Fibered σ ℓX (ℓ-max ℓ' ℓX)
canonical {σ = σ} M .carrier = M .Model.carrier
canonical {σ = σ} M .Split o m =
  Σ[ m⃗ ∈ ((a : σ .arities o) → M .Model.carrier (σ .sortOf o a)) ] (M .Model.op o m⃗ Eq.≡ m)
canonical {σ = σ} M .parts o m sp = sp .fst

-- ... and a model is exactly what points it.  Splitting the record makes
-- this direction visible: `canonical` needs only the carrier and the
-- operation to build the SPLITTINGS, and the total point is then a
-- separate, automatic consequence.
canonicalPoint : {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (M : Model σ ℓX)
               → LaxPoint (canonical M)
canonicalPoint {σ = σ} M .op = M .Model.op
canonicalPoint {σ = σ} M .split o m⃗ = m⃗ , Eq.refl
canonicalPoint {σ = σ} M .parts-split o m⃗ = refl

-- ==================================================================
-- WHEN ⊗ˢ AND ⊗[ o ] AGREE.
--
-- `⊗ˢ` convolves over the SPLITTINGS; `⊗[ o ]` (Base.agda) convolves
-- over the OPERATION, carrying `op o m⃗ Eq.≡ m`.  Programs are written
-- against the first, `ChangeOfTheory` and `Equations` are stated at the
-- second, and both `Instances/Nat/Length` and `Instances/Semimodule/
-- Graded` had to write the translation by hand.  It belongs here, and
-- the hypothesis it needs is exactly one the record does NOT have:
--
--     HONEST -- every splitting of `m` really does recompose to `m`.
--
-- `parts-split` is the converse (every tuple splits its own composite).
-- Honesty is emphatically NOT derivable, and `Bags` is the counterexample
-- the rest of this development already turns on: `Ilv u v w` does not
-- imply `u ++ v ≡ w`, so an interleaving splitting recomposes to a
-- PERMUTATION of `w`.  That is the whole reason a promodel is allowed to
-- be strictly larger than the graph of its point.  So it stays a
-- hypothesis -- `Representable` already takes it, under the name
-- `unsplit`.
-- ==================================================================

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

-- ==================================================================
-- DEFINITIONAL β/η FOR THE RESIDUAL.
--
-- `⊸ˢ` above still carries a `parts o m sp i ≡ x` component, so it has
-- the same disease one level down: a Path is not a record, so the
-- residual's η needs a match.  The same cure applies -- have the
-- promodel supply the FOCUSED splittings (the zipper view: a splitting
-- seen from slot i, with slot i's content as the index) rather than
-- reconstructing them with an equation.  Then the residual is a plain Π
-- and BOTH laws are refl.
-- ==================================================================

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
