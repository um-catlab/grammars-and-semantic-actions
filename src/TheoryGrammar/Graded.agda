{-
  CHECK 3: local contractivity, and the hylomorphism.

  Checks 1 and 2 (algebras and coalgebras internal to families over `Ix`)
  are in TheoryGrammar.Inductive: `⟦_⟧`, `Fmap`, `Alg`, `Coalg`.  This
  file supplies the third, and with it the recursive-coalgebra story.

  The point of the file is that for a CONTAINER functor, local
  contractivity is not an extra structure you must supply -- it is
  DERIVABLE from a single lemma:

      Guarded F  =  every position's next index is STRICTLY smaller.

  Because `Fmap h (sh , f) = (sh , h ∘ f)` does not touch shapes, the
  strength `Hδ : ▷(A ⇒ B) → (H A ⇒ H B)` -- ccl's `▷HomActionFam` -- is
  forced, and `Guarded` is precisely the side condition that lets you
  apply the later-function at each position.  That is `mapGuarded` below,
  and it IS the strength.

  Guardedness itself decomposes: `Guarded≤` ("no growth") holds for every
  description former including `Var`, and the single STRICT step comes
  from `⊗e` at a proper splitting.  So the shape of the argument is

      Var contributes equality,  ⊗e contributes the strict decrease,

  which is the generic form of "the recursive call is on a proper part".
  `Var` at the top of a description is exactly what fails to be guarded --
  that is left recursion, correctly rejected.

  The degree is ℕ.  Every instance in ccl and gsa grades to ℕ via
  `pullbackWFOrder ℕWFOrder`, so this loses nothing today; the order can
  be made abstract later if a lexicographic instance needs it.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Graded where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Induction.WellFounded

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive

private variable ℓS ℓ ℓ' ℓX ℓP ℓA ℓM ℓN ℓV : Level

-- ==================================================================
-- A promodel with a grading.
-- ==================================================================

record GradedFib {S : Type ℓS} (σ : SortedSig S ℓ ℓ') ℓX ℓP
  : Type (ℓ-max ℓS (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max (ℓ-suc ℓX) (ℓ-suc ℓP))))) where
  field
    fib : Fibered σ ℓX ℓP
    deg : (s : S) → fib .carrier s → ℕ

    -- Properness is DATA ON THE SPLITTING.  Phrasing it this way dodges
    -- "some slot other than a", and hence dodges needing
    -- `Discrete (arities o)` -- the same problem `Focus` was introduced
    -- to avoid.  For strings, `Proper appop w sp false` says the left
    -- part is nonempty.
    Proper : (o : σ .ops) (m : fib .carrier (σ .resultSort o))
           → fib .Split o m → σ .arities o → Type ℓP

    -- slots never grow ...
    deg≤ : (o : σ .ops) (m : fib .carrier (σ .resultSort o))
           (sp : fib .Split o m) (a : σ .arities o)
         → deg _ (fib .parts o m sp a) ≤ deg _ m

    -- ... and a proper slot strictly shrinks
    deg< : (o : σ .ops) (m : fib .carrier (σ .resultSort o))
           (sp : fib .Split o m) (a : σ .arities o)
         → Proper o m sp a
         → deg _ (fib .parts o m sp a) < deg _ m

open GradedFib public

-- ==================================================================
-- THE GRADING, UNBUNDLED -- a structure OVER a promodel, exactly as
-- `Focus` is, and for the same reason.
--
-- `GradedFib` bundles the promodel, which makes one thing UNSTATABLE:
-- "for every grading of THIS promodel".  That quantification is what the
-- obstruction theorems need -- `Instances/Group/NoGrading` wants to say
-- ℤ admits only the degenerate grading, and with the bundled record it
-- had to unbundle into four module parameters and rebuild `GradedFib` by
-- hand at every use.  Both the group and the ring instance did exactly
-- that, independently, which is the signal that the record is shaped
-- wrong.
--
-- Note this does NOT say "ℤ has no grading": the trivial grading
-- (`deg = const 0`, `Proper = ⊥`) always exists, so the honest theorem is
-- RIGIDITY -- that it is the only one.  Stating rigidity is precisely
-- what needs the quantifier this record provides.
-- ==================================================================

record Grading {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (Fib : Fibered σ ℓX ℓP)
  : Type (ℓ-max ℓS (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓX (ℓ-suc ℓP))))) where
  field
    deg    : (s : S) → Fib .carrier s → ℕ
    Proper : (o : σ .ops) (m : Fib .carrier (σ .resultSort o))
           → Fib .Split o m → σ .arities o → Type ℓP
    deg≤   : (o : σ .ops) (m : Fib .carrier (σ .resultSort o))
             (sp : Fib .Split o m) (a : σ .arities o)
           → deg _ (Fib .parts o m sp a) ≤ deg _ m
    deg<   : (o : σ .ops) (m : Fib .carrier (σ .resultSort o))
             (sp : Fib .Split o m) (a : σ .arities o)
           → Proper o m sp a
           → deg _ (Fib .parts o m sp a) < deg _ m

open Grading public

-- The two presentations are the same data, and both directions are
-- definitional -- there is no content here, only shape.
gradingOf : {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
            (GS : GradedFib σ ℓX ℓP) → Grading (GS .fib)
gradingOf GS .deg    = GS .deg
gradingOf GS .Proper = GS .Proper
gradingOf GS .deg≤   = GS .deg≤
gradingOf GS .deg<   = GS .deg<

graded : {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
         (Fib : Fibered σ ℓX ℓP) → Grading Fib → GradedFib σ ℓX ℓP
graded Fib G .fib    = Fib
graded Fib G .deg    = G .deg
graded Fib G .Proper = G .Proper
graded Fib G .deg≤   = G .deg≤
graded Fib G .deg<   = G .deg<

-- ==================================================================
-- ▷, next, löb -- first-order, exactly as Grammar/Later/Ordered.agda
-- hand-collapses ccl's presheaf ▷.
-- ==================================================================

-- ==================================================================
-- THE LATER MODALITY, GENERIC IN THE ORDER.
--
-- The header above says "the order can be made abstract later if a
-- lexicographic instance needs it".  Doing it now costs nothing: ▷,
-- `next` and `löb` never mention the degree, only the relation and its
-- well-foundedness.  The graded order below is then one instance, and
-- `Grammar/Later/Ordered.agda` -- which is generic in a `WFOrder` and
-- instantiated at the suffix and infix orders -- is another.
-- ==================================================================
module WFLater {ℓI ℓR : Level} {I : Type ℓI} (_≺_ : I → I → Type ℓR)
               (≺-wf : WellFounded _≺_) where

  ▷ : {ℓM : Level} → (I → Type ℓM) → I → Type (ℓ-max ℓI (ℓ-max ℓR ℓM))
  ▷ A i = (j : I) → j ≺ i → A j

  next : {ℓM : Level} {A : I → Type ℓM} → ((i : I) → A i) → (i : I) → ▷ A i
  next f i j _ = f j

  löb : {ℓM : Level} {A : I → Type ℓM}
      → ((i : I) → ▷ A i → A i) → (i : I) → A i
  löb {A = A} step = WFI.induction ≺-wf λ i rec → step i (λ j q → rec j q)

-- A FINER order gives a WEAKER modality: fewer `j ≺ i` means fewer
-- assumptions available in the löb step.  So `Later/Infix`'s `▷ⁱ` --
-- the proper-substring order -- is IMPLIED by the graded `▷`, since a
-- proper infix is strictly shorter but not conversely.  That is why
-- `Instances/Strings/CYK.agda` needs no infix modality: the CYK
-- recursion is available already, with a stronger hypothesis.
▷-mono : {ℓI ℓR ℓR' ℓM : Level} {I : Type ℓI}
         {_≺_ : I → I → Type ℓR} {_≺'_ : I → I → Type ℓR'}
       → ({i j : I} → i ≺' j → i ≺ j)
       → {A : I → Type ℓM} {i : I}
       → ((j : I) → j ≺ i → A j) → ((j : I) → j ≺' i → A j)
▷-mono sub r j q = r j (sub q)

module Guard {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
             (GS : GradedFib σ ℓX ℓP) (ℓA : Level)
             (X : Type ℓV) (xs : X → S) where

  open Ind (GS .fib) ℓA X xs public

  degIx : Ix → ℕ
  degIx (x , m) = GS .deg (xs x) m

  _≺_ : Ix → Ix → Type
  i ≺ j = degIx i < degIx j

  private
    ≺-wf : WellFounded _≺_
    ≺-wf i = go (degIx i) (<-wellfounded (degIx i)) i refl
      where
        go : (n : ℕ) → Acc _<_ n → (j : Ix) → degIx j ≡ n → Acc _≺_ j
        go n (acc h) j p =
          acc λ k q → go (degIx k) (h (degIx k) (subst (degIx k <_) p q)) k refl

  -- the graded order is one instance of `WFLater`; ▷/next/löb come
  -- from there rather than being re-defined here
  open WFLater _≺_ ≺-wf public

  -- ================================================================
  -- Guardedness.
  -- ================================================================

  Guarded≤ : {s : S} → Functor s → Type (ℓ-max ℓX (ℓ-max ℓSh ℓPos))
  Guarded≤ {s} F = (m : GS .fib .carrier s) (sh : Sh F m) (p : Pos F m sh)
                 → degIx (nx F m sh p) ≤ GS .deg s m

  Guarded : {s : S} → Functor s → Type (ℓ-max ℓX (ℓ-max ℓSh ℓPos))
  Guarded {s} F = (m : GS .fib .carrier s) (sh : Sh F m) (p : Pos F m sh)
                → degIx (nx F m sh p) < GS .deg s m

  Guarded→≤ : {s : S} {F : Functor s} → Guarded F → Guarded≤ F
  Guarded→≤ g m sh p = <-weaken (g m sh p)

  -- every former is non-increasing ...
  ≤⌜⌝ : {s : S} (A : FibNotation.TheoryTy (GS .fib) ℓA s) → Guarded≤ ⌜ A ⌝
  ≤⌜⌝ A m sh ()

  ≤Var : (x : X) → Guarded≤ (Var x)
  ≤Var x m sh p = ≤-refl

  ≤⊕e : {s : S} (Y : Type ℓA) (G : Y → Functor s)
      → ((y : Y) → Guarded≤ (G y)) → Guarded≤ (⊕e Y G)
  ≤⊕e Y G g m (y , sh) p = g y m sh p

  ≤&e : {s : S} (Y : Type ℓA) (G : Y → Functor s)
      → ((y : Y) → Guarded≤ (G y)) → Guarded≤ (&e Y G)
  ≤&e Y G g m sh (y , p) = g y m (sh y) p

  ≤⊗e : (o : σ .ops) (G : (a : σ .arities o) → Functor (σ .sortOf o a))
      → ((a : σ .arities o) → Guarded≤ (G a)) → Guarded≤ (⊗e o G)
  ≤⊗e o G g m (sp , sh) (a , p) =
    ≤-trans (g a _ (sh a) p) (GS .deg≤ o m sp a)

  -- ... and ⊗e at a proper splitting is the one STRICT step.
  <⊗e : (o : σ .ops) (G : (a : σ .arities o) → Functor (σ .sortOf o a))
      → ((a : σ .arities o) → Guarded≤ (G a))
      → ((m : GS .fib .carrier (σ .resultSort o)) (sp : GS .fib .Split o m)
         (sh : (a : σ .arities o) → Sh (G a) (GS .fib .parts o m sp a))
         (a : σ .arities o) → Pos (G a) _ (sh a) → Proper GS o m sp a)
      → Guarded (⊗e o G)
  <⊗e o G g pr m (sp , sh) (a , p) =
    ≤<-trans (g a _ (sh a) p) (GS .deg< o m sp a (pr m sp sh a p))

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
