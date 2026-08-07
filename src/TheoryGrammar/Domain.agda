{-
  THE DOMAIN OF DEFINITION IS A PREDICATE ON TUPLES, NOT ON SLOTS.

  `DomainOf` (§0) reads it slotwise, as `Domˢ o i`, and heaps refute
  that: a partial commutative monoid's partiality is JOINT -- every slot
  is fine and only the COMBINATION fails (`Heap/Located.no-slotwise-L/R`
  against `Connectives.noHeapPoint`).  The joint form is

      Composable o m⃗ = Σ m, Σ sp ∈ Split o m, parts o m sp ≐ m⃗,

  the total space of `⊗ˢ o ⌈ m⃗ ⌉`.  A `LaxPoint` composes EVERY tuple,
  so ONE non-composable tuple refutes every total point
  (`no-point-joint`), and the slotwise theorem is a corollary of that,
  with the same statement.  Surjectivity (`Imageˢ`/`Surjective`) and the
  slotwise notions are inherited from `DomainOf`, not restated.

  MAIN: `DomainOf.{Imgˢ, Domˢ, Fills, no-point, Covering}` (§0);
  `JointDomain.{Composable, no-point-joint, no-point-internal}` (§1+),
  with `joint→dom` and `no-point-from-joint` the two directions across.

  `DomainOf` was moved here from `Instances/Field/Domain.agda`: it is
  parameterised by an arbitrary `Fibered`, mentions no field, and was
  imported from outside the field (here, and by `Heap/Located`), so the
  dependency ran from a generic module INTO an instance directory.

  PRIMITIVE: none.
-}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Domain where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib
open import TheoryGrammar.Decidable.Additive

private variable ℓS ℓ ℓ' ℓX ℓP ℓA : Level

-- ==================================================================
-- 0.  IMAGE AND DOMAIN OF AN OPERATION, ONE SLOT AT A TIME.
--
--     Imgˢ o     at  resultSort o   -- `⊗ˢ o ⊤`: m is an o-composite
--     Domˢ o i   at  sortOf o i     -- x occurs in slot i of one
--
-- `⊗ˢ o ⊤` is the IMAGE, not the domain: `Covering` (surjectivity of the
-- point) is what makes it `⊤` (`covering→img`/`img→covering`), and a
-- total nullary operation already fails it.  `no-point` reads `Domˢ` one
-- SLOT at a time; that reading is complete for a unary partial operation
-- and blind at a heap, so `JointDomain` (§1 onwards) supersedes it with
-- the JOINT form and re-derives this one as a corollary.
-- ==================================================================

module DomainOf {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (Fib : Fibered σ ℓX ℓP) where

  open RulesF Fib public
  open DecAdd (Fib .carrier) public using (¬G_; _⊣⊢_; Dec⟨_⟩; dec-yes; dec-no;
    ⊕-E-at; ⊕-E-atᴰ; dec-elim; Complement; Decision; decide; exclude;
    ¬G-excludes; largest; toDec; contra; &-swap; ¬G-map; dec-map;
    dec-&; dec-⊕; dec-¬)

  -- ================================================================
  -- The two grammars.
  -- ================================================================

  -- the IMAGE of o: which results are o-composites at all.  This is
  -- literally `⊗ˢ o ⊤`, named.
  Imgˢ : (o : σ .ops) → TheoryTy (ℓ-max ℓP ℓ') (σ .resultSort o)
  Imgˢ o = ⊗ˢ o (λ _ → ⊤G)

  -- the DOMAIN of o at slot i: which arguments occur in slot i of some
  -- splitting.  Definable from `Split`/`parts` alone -- no point.
  Domˢ : (o : σ .ops) (i : σ .arities o) → TheoryTy (ℓ-max ℓX ℓP) (σ .sortOf o i)
  Domˢ o i x = Σ[ m ∈ Fib .carrier (σ .resultSort o) ]
               Σ[ sp ∈ Fib .Split o m ] (Fib .parts o m sp i Eq.≡ x)

  -- transport of splittings along an `Eq`, so nothing below uses a Path
  -- where the index has to reduce
  splitEq : (o : σ .ops) {m n : Fib .carrier (σ .resultSort o)}
          → m Eq.≡ n → Fib .Split o m → Fib .Split o n
  splitEq o Eq.refl sp = sp

  -- ================================================================
  -- WHAT A TOTAL POINT FORCES.
  -- ================================================================

  -- A `Fills o i` denotes a way to complete a tuple around slot `i`:
  -- given an element for that slot, values for all the others.  Trivial
  -- for a unary operation; for a wider one it is "pad the rest".  The
  -- law is what makes it a completion rather than an arbitrary tuple,
  -- and it is exactly what turns a bad ELEMENT into a bad TUPLE in
  -- `no-point-from-joint`.
  record Fills (o : σ .ops) (i : σ .arities o) : Type (ℓ-max ℓ' ℓX) where
    field
      -- the completed tuple
      pad   : Fib .carrier (σ .sortOf o i)
             → (a : σ .arities o) → Fib .carrier (σ .sortOf o a)
      -- ... which really does put `x` at slot `i`
      pad-i : (x : Fib .carrier (σ .sortOf o i)) → pad x i ≡ x

  open Fills public

  -- THEOREM.  A total point makes every fillable slot TOTAL: its domain
  -- grammar is ⊤.  (`split` supplies the splitting, `parts-split` says
  -- the slot really holds what you put there.)
  point→dom : (P : LaxPoint Fib) (o : σ .ops) (i : σ .arities o)
            → Fills o i → ⊤G ⊢ Domˢ o i
  point→dom P o i F x _ =
      P .op o (F .pad x)
    , P .split o (F .pad x)
    , Eq.pathToEq (funExt⁻ (P .parts-split o (F .pad x)) i ∙ F .pad-i x)

  -- CONTRAPOSITIVE, and the whole point of the split record: an
  -- INTERNAL refutation at one element of a fillable slot refutes every
  -- total point.  Nothing here is specific to inversion.
  no-point : (o : σ .ops) (i : σ .arities o) → Fills o i
           → (x : Fib .carrier (σ .sortOf o i))
           → (Domˢ o i ⊢ ¬G ⌈ x ⌉) → LaxPoint Fib → ⊥
  no-point o i F x k P = E.rec* (k x (point→dom P o i F x tt) Eq.refl)

  -- THEOREM.  A total point puts every composite in the image -- but
  -- only the composites: this is a map at `op o m⃗`, not at every m.
  point→img : (P : LaxPoint Fib) (o : σ .ops)
              (m⃗ : (a : σ .arities o) → Fib .carrier (σ .sortOf o a))
            → Imgˢ o (P .op o m⃗)
  point→img P o m⃗ = P .split o m⃗ , λ _ → tt

  -- ================================================================
  -- WHEN IS `⊗ˢ o ⊤` THE UNIT?  Exactly when o is surjective.
  -- ================================================================

  Covering : (P : LaxPoint Fib) (o : σ .ops) → Type (ℓ-max ℓ' ℓX)
  Covering P o = (m : Fib .carrier (σ .resultSort o))
               → Σ[ m⃗ ∈ ((a : σ .arities o) → Fib .carrier (σ .sortOf o a)) ]
                 (P .op o m⃗ Eq.≡ m)

  covering→img : (P : LaxPoint Fib) (o : σ .ops) → Covering P o → ⊤G ⊢ Imgˢ o
  covering→img P o cov m _ =
    splitEq o (cov m .snd) (P .split o (cov m .fst)) , λ _ → tt

  -- the converse needs `Honest`, and needs it for the same reason
  -- `Bridge` does: a splitting must recompose to the thing it splits.
  img→covering : (P : LaxPoint Fib) → Honest P → (o : σ .ops)
               → (⊤G ⊢ Imgˢ o) → Covering P o
  img→covering P hon o f m =
    Fib .parts o m (f m tt .fst) , hon o m (f m tt .fst)

-- ==================================================================
-- 1.  THE JOINT READING.
-- ==================================================================

module JointDomain {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (Fib : Fibered σ ℓX ℓP) where

  open RulesF Fib public
  open DecAdd (Fib .carrier) public using (¬G_)

  -- The slotwise reading, and the two surjectivity notions, inherited
  -- rather than restated -- only `Imgˢ`/`Covering` change name.
  open DomainOf Fib public
    using (Domˢ; Fills; pad; pad-i; point→dom; splitEq)
    renaming (Imgˢ to Imageˢ; Covering to Surjective;
              point→img to point→image;
              covering→img to surjective→image;
              img→covering to image→surjective;
              no-point to no-point-slotwise)

  -- ================================================================
  -- JOINT COMPOSABILITY.
  -- ================================================================

  -- an argument tuple for o
  Tuple : (o : σ .ops) → Type (ℓ-max ℓ' ℓX)
  Tuple o = (a : σ .arities o) → Fib .carrier (σ .sortOf o a)

  -- INTERNAL: "this result is a composite of exactly this tuple".  The
  -- payload is pointwise `Eq`, i.e. a representable at each slot, which
  -- is what makes this a connective of the calculus rather than an
  -- equation between two functions.
  Composableᴳ : (o : σ .ops) → Tuple o
              → TheoryTy (ℓ-max ℓP (ℓ-max ℓ' ℓX)) (σ .resultSort o)
  Composableᴳ o m⃗ = ⊗ˢ o (λ a → ⌈ m⃗ a ⌉)

  -- ... and the domain of definition itself: the tuple composes SOMEWHERE.
  Composable : (o : σ .ops) → Tuple o → Type (ℓ-max ℓX (ℓ-max ℓP ℓ'))
  Composable o m⃗ = Σ[ m ∈ Fib .carrier (σ .resultSort o) ] Composableᴳ o m⃗ m

  -- ================================================================
  -- WHAT A TOTAL POINT FORCES -- and the contrapositive.
  -- ================================================================

  -- THEOREM.  A total point composes every tuple.  Note the absence of
  -- any `Fills` hypothesis: there is no slot to pad around.
  point→composable : (P : LaxPoint Fib) (o : σ .ops) (m⃗ : Tuple o)
                   → Composable o m⃗
  point→composable P o m⃗ =
      P .op o m⃗
    , P .split o m⃗
    , λ a → Eq.pathToEq (funExt⁻ (P .parts-split o m⃗) a)

  -- THE THEOREM.  A single non-composable tuple refutes every total
  -- point.  Both known partial algebras factor through this.
  no-point-joint : (o : σ .ops) (m⃗ : Tuple o)
                 → (Composable o m⃗ → ⊥) → LaxPoint Fib → ⊥
  no-point-joint o m⃗ k P = k (point→composable P o m⃗)

  -- ... in the form instances actually use: the refutation is a MAP OF
  -- THE CALCULUS out of the tensor of representables.  (This is
  -- `Heap/Connectives.Generic.no-tuple-point`, hoisted upstream where it
  -- belongs and generalised in the levels.)
  no-point-internal : (o : σ .ops) (m⃗ : Tuple o)
                    → (Composableᴳ o m⃗ ⊢ ⊥G) → LaxPoint Fib → ⊥
  no-point-internal o m⃗ k =
    no-point-joint o m⃗ (λ c → E.rec* (k (c .fst) (c .snd)))

  -- ================================================================
  -- HOW THE THREE NOTIONS RELATE.
  -- ================================================================

  -- (1) JOINT ⟹ SLOTWISE, at every slot.  This is a projection: the
  -- payload at slot i IS the witness `Domˢ o i` asks for.
  joint→dom : (o : σ .ops) (m⃗ : Tuple o) (i : σ .arities o)
            → Composable o m⃗ → Domˢ o i (m⃗ i)
  joint→dom o m⃗ i (m , sp , h) = m , sp , h i

  -- (2) JOINT ⟹ the result is in the IMAGE.  Forgetting the payload.
  joint→image : (o : σ .ops) (m⃗ : Tuple o)
              → Composable o m⃗ → Σ[ m ∈ Fib .carrier (σ .resultSort o) ] Imageˢ o m
  joint→image o m⃗ (m , sp , _) = m , sp , λ _ → tt

  -- (3) THE SLOTWISE THEOREM IS A COROLLARY.  `Fills` is exactly what
  -- turns a bad ELEMENT into a bad TUPLE; `no-point-slotwise` (i.e.
  -- `DomainOf.no-point`, §0) is recovered with the same statement.
  no-point-from-joint : (o : σ .ops) (i : σ .arities o) → Fills o i
                      → (x : Fib .carrier (σ .sortOf o i))
                      → (Domˢ o i ⊢ ¬G ⌈ x ⌉) → LaxPoint Fib → ⊥
  no-point-from-joint o i F x k =
    no-point-joint o (F .pad x)
      (λ c → E.rec* (k (F .pad x i) (joint→dom o (F .pad x) i c)
                       (Eq.pathToEq (F .pad-i x))))

  -- ... and it really is the SAME statement, not a lookalike: the old
  -- proof inhabits the new one's type.  Nothing was weakened; only the
  -- proof now factors through the joint lemma.
  no-point-same-statement :
      ((o : σ .ops) (i : σ .arities o) → Fills o i
     → (x : Fib .carrier (σ .sortOf o i))
     → (Domˢ o i ⊢ ¬G ⌈ x ⌉) → LaxPoint Fib → ⊥)
  no-point-same-statement = no-point-slotwise

  -- (4) THE CONVERSE OF (1) FAILS.  It cannot be proved here, so it is
  -- NAMED here and refuted at an instance: `Heap/Joint.no-slotwise-joint`
  -- exhibits a tuple every slot of which is in `Domˢ` -- `Located`'s
  -- `dom-total-L/R` -- and which does not compose.  Surjectivity is no
  -- help either: `Located.img-total` holds at the same instance.
  SlotwiseSuffices : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓX ℓP)))
  SlotwiseSuffices = (o : σ .ops) (m⃗ : Tuple o)
                   → ((i : σ .arities o) → Domˢ o i (m⃗ i)) → Composable o m⃗

  -- the one implication that IS available in that direction, for the
  -- record: a total point gives both, independently.
  point→slotwise : (P : LaxPoint Fib) → SlotwiseSuffices
  point→slotwise P o m⃗ _ = point→composable P o m⃗

-- ==================================================================
-- SANITY: a TOTAL algebra composes everything, so nothing above is
-- vacuous.  `canonical`/`canonicalPoint` are `Fibered`'s own.
-- ==================================================================

canonicalComposable : {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (M : Model σ ℓX)
                      (o : σ .ops)
                      (m⃗ : JointDomain.Tuple (canonical M) o)
                    → JointDomain.Composable (canonical M) o m⃗
canonicalComposable M = JointDomain.point→composable (canonical M) (canonicalPoint M)
