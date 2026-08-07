{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  A GENUINELY PARTIAL PROMODEL: heaps, and separation logic.

  Every other instance in this tree has a total operation.  Each supplies
  a `Fibered` together with a `LaxPoint`, and each would have worked just
  as well before the two were separated -- so the split that
  `TheoryGrammar.Fibered` argues for is, so far, unexercised.  This file
  is the test.  Its claim is not that heaps are interesting (they are, but
  that is separation logic's business) but that

      RulesF heapFib  works, and  LaxPoint heapFib  is REFUTABLE.

  If both hold, the split delivered what it promised: the multiplicative
  and additive layers really do need only `Split` and `parts`, and the
  three totality fields really were excluding something.

  ------------------------------------------------------------------
  THE CARRIER, AND WHY THIS SHAPE
  ------------------------------------------------------------------

  A heap is an allocation bitmap, `List Bool`: position n says whether
  location n is owned.  This is deliberately the crudest heap there is --
  no values, no addresses -- because the point is the PARTIALITY of
  joining, and values would only add noise.

  The real design decision is `Disj`.  Every instance in this tree gives
  its splittings as an inductive family indexed by the output -- `Split3`
  for strings, `Add3` for ℕ, `Times` for Dirichlet, `Ilv` for bags -- and
  the same works here:

      Disj u v w   =   u and v are disjoint, and their union is w.

  Read the constructors and notice what is ABSENT: there is no clause
  taking `true` on the left and `true` on the right.  THAT missing
  constructor is the partiality, and it is structural.  No equation, no
  proof component, no `Maybe`, nothing to unfold.  `CLAUDE.md` warns
  against carrying a proof in a `Split`; partiality turns out to be one
  more thing you get for free by not carrying one.

  ------------------------------------------------------------------
  WHAT THIS IS, IN THE SEPARATION-LOGIC READING
  ------------------------------------------------------------------

      ⊗ˢ joinOp   is  the separating conjunction  ∗
      ⊸ˢ joinOp   is  the magic wand             ─∗
      ⊗ˢ empOp    is  emp
      ⊗ˢ-map      is  the FRAME RULE

  none of which is new here -- they are the generic connectives of
  `RulesF`, instantiated.  That is the whole content: separation logic is
  what the calculus becomes at a partial promodel, and it costs no new
  infrastructure.
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Heap.Base where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.List
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib

-- ==================================================================
-- The carrier and the signature.
-- ==================================================================

Heap : Type₀
Heap = List Bool

-- The signature of a commutative monoid.  Note it is the SAME signature
-- a total monoid has: partiality is not visible here at all, because a
-- signature only names operations.  It shows up one level down, in what
-- `Split` is willing to produce.
data PcmOp : Type₀ where
  empOp joinOp : PcmOp

PcmAr : PcmOp → Type₀
PcmAr empOp  = ⊥
PcmAr joinOp = Bool

pcmSig : SortedSig Unit ℓ-zero ℓ-zero
pcmSig .ops          = PcmOp
pcmSig .arities      = PcmAr
pcmSig .sortOf _ _   = tt
pcmSig .resultSort _ = tt

-- ==================================================================
-- DISJOINT UNION, as data indexed by the output.
--
-- The four constructors are: both empty; owned on the left; owned on
-- the right; owned by neither.  There is NO fifth taking (true, true).
-- ==================================================================

data Disj : Heap → Heap → Heap → Type₀ where
  dnil : Disj [] [] []
  dl   : ∀ {u v w} → Disj u v w → Disj (true  ∷ u) (false ∷ v) (true  ∷ w)
  dr   : ∀ {u v w} → Disj u v w → Disj (false ∷ u) (true  ∷ v) (true  ∷ w)
  dnone : ∀ {u v w} → Disj u v w → Disj (false ∷ u) (false ∷ v) (false ∷ w)

-- `emp`, as a RECURSIVE predicate rather than an indexed family -- the
-- same choice `IsNil` makes for strings, and for the same reason: every
-- case split then happens on the heap itself.
Emp : Heap → Type₀
Emp []            = Unit
Emp (true  ∷ _)   = ⊥
Emp (false ∷ w)   = Emp w

PcmSplit : (o : PcmOp) → Heap → Type₀
PcmSplit empOp  w = Emp w
PcmSplit joinOp w = Σ[ u ∈ Heap ] Σ[ v ∈ Heap ] Disj u v w

PcmParts : (o : PcmOp) (w : Heap) → PcmSplit o w → PcmAr o → Heap
PcmParts empOp  w sp ()
PcmParts joinOp w (u , v , _) b = if b then u else v

-- ==================================================================
-- THE PROMODEL.  Note what is NOT here: no `op`, no `split`, no
-- `parts-split`.  Before the split of `Fibered` from `LaxPoint` this
-- record could not have been written at all.
-- ==================================================================

heapFib : Fibered pcmSig ℓ-zero ℓ-zero
heapFib .carrier _ = Heap
heapFib .Split     = PcmSplit
heapFib .parts     = PcmParts

-- ... and the whole calculus is available over it.
open RulesF heapFib public

Hp : Type₁
Hp = TheoryTy ℓ-zero tt

-- ==================================================================
-- THE THEOREM.  There is no total point.
--
-- A `LaxPoint` would have to supply a total `op`, and `split` would then
-- have to exhibit a splitting of `op joinOp m⃗` whose parts are `m⃗`.  Take
-- `m⃗` to be two heaps that both own location 0: no constructor of `Disj`
-- applies, so no such splitting exists at any output whatsoever.
--
-- This is the exact analogue of upstream's `heapNoLaxPoint`, and it is
-- what makes the instance a real test rather than a re-labelling: the
-- calculus above is not merely usable without the totality fields, it is
-- usable where they are FALSE.
-- ==================================================================

-- PRIMITIVE (phase 1): two owners of location 0 cannot be joined.
noJoin : (w : Heap) → Disj (true ∷ []) (true ∷ []) w → ⊥
noJoin w ()

¬LaxPointHeap : LaxPoint heapFib → ⊥
¬LaxPointHeap P =
  noJoin (P .op joinOp m⃗)
         (transport (λ i → Disj (uEq i) (vEq i) (P .op joinOp m⃗)) d)
  where
    m⃗ : Bool → Heap
    m⃗ _ = true ∷ []

    u = P .split joinOp m⃗ .fst
    v = P .split joinOp m⃗ .snd .fst
    d = P .split joinOp m⃗ .snd .snd

    -- `parts-split` says the splitting's parts really are `m⃗`
    uEq : u ≡ true ∷ []
    uEq i = P .parts-split joinOp m⃗ i true

    vEq : v ≡ true ∷ []
    vEq i = P .parts-split joinOp m⃗ i false
