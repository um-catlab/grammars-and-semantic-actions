{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE HEAP IS LINEAR, AND THAT IS A THEOREM OF THE CALCULUS.

  Two results, and a controlled experiment relating them.

  ------------------------------------------------------------------
  1.  A POINTS-TO CANNOT BE DUPLICATED.
  ------------------------------------------------------------------

  In a separation logic this is normally a property of the MODEL -- one
  proves the semantics is a PCM and derives non-duplication from
  disjointness.  Here it is a one-line composition:

      dup→absurd  =  apart-self ∘g d

  Any map `⌈ s ⌉ ⊢ ⌈ s ⌉ ∗ ⌈ s ⌉` composes with the internal refutation
  `apart-self` to make `⌈ s ⌉` itself absurd, and by the calculus's own
  Yoneda lemma (`⌈⌉-UP : Iso (⌈ a ⌉ ⊢ B) (B a)`) that is already a
  contradiction.  Nothing is matched, no heap is inspected.

  This is worth putting beside the finding in `Ring/Distributivity`.
  There, the forward distributivity map exists for EVERY `A`, because the
  calculus is linear in the INDEX and cartesian in the PAYLOAD -- so a
  duplicability hypothesis on a forward map is vacuous, and contraction
  on payloads is free.  Heaps are where the index-linearity actually
  bites: the resource lives in the index, so non-duplication is a `⊢`
  consequence rather than a side condition.  The two results are the
  negative and positive halves of one observation.

  ------------------------------------------------------------------
  2.  THE CONTROLLED EXPERIMENT.
  ------------------------------------------------------------------

  `Base` gives `cellFib`: the same carrier, the same `parts`, the same
  `Ilv`, with the `u # v` conjunct deleted -- and it HAS a total point.
  So the two promodels differ at exactly one conjunct of one operation,
  and everything else is held fixed.

  The sharp statement is that the SAME generic lemma runs in both
  directions:

      heapFib :  apart-self  (internal)  ⟹  no total point
      cellFib :  cellPoint   (exists)    ⟹  no `apart-self`

  `Generic.no-tuple-point` takes an internal refutation and returns a
  metatheorem; read contrapositively it takes a point and returns the
  IMPOSSIBILITY of the internal refutation.  So no witness has to be
  built by hand on the cell side: the existence of `cellPoint` alone
  rules out the separation statement.  Bags permit duplication, heaps do
  not, and the difference is located at that one conjunct.
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Heap.Linear where

open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Empty as E using (⊥; ⊥*)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib

open import TheoryGrammar.Instances.Heap.Connectives public

-- ==================================================================
-- 1.  NON-DUPLICATION.
-- ==================================================================

module _ (l : Loc) (x : Val) where

  private
    s : Heap
    s = single l x

  -- INTERNAL.  One `∘g`: a duplication map makes the points-to absurd.
  dup→absurd : (⌈ s ⌉ ⊢ (⌈ s ⌉ ∗ ⌈ s ⌉)) → (⌈ s ⌉ ⊢ ⊥G)
  dup→absurd d = apart-self l x ∘g d

  -- ... and the Yoneda lemma of the calculus turns that into a
  -- contradiction, since `⌈ s ⌉ ⊢ B` IS `B s` and `⊥G s` is empty.
  -- The external step is the last one only, exactly as for `noHeapPoint`.
  no-dup : (⌈ s ⌉ ⊢ (⌈ s ⌉ ∗ ⌈ s ⌉)) → ⊥
  no-dup d = E.rec* (⌈⌉-UP {a = s} {B = ⊥G} .Iso.fun (dup→absurd d))

-- ==================================================================
-- 2.  THE CELL FRAGMENT, WHERE DUPLICATION IS FINE.
--
-- `cellFib` is `heapFib` minus disjointness.  Its connectives are
-- qualified, since the unqualified ones are the heap's.
-- ==================================================================

module C = RulesF cellFib

-- the cell fragment's separating conjunction -- the same former, at the
-- promodel that does not require disjointness
_∗c_ : C.TheoryTy ℓ-zero tt → C.TheoryTy ℓ-zero tt → C.TheoryTy ℓ-zero tt
A ∗c B = C.⊗ˢ appop (boolΠ A B)

infixr 20 _∗c_

-- the same respelling coercion as on the heap side: `boolΠ` is stuck at
-- a variable, so the two spellings of one family need bridging
respellC : {u v : Heap} (a : Bool)
         → C.⌈ boolΠ u v a ⌉ C.⊢ boolΠ C.⌈ u ⌉ C.⌈ v ⌉ a
respellC {u} {v} =
  boolΠ {M = λ a → C.⌈ boolΠ u v a ⌉ C.⊢ boolΠ C.⌈ u ⌉ C.⌈ v ⌉ a} C.idg C.idg

-- THE CONTRAST.  No witness is constructed: `cellPoint` alone refutes
-- the possibility of a separation statement, through the very lemma that
-- `noHeapPoint` uses in the other direction.
cell-no-apart : (l : Loc) (x : Val)
              → ((C.⌈ single l x ⌉ ∗c C.⌈ single l x ⌉) C.⊢ C.⊥G) → ⊥
cell-no-apart l x k =
  Generic.no-tuple-point cellFib appop (boolΠ s s)
    ( k C.∘g C.⊗ˢ-map appop {A = λ a → C.⌈ boolΠ s s a ⌉}
                            {B = boolΠ C.⌈ s ⌉ C.⌈ s ⌉} respellC )
    cellPoint
  where s = single l x

-- ==================================================================
-- The experiment, side by side.  Same signature, same carrier, same
-- `parts`, same `Ilv`; one conjunct apart.
--
--     noHeapPoint    : LaxPoint heapFib → ⊥
--     cell-no-apart  : (⌈s⌉ ∗c ⌈s⌉ ⊢ ⊥G) → ⊥
--
-- Adding `u # v` buys the separation theorem and costs the total point;
-- deleting it buys the total point and costs the separation theorem.
-- ==================================================================
