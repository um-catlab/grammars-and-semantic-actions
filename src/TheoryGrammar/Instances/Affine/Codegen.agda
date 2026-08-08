{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  DOES PHASE 4 SURVIVE AN AFFINE SOURCE?  NO -- AND THE REASON IS NOT
  ALIASING.

  `LinLam/Codegen.agda` is the headline of the pipeline.  Its claim:

      the source's MISSING constructor manufactures the target's
      DISJOINTNESS conjunct,

  so "the code emitted for the two premises of an application does not
  alias" is the pass's TYPE (`SplitPresAt`), not a theorem about it.
  `Instances/Affine/` replaces `Use⊎` by `Aff⊎`, which differs by one
  constructor:

      adrop : Aff⊎ u v w → Aff⊎ (false ∷ u) (false ∷ v) (true ∷ w)

  The obvious worry is that affinity breaks no-aliasing.  IT DOES NOT,
  and this file separates the two questions, because they come apart
  cleanly and only one of them fails.

  RESULT 1 (POSITIVE).  NO-ALIASING IS UNTOUCHED.

      apartLayA : Aff⊎ u₁ u₂ u → (i : ℕ) → lay i u₁ # lay i u₂

  The proof is `Codegen.apartLay` with ONE extra clause, and that clause
  is `askip`'s verbatim: `adrop` puts `false` in both slots, so both
  parts skip the position and the recursion is the same.  Disjointness
  came from the absent `(true,true)` clause, and `Base.noDupAff` /
  `Base.affDiag` say affinity did not restore it.  So the half of the
  Phase 4 claim that everyone would worry about is exactly the half that
  is insensitive to the change.

  Note also `affLayPresNil` below: `SplitPresAt` still holds at `nilop`.
  The failure is localised at ONE operation, which is what `CarrierMap`
  is for -- compare `Passes/Inline.agda`'s `¬subSplitPres` at `varOp`.

  RESULT 2 (NEGATIVE).  SPLIT PRESERVATION FAILS ON *COVERAGE*.

      noAffPres : ¬ SplitPresAt affLayoutMap appop

  `Ilv` is EXACT interleaving -- the whole is precisely the merge of the
  parts.  Under `adrop` the whole owns a variable that neither part
  owns, so the emitted heap has a cell that neither emitted region has,
  and no `Ilv` can cover it.  The witness is as small as it could be:

      u  = true ∷ []          layout u  = single 0 v1
      u₁ = u₂ = false ∷ []    layout u₁ = layout u₂ = []
      s  = adrop anil

  and `Ilv [] [] (single 0 v1)` has NO constructor (`noIlvGap`).  The
  refutation is stated against an ARBITRARY `homSplit`, not against
  `ilvLay` -- it is not that the obvious translation fails, it is that
  none exists: `homParts` pins both regions to `[]` and then the
  interleaving field is uninhabited.

  WHAT THIS MEANS.  The two failures a compiler could have here are

      ALIASING     two live variables emitted to one location
      LEAKING      a location emitted for a variable nobody consumes

  and Phase 4's `SplitPresAt` conflates them, because `Ilv u v w × u # v`
  asserts both at once.  A linear source rules out both, which is why
  the phase reads so cleanly.  An affine source rules out only the
  first, and `SplitPresAt` is too strong to express that.  So the result
  is a REFINEMENT of the pipeline's central claim rather than a defect
  in it:

      no-aliasing is bought by the absent (true,true) clause;
      no-leaking is bought by the absent (false,false,true) clause,

  and they are separate purchases.  `LinLam` happens to make both.

  THE TWO REPAIRS, and why the second is the interesting one.

  (a) WEAKEN THE TARGET.  Replace `Ilv` by a sub-interleaving that
      permits a cell in the whole belonging to neither part.  Then
      `ilvLayA` goes through with `adrop ↦ leak` and the phase is
      recovered verbatim.  This is a leak-permitting separation logic
      -- morally "the frame rule without the frame being accounted
      for".  NOT DONE HERE; it is a heap-side construction and belongs
      in its own instance.

  (b) EMIT A FREE.  Keep the target exact and make the pass emit an
      explicit deallocation at each `adrop`, so the dropped cell is
      consumed by the generated code rather than by the relation.  This
      is the interesting one, because it says something real: an affine
      source language FORCES the compiler to emit drop code, and the
      forcing is visible as the failure of `SplitPresAt` above.  That is
      the type-theoretic content of Rust's `Drop::drop` being emitted
      code rather than a typing rule -- and here it is not an analogy
      but the exact obstruction, at one constructor.
      NOT DONE HERE: it needs a command language on the target side, and
      `Heap/Hoare.agda` is where that would live.

  PRIMITIVE (phase 1): `apartLayA`, `emptyLayA`, `noIlvGap`.  The layout
  itself is NOT redefined -- `CG.lay` is imported, so this file compares
  the affine source against the SAME allocator the linear phase uses.
  Writing a second copy would have made the comparison vacuous.
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Affine.Codegen where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib
open import TheoryGrammar.CarrierMap

-- the SOURCE theory: the affine `Fibered`
open import TheoryGrammar.Instances.Affine.Base public

-- the TARGET theory, qualified
import TheoryGrammar.Instances.Heap.Base as H

-- the LINEAR phase 4, qualified -- imported for its allocator and its
-- apartness bookkeeping, so that the comparison is against the same
-- `lay` and not a re-derived twin
import TheoryGrammar.Instances.LinLam.Codegen as CG

-- §1  THE ALLOCATOR IS THE LINEAR ONE, UNCHANGED.

layout : Usage → H.Heap
layout = CG.layout

affLayoutMap : Reindex affFib H.heapFib
affLayoutMap .hom _ = layout

-- §2 RESULT 1: NO-ALIASING SURVIVES. `Codegen.apartLay` with one extra
-- clause, and the clause is `askip`'s.

-- PRIMITIVE (phase 1)
apartLayA : ∀ {u₁ u₂ u} → Aff⊎ u₁ u₂ u → (i : ℕ)
          → CG.lay i u₁ H.# CG.lay i u₂
apartLayA anil               i = tt
apartLayA (aleft  {v = v} s) i =
  CG.freshLay v (suc i) i (CG.below-suc i) , apartLayA s (suc i)
apartLayA (aright {u = u} s) i =
  CG.#-cons-r (CG.lay (suc i) u) _ i H.v1
              (CG.freshLay u (suc i) i (CG.below-suc i))
              (apartLayA s (suc i))
apartLayA (askip s)          i = apartLayA s (suc i)
apartLayA (adrop s)          i = apartLayA s (suc i)   -- <-- THE NEW CLAUSE

-- the nullary operation: an exhausted affine usage still lays out to
-- the empty heap, so `SplitPresAt` holds there.
emptyLayA : (u : Usage) (i : ℕ) → Empty u → H.IsNil (CG.lay i u)
emptyLayA []          i e = tt
emptyLayA (true  ∷ u) i e = e            -- both sides are `⊥`
emptyLayA (false ∷ u) i e = emptyLayA u (suc i) e

-- THEOREM.  The pass IS split-preserving at `nilop`.  The failure below
-- is localised at exactly one operation.
affLayPresNil : SplitPresAt affLayoutMap nilop
affLayPresNil .homSplit u e = emptyLayA u 0 e
affLayPresNil .homParts u e ()

-- §3  RESULT 2: SPLIT PRESERVATION FAILS AT `appop`, ON COVERAGE.

-- THE GAP.  A heap with a cell, interleaved from two EMPTY heaps: no
-- constructor of `Ilv` produces a cell the parts do not have.
-- PRIMITIVE (phase 1)
noIlvGap : H.Ilv [] [] ((0 , H.v1) ∷ []) → ⊥
noIlvGap ()

-- the smallest affine splitting that is not linear: one variable, owned
-- by the whole and claimed by neither premise
dropW : Usage
dropW = true ∷ []

dropSp : AffSplit appop dropW
dropSp = (false ∷ []) , (false ∷ []) , adrop anil

-- both premises emit the empty heap ...
_ : layout (false ∷ []) ≡ []
_ = refl

-- ... and the whole emits one cell
_ : layout dropW ≡ (0 , H.v1) ∷ []
_ = refl

-- THEOREM. NO SPLIT-PRESERVING LAYOUT OF THE AFFINE `Fibered`.
noAffPres : SplitPresAt affLayoutMap appop → ⊥
noAffPres P =
  go (P .homSplit dropW dropSp)
     (P .homParts dropW dropSp true)
     (P .homParts dropW dropSp false)
  where
  go : (hs : H.HeapSplit appop (layout dropW))
     → hs .fst Eq.≡ [] → hs .snd .fst Eq.≡ [] → ⊥
  go (h₁ , h₂ , il , d) Eq.refl Eq.refl = noIlvGap il

-- COROLLARY.  ... hence no `Reindex`-with-`SplitPresAt` at every
-- operation, which is what Phase 4 delivers linearly (`CG.layPres`).
noAffPresAll : ((o : MonOp) → SplitPresAt affLayoutMap o) → ⊥
noAffPresAll f = noAffPres (f appop)

-- §4 THE DIAGNOSIS, side by side. The linear phase's two ingredients, at
-- the affine splitting: `apartLayA` -- SURVIVES (§2).

-- the linear phase 4 still holds, cited so the contrast cannot drift
linLayPres : (o : CG.MonOp) → SplitPresAt CG.layoutMap o
linLayPres = CG.layPres

-- and the disjointness half holds affinely, at the same witness where
-- coverage fails: the two emitted regions really are apart
_ : CG.lay 0 (false ∷ []) H.# CG.lay 0 (false ∷ [])
_ = apartLayA (adrop anil) 0
