{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  CODEGEN IS NOT A PASS INTO THE TEXT THEORY -- AND THAT IS WHY THERE
  HAS TO BE A MEMORY MODEL.

  ------------------------------------------------------------------
  THE SETTING
  ------------------------------------------------------------------

  `ISA.Pass` makes `text → command` a `Pass`: the semantics of an
  instruction set preserves splittings, which is the intrinsic
  soundness theorem and is proved once for every ISA.

  A COMPILER needs the other link too,

      source → text ,

  and the obvious candidate is `Compile.LinToISA.Codegen.compileU`.
  If it were a `Pass`, then `compileU ⨟P semPass` would be an
  end-to-end verified compiler as a SINGLE object, with `composite` and
  `chainReflective` doing the gluing.

  It is not.  This file proves it, and the shape of the failure is the
  useful part.

  ------------------------------------------------------------------
  THE MEASUREMENT
  ------------------------------------------------------------------

  `SplitPresAtOver` at `appop` demands: from a splitting of the source
  usage, produce a splitting of the emitted TEXT whose two halves are
  the emitted texts of the two halves.  A splitting of text is
  `Split3 p q r`, i.e. `r = p ++ q`, so what is demanded is

      compileU u  =  compileU u₁ ++ compileU u₂     whenever u = u₁ ⊎ u₂.

  And that is FALSE, at the second-smallest example.  Take the
  two-variable scope with the FIRST variable going right:

      u  = true ∷ true ∷ []        compileU u  = putI 0 ∷ putI 1 ∷ []
      u₁ = false ∷ true ∷ []       compileU u₁ = putI 1 ∷ []
      u₂ = true ∷ false ∷ []       compileU u₂ = putI 0 ∷ []

  `compileU u₁ ++ compileU u₂` stores address 1 BEFORE address 0, and
  `compileU u` stores 0 before 1.  Same instructions, same addresses,
  same heap -- different LISTS.

  Note which side is at fault.  `Compile.LinToISA.Codegen.layPres`
  proves the very same map DOES preserve splittings into the HEAP
  promodel, and `Reindex.Sanity.layoutPass` packages that as a `Pass`.
  So the compiler is right and the source is right; what is wrong is
  the target theory.

      A HEAP SPLITTING IS UNORDERED.  CONCATENATION IS ORDERED.

  The free monoid on instructions is too rigid to be the target of a
  compiler out of a theory whose splittings commute.

  ------------------------------------------------------------------
  WHAT THIS FORCES, WHICH IS THE POINT
  ------------------------------------------------------------------

  The repair is not to weaken the statement.  It is to give assembly
  the theory it actually has -- a memory model:

      instructions with DISJOINT FOOTPRINTS COMMUTE.

  Under that equation the two texts above are EQUAL (addresses 0 and 1
  are disjoint), and preservation is restored.  So the memory model is
  not decoration bolted onto the ISA afterwards: it is exactly, and
  only, what is needed for code generation to be a `Pass`.

  That equation is LINEAR -- each side uses each instruction variable
  once -- which is the side condition `TheoryGrammar.Equations` needs.
  `eqn→Iso` therefore lifts it to an ISOMORPHISM OF CONNECTIVES for
  free, and the commuting-conversion structure of assembly comes with
  it rather than being proved instruction by instruction.

  And the disjointness hypothesis is not an extra obligation either:
  `layPres` already turns a source `Use⊎ u₁ u₂ u` into a heap `_#_`,
  so LINEARITY OF THE SOURCE IS WHAT DISCHARGES THE SIDE CONDITION OF
  THE MEMORY-MODEL EQUATION.  The two halves of the compiler meet
  exactly here.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1: a refutation, so it matches on the data it is refuting.
  Compare `Codegen.noPackPres`, `Scope.¬presLam`, `Reindex.LinLam.
  ¬presApp` -- this file is the fourth entry in that table, and the
  first whose failure is repaired by an EQUATION rather than by
  restricting the source.
-}
open import Cubical.Foundations.Prelude

module Compile.LinToISA.NoTextPres where

open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.List using (List; []; _∷_; _++_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Theories.Monoid
open import TheoryGrammar.Reindex.Base
open import TheoryGrammar.Reindex.Pass

open import Compile.LinToISA.Codegen
import TheoryGrammar.Instances.LinLam.Codegen as L

-- ==================================================================
-- §1  THE CANDIDATE CARRIER MAP.
--
-- `compileU`, over the identity signature morphism, from the linear
-- context promodel to program TEXT.
-- ==================================================================

codeOver : ReindexOver (idSigMor monoidSig) L.linFib PT.strFib
codeOver .homO _ u = compileU u

-- ==================================================================
-- §2  THE WITNESS.
-- ==================================================================

u  : L.Usage
u  = true ∷ true ∷ []

uA : L.Usage                      -- takes the SECOND variable
uA = false ∷ true ∷ []

uB : L.Usage                      -- takes the FIRST
uB = true ∷ false ∷ []

spl : L.Use⊎ uA uB u
spl = L.uright (L.uleft L.unil)

wit : L.linFib .Split appop u
wit = uA , uB , spl

-- the three emitted texts, pinned
_ : compileU u  ≡ putI 0 v1 ∷ putI 1 v1 ∷ []
_ = refl

_ : compileU uA ≡ putI 1 v1 ∷ []
_ = refl

_ : compileU uB ≡ putI 0 v1 ∷ []
_ = refl

-- ... and the two orders really are different lists
_ : compileU uA ++ compileU uB ≡ putI 1 v1 ∷ putI 0 v1 ∷ []
_ = refl

-- ==================================================================
-- §3  THE CONCATENATION IS IMPOSSIBLE.
--
-- `cons` would have to unify the head of the left part with the head
-- of the whole -- `putI 1 v1` with `putI 0 v1` -- and `1` is not `0`.
-- ==================================================================

noSplit3 : PT.Split3 (compileU uA) (compileU uB) (compileU u) → ⊥
noSplit3 ()

-- ==================================================================
-- §4  THE REFUTATION.
--
-- `homSplitO` hands us a factorisation of the emitted text;
-- `homPartsO` says its two halves ARE the two emitted texts.
-- Transport the first along the second and §3 applies.
-- ==================================================================

noTextPres : SplitPresAtOver codeOver appop → ⊥
noTextPres P = noSplit3 s₂
  where
  fac : PT.strFib .Split appop (compileU u)
  fac = P .homSplitO u wit

  -- the two halves, and the equations identifying them
  eA : fac .fst Eq.≡ compileU uA
  eA = P .homPartsO u wit true

  eB : fac .snd .fst Eq.≡ compileU uB
  eB = P .homPartsO u wit false

  s₀ : PT.Split3 (fac .fst) (fac .snd .fst) (compileU u)
  s₀ = fac .snd .snd

  s₁ : PT.Split3 (compileU uA) (fac .snd .fst) (compileU u)
  s₁ = Eq.transport (λ z → PT.Split3 z (fac .snd .fst) (compileU u)) eA s₀

  s₂ : PT.Split3 (compileU uA) (compileU uB) (compileU u)
  s₂ = Eq.transport (λ z → PT.Split3 (compileU uA) z (compileU u)) eB s₁

-- ==================================================================
-- §5  ... AND THEREFORE NOT A PASS.
--
-- `Pass` demands preservation at EVERY operation, so one failing
-- operation kills it.  Compare `Reindex.Sanity.layoutPass`, which is
-- the same carrier map into the HEAP theory and is a pass.
-- ==================================================================

asmTheory : Theory ℓ-zero ℓ-zero ℓ-zero ℓ-zero ℓ-zero
asmTheory = theory monoidSig PT.strFib

linTheory : Theory ℓ-zero ℓ-zero ℓ-zero ℓ-zero ℓ-zero
linTheory = theory monoidSig L.linFib

-- the candidate map is not pinned to `codeOver` itself: ANY carrier map
-- that agrees with `compileU` fails, so this is a fact about the
-- function and not about how it was packaged
over : (L.Usage → Program)
     → ReindexOver (idSigMor monoidSig) L.linFib PT.strFib
over f .homO _ = f

noCodePres : (m : ReindexOver (idSigMor monoidSig) L.linFib PT.strFib)
           → m .homO tt Eq.≡ compileU
           → SplitPresAtOver m appop → ⊥
noCodePres m e P =
  noTextPres (Eq.transport (λ f → SplitPresAtOver (over f) appop) e P)

-- A `Pass linTheory asmTheory` over the identity signature morphism is
-- exactly that datum at every operation, so no such pass carries
-- `compileU`.  (A pass over a NON-identity morphism is a different
-- claim and is not addressed here -- the failure measured above is
-- about the two promodels, not about the signature.)
