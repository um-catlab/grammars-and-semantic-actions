{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  COMPILER CORRECTNESS IS `SplitPresAt runop`.

  Two ISA promodels over `isaSig` -- a SOURCE machine and a TARGET
  machine -- and a `CarrierMap.Reindex` between them.  Its `hom` has two
  components, one per sort:

      hom prog : SrcProg → TgtProg          the COMPILER
      hom res  : SrcRes  → TgtRes           the state DECODING

  and `TheoryGrammar.CarrierMap`'s per-operation condition `SplitPresAt`
  reads, at the three operations of `isaSig`, as the three things a
  compiler is ever asked to satisfy:

      SplitPresAt _ seqop    compilation is a monoid homomorphism
                             (compiling a concatenation concatenates the
                             compilations)

      SplitPresAt _ sepop    decoding preserves separation -- disjoint
                             source resources decode to disjoint target
                             resources.  This is `LinLam/Codegen`'s
                             `layPres`, i.e. NO ALIASING.

      SplitPresAt _ runop    FORWARD SIMULATION
                             SRun p x y ⟹ TRun (compile p) (dec x) (dec y)

  The third is the theorem every verified compiler proves by hand, and
  here it is the same record field as the other two at a different
  operation.  `Sim` below is its unfolding and `ofSim`/`toSim` are the
  two directions, so the identification is an equivalence of data rather
  than a slogan.

  ------------------------------------------------------------------
  WHICH DIRECTION DOES A PROOF TRAVEL?  -- AND THE ONE THING MISSING.

    * `wpre-pull` needs `SplitPresAt runop` (forward simulation) and
      carries a TARGET-level Hoare triple to a SOURCE-level one.  Prove
      it about the machine, get it about the source, free.

    * `wpre-push` is the COMPILER direction -- a triple proved at the
      source, wanted about the emitted code -- and it needs strictly
      more.  Two things, and naming both is the point of this section:

        BACKWARD SIMULATION.  `CarrierMap.ReflectsSplitAt` is NOT it.
        That record is indexed by the OUTPUT of the splitting, because
        `Fibered .Split` is; `wpre` is a residual and is therefore
        indexed by the INPUT (that is what `Focus` is for).  So the
        framework's reflection condition is focused at the wrong end, and
        `BackSim` below has to be written by hand.  A `ReflectsFocusAt`
        to sit beside `ReflectsSplitAt` is the missing piece, and it is
        missing generically, not just for machines.

        THE SPEC MUST BE IN THE IMAGE OF THE COMPILER (`InImage`).  A
        target-level `wpre` quantifies over EVERY target program
        satisfying the spec, including ones no source program compiles
        to.  Backward simulation says nothing about those.

  "Forward simulation does not transport a specification to the compiled
  code, and backward simulation does" is, here, the observation that
  `push⊗` and `pull⊗` have different hypotheses -- a distinction
  `CarrierMap` draws for reasons that had nothing to do with machines.

  ------------------------------------------------------------------
  PHASE.  Phase 1: `coeEq`, `ofSim`, `toSim`, `wpre-pull`, `wpre-push`.
  Each destructures a `runop`-splitting, which is what a simulation
  argument IS.  `transportTriple` is a composite.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit using (Unit; tt)

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Theories.Monoid
open import TheoryGrammar.Machine.Signature
import TheoryGrammar.Machine.Theory

module TheoryGrammar.Machine.Refine
  -- the SOURCE machine
  (SFib SPFib : Fibered monoidSig ℓ-zero ℓ-zero)
  (SRun : SPFib .carrier tt → SFib .carrier tt → SFib .carrier tt → Type₀)
  -- the TARGET machine
  (TFib TPFib : Fibered monoidSig ℓ-zero ℓ-zero)
  (TRun : TPFib .carrier tt → TFib .carrier tt → TFib .carrier tt → Type₀)
  where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.CarrierMap

module S = TheoryGrammar.Machine.Theory SFib SPFib SRun
module T = TheoryGrammar.Machine.Theory TFib TPFib TRun

private variable ℓA ℓB : Level

-- PRIMITIVE (phase 1): the single coercion used below.  Both endpoints
-- are variables, so the match on `Eq.refl` always unifies -- which is
-- exactly why every use site abstracts its motive explicitly.
coeEq : ∀ {ℓ ℓ'} {X : Type ℓ} (F : X → Type ℓ') {a b : X}
      → a Eq.≡ b → F a → F b
coeEq F Eq.refl z = z

module _ (h : Reindex S.isaFib T.isaFib) where

  module A = Along h

  compile : S.Prog → T.Prog
  compile = h .hom prog

  decode : S.Res → T.Res
  decode = h .hom res

  -- ================================================================
  -- `SplitPresAt _ runop` UNFOLDED IS THE SIMULATION DIAGRAM.
  -- ================================================================

  Sim : Type₀
  Sim = (p : S.Prog) (x y : S.Res) → SRun p x y
      → TRun (compile p) (decode x) (decode y)

  ofSim : Sim → SplitPresAt h runop
  ofSim sim .homSplit y (p , x , r) = compile p , decode x , sim p x y r
  ofSim sim .homParts y (p , x , r) =
    boolΠ {M = λ a → T.isaFib .parts runop (decode y)
                       (compile p , decode x , sim p x y r) a
                     Eq.≡ h .hom (ISASortOf runop a)
                            (S.isaFib .parts runop y (p , x , r) a)}
          Eq.refl Eq.refl

  toSim : SplitPresAt h runop → Sim
  toSim P p x y r =
    coeEq (λ z → TRun (compile p) z (decode y)) (P .homParts y (p , x , r) rslot)
      (coeEq (λ c → TRun c (P .homSplit y (p , x , r) .snd .fst) (decode y))
             (P .homParts y (p , x , r) pslot)
             (P .homSplit y (p , x , r) .snd .snd))

  -- ================================================================
  -- FORWARD SIMULATION TRANSPORTS A TARGET TRIPLE TO A SOURCE TRIPLE.
  --
  -- Read the type: `A.pull` turns a predicate on target states into one
  -- on source states, and this says the weakest-precondition connective
  -- commutes with it, laxly, in the direction forward simulation
  -- licenses.
  -- ================================================================

  module _ (P : SplitPresAt h runop) where

    wpre-pull : (Q : T.Spec ℓA) (B : T.Asrt ℓA)
              → A.pull {s = res} (T.wpre Q B) S.⊢ S.wpre (A.pull {s = prog} Q) (A.pull {s = res} B)
    wpre-pull Q B x w (p , y , r) k =
      w ( P .homSplit y (p , x , r) .fst
        , decode y
        , coeEq (λ z → TRun (P .homSplit y (p , x , r) .fst) z (decode y))
                (P .homParts y (p , x , r) rslot)
                (P .homSplit y (p , x , r) .snd .snd) )
        (λ _ → coeEq Q (Eq.sym (P .homParts y (p , x , r) pslot)) (k tt))

    -- ... and therefore every Hoare triple about the MACHINE is a Hoare
    -- triple about the SOURCE.  Two combinators.
    transportTriple : {A : T.Asrt ℓA} {Q : T.Spec ℓA} {B : T.Asrt ℓA}
                    → T.⟪_⟫_⟪_⟫ A Q B
                    → S.⟪_⟫_⟪_⟫ (A.pull {s = res} A) (A.pull {s = prog} Q)
                                 (A.pull {s = res} B)
    transportTriple {Q = Q} {B = B} t = wpre-pull Q B S.∘g A.pullTerm t

  -- ================================================================
  -- THE COMPILER DIRECTION.
  --
  -- `BackSim` is `ReflectsSplitAt` re-focused at the INPUT -- the shape
  -- `Focus` would give if `CarrierMap` had a `ReflectsFocusAt`.  See the
  -- header: it does not, and that is the one thing this file has to
  -- supply by hand.
  -- ================================================================

  BackSim : Type₀
  BackSim = (p : S.Prog) (x : S.Res) (ŷ : T.Res)
          → TRun (compile p) (decode x) ŷ
          → Σ[ y ∈ S.Res ] (SRun p x y × (decode y Eq.≡ ŷ))

  -- a target spec is in the image of the compiler
  InImage : T.Spec ℓA → Type ℓA
  InImage Q = (p̂ : T.Prog) → Q p̂ → Σ[ p ∈ S.Prog ] ((compile p Eq.≡ p̂) × Q (compile p))

  module _ (bsim : BackSim) where

    wpre-push : (Q : T.Spec ℓA) → InImage Q → (B : T.Asrt ℓA)
              → S.wpre (A.pull {s = prog} Q) (A.pull {s = res} B)
                S.⊢ A.pull {s = res} (T.wpre Q B)
    wpre-push Q im B x v (p̂ , ŷ , r̂) k =
      coeEq B (bs .snd .snd) (v (p , bs .fst , bs .snd .fst) (λ _ → qc))
      where
      ip = im p̂ (k tt)

      p : S.Prog
      p = ip .fst

      e : compile p Eq.≡ p̂
      e = ip .snd .fst

      qc : Q (compile p)
      qc = ip .snd .snd

      bs : Σ[ y ∈ S.Res ] (SRun p x y × (decode y Eq.≡ ŷ))
      bs = bsim p x ŷ (coeEq (λ c → TRun c (decode x) ŷ) (Eq.sym e) r̂)
