{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- COMPILER CORRECTNESS IS `SplitPresAt runop`. -}
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

  -- `SplitPresAt _ runop` UNFOLDED IS THE SIMULATION DIAGRAM.

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

  -- FORWARD SIMULATION TRANSPORTS A TARGET TRIPLE TO A SOURCE TRIPLE.

  module _ (P : SplitPresAt h runop) where

        -- PRIMITIVE (phase 1): `wpre` is a HAND-ROLLED `Σ`, not a composite of
        -- connectives, so there is nothing for the elim rules to act on.  The
        -- fix is to build it from the connectives, not to rewrite this clause.
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

  -- THE COMPILER DIRECTION. `BackSim` is `ReflectsSplitAt` re-focused at
  -- the INPUT -- the shape `Focus` would give if `CarrierMap` had a
  -- `ReflectsFocusAt`.

  BackSim : Type₀
  BackSim = (p : S.Prog) (x : S.Res) (ŷ : T.Res)
          → TRun (compile p) (decode x) ŷ
          → Σ[ y ∈ S.Res ] (SRun p x y × (decode y Eq.≡ ŷ))

  -- a target spec is in the image of the compiler
  InImage : T.Spec ℓA → Type ℓA
  InImage Q = (p̂ : T.Prog) → Q p̂ → Σ[ p ∈ S.Prog ] ((compile p Eq.≡ p̂) × Q (compile p))

  module _ (bsim : BackSim) where

        -- PRIMITIVE (phase 1): `wpre` is a HAND-ROLLED `Σ`, not a composite of
        -- connectives, so there is nothing for the elim rules to act on.  The
        -- fix is to build it from the connectives, not to rewrite this clause.
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
