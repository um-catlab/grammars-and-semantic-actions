{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{- ALIGNED STRING PAIRS: the comma object of two string `Fibered` over
   `length`. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Strings.Aligned (In Out : Type₀) where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit
open import Cubical.Data.Empty as E using (⊥)
open import Cubical.Data.Nat
open import Cubical.Data.List
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Theories.Monoid
open import TheoryGrammar.Fibered
open import TheoryGrammar.CarrierMap
open import TheoryGrammar.Gluing

import TheoryGrammar.Instances.Strings.Base as StB
module I = StB In
module O = StB Out

import TheoryGrammar.Instances.Nat.LengthFib as LF
module LI = LF In
module LO = LF Out

-- THE COMMA OBJECT.

open Pullback I.strFib O.strFib LI.lenIx LO.lenIx public

-- two strings of equal length, over different alphabets
Aligned : Type₀
Aligned = glue .carrier tt

-- The input side determines the output side: `lenPres` pushes the input
-- splitting down to `ℕ`, `lenReflects` lifts it back up the output leg.
alignedDetermined : Determined
alignedDetermined = pullbackDetermined LI.lenPres LO.lenReflects

-- THE TESTS.  Abstract letters on both sides -- the alignment never
-- inspects them, which is the point.

module _ (x y : In) (p q : Out) where

  private
    w2 : I.String
    w2 = x ∷ y ∷ []

    v2 : O.String
    v2 = p ∷ q ∷ []

    -- `Eq.refl` typechecks only because both lengths reduce to `2`
    g2 : Aligned
    g2 = w2 , v2 , Eq.refl

    -- cut the INPUT tape after one letter ...
    cut1 : I.strFib .Split appop w2
    cut1 = (x ∷ []) , (y ∷ []) , I.cons I.nil

    -- ... and read off what the OUTPUT tape does
    out1 : O.strFib .Split appop v2
    out1 = alignedDetermined appop g2 cut1 .fst

  -- THE SYNCHRONISATION.  Nothing said the output should cut here; it
  -- follows from `cutS` recursing in step with the addition.
  _ : out1 .fst ≡ p ∷ []
  _ = refl

  _ : out1 .snd .fst ≡ q ∷ []
  _ = refl

  private
    -- the degenerate cut, as a second data point
    cut0 : I.strFib .Split appop w2
    cut0 = [] , w2 , I.nil

    out0 : O.strFib .Split appop v2
    out0 = alignedDetermined appop g2 cut0 .fst

  _ : out0 .fst ≡ []
  _ = refl

  _ : out0 .snd .fst ≡ p ∷ q ∷ []
  _ = refl

  -- the relatedness datum -- a composite of `homParts`, `coeParts` and
  -- the reflection -- collapses, so the glued splitting is not inert
  _ : alignedDetermined appop g2 cut1 .snd true ≡ Eq.refl
  _ = refl

  _ : alignedDetermined appop g2 cut1 .snd false ≡ Eq.refl
  _ = refl

  -- ... and the glued splitting has BOTH tapes' halves at each slot.

  private
    glued : glue .Split appop g2
    glued = cut1 , alignedDetermined appop g2 cut1

  _ : glue .parts appop g2 glued true .fst ≡ x ∷ []
  _ = refl

  _ : glue .parts appop g2 glued true .snd .fst ≡ p ∷ []
  _ = refl

  _ : glue .parts appop g2 glued false .fst ≡ y ∷ []
  _ = refl

  _ : glue .parts appop g2 glued false .snd .fst ≡ q ∷ []
  _ = refl

  -- EVERY INPUT-SIDE PROGRAM LIFTS. `Determined` gives `π₁` reflection,
  -- hence `Along.pull⊗`: an input-side `⊗ˢ` becomes a glued `⊗ˢ`, and the
  -- output tape is cut to match.

  private
    TT : (a : MonAr appop) → I.TheoryTy ℓ-zero tt
    TT _ = I.⊤G

    inTensor : I.⊗ˢ appop TT w2
    inTensor = cut1 , λ _ → tt

    lifted : G.⊗ˢ appop (λ a → pull₁ (TT a)) g2
    lifted = pull⊗₁ appop (determined→reflects alignedDetermined appop)
                    {B = TT} g2 inTensor

  _ : lifted .fst .fst ≡ cut1
  _ = refl

  _ : lifted .fst .snd .fst .fst ≡ p ∷ []
  _ = refl

  _ : lifted .fst .snd .fst .snd .fst ≡ q ∷ []
  _ = refl

  -- `zip` ON REAL PAYLOADS. One `⊗ˢ` over the glue yields TWO `⊗ˢ`s, one
  -- per tape -- and they are at the SAME cut, because the cut is the index
  -- rather than a side condition.

  private
    AIn : (a : MonAr appop) → I.TheoryTy ℓ-zero tt
    AIn true  = I.⌈ x ∷ [] ⌉
    AIn false = I.⌈ y ∷ [] ⌉

    BOut : (a : MonAr appop) → O.TheoryTy ℓ-zero tt
    BOut true  = O.⌈ p ∷ [] ⌉
    BOut false = O.⌈ q ∷ [] ⌉

    pay : (a : MonAr appop) → (AIn a ⊛ BOut a) (glue .parts appop g2 glued a)
    pay true  = Eq.refl , Eq.refl
    pay false = Eq.refl , Eq.refl

    zipped : ((I.⊗ˢ appop AIn) ⊛ (O.⊗ˢ appop BOut)) g2
    zipped = zip appop AIn BOut g2 (glued , pay)

  _ : zipped .fst .fst ≡ cut1
  _ = refl

  _ : zipped .snd .fst .fst ≡ p ∷ []
  _ = refl

  _ : zipped .snd .fst .snd .fst ≡ q ∷ []
  _ = refl

  -- AND THE BOUNDARY. `Coherent` -- any two splittings of related wholes
  -- have related parts -- FAILS here, at the very glue that is
  -- `Determined`.

  private
    outCut0 : O.strFib .Split appop v2
    outCut0 = [] , v2 , O.nil

    oneNotZero : (1 Eq.≡ 0) → ⊥
    oneNotZero ()

  notCoherent : Coherent → ⊥
  notCoherent c = oneNotZero (c appop g2 cut1 outCut0 true)
