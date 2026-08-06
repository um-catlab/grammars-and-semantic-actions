{-
  THE FOUR MODES.

  Each is `Core.Mode` at a context substrate and a leaf.  Nothing else
  varies: `Uses`, `check`, `checkAST` and `accepts` are inherited.

      ordered   Concat      (free monoid)            leaf  ⌈n⌉
      linear    Interleave  (free comm. monoid)      leaf  ⌈n⌉
      affine    Interleave  (the SAME substrate)     leaf  ⌈n⌉ ⊗ᶜ ⊤
      relevant  Overlap     (+ idempotence)          leaf  ⌈n⌉

  So weakening is a MODALITY on the leaf (`- ⊗ᶜ ⊤`, "a variable may
  consume slack"), while exchange and contraction are properties of the
  substrate's `Split`.  That asymmetry is the one real finding: three of
  the four modes are the same grammar at three substrates, and affine is
  the same grammar at the linear substrate with one modality inserted.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Modes.Instances where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Unit
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.List.Properties using (discreteList)
open import Cubical.Relation.Nullary.Base using (Discrete)

open import TheoryGrammar.Base
open import TheoryGrammar.Substrate
open import TheoryGrammar.Decidable
open import TheoryGrammar.Decidable.Splittings
open import TheoryGrammar.Decidable.Representable
open import TheoryGrammar.Instances.Lambda.Modes.Ctx
open import TheoryGrammar.Instances.Lambda.Modes.Core
open import TheoryGrammar.Instances.Lambda.Modes.Concat
open import TheoryGrammar.Instances.Lambda.Modes.Interleave
open import TheoryGrammar.Instances.Lambda.Modes.Overlap

module Modes (Name : Type₀) (_≟_ : Discrete Name) where

  sing : Name → List Name
  sing n = n ∷ []

  -- external decidability, used ONLY to build `dec-⌈⌉`
  discreteCtx : Discrete (List Name)
  discreteCtx = discreteList _≟_

  module Cc = Concat Name
  module Il = Interleave Name
  module Ov = Overlap Name

  module CcR = DecRep ⌊ Cc.sub ⌋
  module IlR = DecRep ⌊ Il.sub ⌋
  module OvR = DecRep ⌊ Ov.sub ⌋

  private
    module OrdC = Core Name Cc.sub Cc.dec sing
    module LinC = Core Name Il.sub Il.dec sing
    module RelC = Core Name Ov.sub Ov.dec sing

  -- ================================================================
  -- ORDERED: concatenation, no exchange.
  -- ================================================================
  module Ord where
    open OrdC public

    Lf : Name → CtxG
    Lf n = ⌈ sing n ⌉

    decLf : (n : Name) → ⊤G ⊢ Dec⟨ Lf n ⟩
    decLf n = CcR.dec-⌈⌉ discreteCtx (sing n)

    open Mode Lf decLf public

  -- ================================================================
  -- LINEAR: interleaving.  Exchange, no weakening, no contraction.
  -- ================================================================
  module Lin where
    open LinC public

    Lf : Name → CtxG
    Lf n = ⌈ sing n ⌉

    decLf : (n : Name) → ⊤G ⊢ Dec⟨ Lf n ⟩
    decLf n = IlR.dec-⌈⌉ discreteCtx (sing n)

    open Mode Lf decLf public

  -- ================================================================
  -- AFFINE: the LINEAR substrate, with weakening as a leaf modality.
  -- `⌈n⌉ ⊗ᶜ ⊤` is "a use of n, plus any slack" -- and slack is exactly
  -- what weakening licenses.  Its decision is `dec-⊗ˢ` again.
  -- ================================================================
  module Aff where
    open LinC public

    Lf : Name → CtxG
    Lf n = ⌈ sing n ⌉ ⊗ᶜ ⊤G

    decLf : (n : Name) → ⊤G ⊢ Dec⟨ Lf n ⟩
    decLf n Γ _ =
      Il.dec .dec-⊗ˢ mul (λ b → if b then ⌈ sing n ⌉ else ⊤G) Γ
        λ { sp true  → IlR.dec-⌈⌉ discreteCtx (sing n) _ tt
          ; sp false → dec-⊤ _ tt }

    open Mode Lf decLf public

  -- ================================================================
  -- RELEVANT: interleaving WITH SHARING.  Contraction, no weakening.
  -- ================================================================
  module Rel where
    open RelC public

    Lf : Name → CtxG
    Lf n = ⌈ sing n ⌉

    decLf : (n : Name) → ⊤G ⊢ Dec⟨ Lf n ⟩
    decLf n = OvR.dec-⌈⌉ discreteCtx (sing n)

    open Mode Lf decLf public
