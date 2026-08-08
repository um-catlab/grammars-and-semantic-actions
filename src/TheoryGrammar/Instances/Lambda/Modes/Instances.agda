{- THE FOUR MODES. Each is `Core.Mode` at a context `Fibered` and a leaf,
   so each exports `Uses`, `check`, `checkAST`, `accepts` and `acceptsLf`
   unchanged, and supplies only `Lf` (its leaf grammar) and `decLf` (that
   leaf's decision). -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Modes.Instances where

open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.List.Properties using (discreteList)
open import Cubical.Data.Unit
open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary.Base using (Discrete)

open import TheoryGrammar.Base
open import TheoryGrammar.Decidable
open import TheoryGrammar.Decidable.Representable
open import TheoryGrammar.Instances.Lambda.Modes.Concat
open import TheoryGrammar.Instances.Lambda.Modes.Core
open import TheoryGrammar.Instances.Lambda.Modes.Interleave
open import TheoryGrammar.Instances.Lambda.Modes.Overlap

module Modes (Name : Type₀) (_≟_ : Discrete Name) where

  -- the one-name context: what a leaf must account for
  sing : Name → List Name
  sing n = n ∷ []

  -- external decidability, used ONLY to build `dec-⌈⌉`
  discreteCtx : Discrete (List Name)
  discreteCtx = discreteList _≟_

  module Cc = Concat Name
  module Il = Interleave Name
  module Ov = Overlap Name

  private
    -- `dec-⌈⌉` needs the CARRIER and nothing else, and all three
    -- `Fibered` have the same one -- so ONE instance serves all four
    -- modes, and the three bare leaves below are literally one term.
    module Rep = DecRep {S = Unit} (λ _ → List Name)

    module OrdC = Core Name Cc.fib Cc.point Cc.dec sing
    module LinC = Core Name Il.fib Il.point Il.dec sing
    module RelC = Core Name Ov.fib Ov.point Ov.dec sing

  -- ORDERED: concatenation, no exchange.
  module Ord where
    open OrdC public

    Lf : Name → CtxG
    Lf n = ⌈ sing n ⌉

    decLf : (n : Name) → ⊤G ⊢ Dec⟨ Lf n ⟩
    decLf n = Rep.dec-⌈⌉ discreteCtx (sing n)

    open Mode Lf decLf public

  -- LINEAR: interleaving.  Exchange, no weakening, no contraction.
  module Lin where
    open LinC public

    Lf : Name → CtxG
    Lf n = ⌈ sing n ⌉

    decLf : (n : Name) → ⊤G ⊢ Dec⟨ Lf n ⟩
    decLf n = Rep.dec-⌈⌉ discreteCtx (sing n)

    open Mode Lf decLf public

  -- AFFINE: the LINEAR `Fibered`, with weakening as a leaf modality.
  -- `⌈n⌉ ⊗ᶜ ⊤` denotes "a use of n, plus any slack" -- and slack is
  -- exactly what weakening licenses.  Its decision is the tensor's.
  module Aff where
    open LinC public

    Lf : Name → CtxG
    Lf n = ⌈ sing n ⌉ ⊗ᶜ ⊤G

    decLf : (n : Name) → ⊤G ⊢ Dec⟨ Lf n ⟩
    decLf n = dec-⊗ᶜ ⌈ sing n ⌉ ⊤G (Rep.dec-⌈⌉ discreteCtx (sing n)) dec-⊤

    open Mode Lf decLf public

  -- RELEVANT: interleaving WITH SHARING.  Contraction, no weakening.
  module Rel where
    open RelC public

    Lf : Name → CtxG
    Lf n = ⌈ sing n ⌉

    decLf : (n : Name) → ⊤G ⊢ Dec⟨ Lf n ⟩
    decLf n = Rep.dec-⌈⌉ discreteCtx (sing n)

    open Mode Lf decLf public
