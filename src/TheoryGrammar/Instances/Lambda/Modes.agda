{-
  SUBSTRUCTURAL MODES over the lambda AST.  Index module.

  The claim under test: ordered, linear, affine and relevant are ONE
  grammar over four context substrates.

    Ctx          the context signature: one sort, one binary operation
    Fold         `indRaw` -- the AST's eliminator, the only AST primitive
    Core         `Uses` and `check`, generic in the context substrate
    Concat       ordered contexts   (free monoid; `Split3` from Strings)
    Interleave   linear + affine    (free comm. monoid; `Ilv` from Bags)
    Overlap      relevant contexts  (idempotent; `Ilv` plus `both`)
    Instances    the four modes
    Laws         which equations are refl and which cost funExt
    Tests        24 `refl` tests: the four modes separate

  Generic support added under `TheoryGrammar/`:
    CanonicalFocus            every substrate's residual, from `split`
    Decidable.Splittings      `dec-⊗` as an interface, not a theorem
    Decidable.Representable   `dec-⌈⌉`, stated once
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Modes where

open import TheoryGrammar.Instances.Lambda.Modes.Ctx        public
open import TheoryGrammar.Instances.Lambda.Modes.Fold       public
open import TheoryGrammar.Instances.Lambda.Modes.Core       public
open import TheoryGrammar.Instances.Lambda.Modes.Concat     public
open import TheoryGrammar.Instances.Lambda.Modes.Interleave public
open import TheoryGrammar.Instances.Lambda.Modes.Overlap    public
open import TheoryGrammar.Instances.Lambda.Modes.Instances  public
open import TheoryGrammar.Instances.Lambda.Modes.Laws       public
