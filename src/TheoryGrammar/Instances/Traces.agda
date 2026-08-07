{-
  THE PARTIALLY COMMUTATIVE MONOID (trace monoid), as a promodel.

  A trace monoid is the free monoid on Σ modulo `ab = ba` for pairs in a
  symmetric irreflexive independence relation `I`.  The operation stays
  TOTAL; it is the EQUATION that is conditional.  So, exactly as for
  `Bags`, nothing is quotiented: the carrier stays `List Σ` and the
  commutation goes into `Split`.

  This module is only the index; each piece lives in `Instances/Traces/`.

    Shuffle      PRIMITIVE: `ITr`, the I-indexed shuffle, and `IndepAll`
    Base         the promodel, its lax point, and the connectives
    Ordered      ENDPOINT: `ITr ⊥I ≅ Split3`   (Strings, unchanged)
    Commutative  ENDPOINT: `ITr ⊤I ≅ Ilv`      (Bags,    unchanged)
    Enumeration  the shuffles of `w`, enumerated and complete
    Decidable    `DecEnumerable` / `DecSplittings` / `DecTensorRule`
    Examples     3 letters, 1 independent pair: 4 < 5 < 8
    Mode         `Modes/Core`'s `Uses` at this substrate
    ModeTests    the mode separates ordered from linear

  Ordered and Commutative together are the INTERPOLATION THEOREM: the
  two resource substrates this development already had are the two
  endpoints of one family, and both isos are proved, not asserted.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Traces where

open import TheoryGrammar.Instances.Traces.Shuffle
open import TheoryGrammar.Instances.Traces.Base
open import TheoryGrammar.Instances.Traces.Ordered
open import TheoryGrammar.Instances.Traces.Commutative
open import TheoryGrammar.Instances.Traces.Enumeration
open import TheoryGrammar.Instances.Traces.Decidable
open import TheoryGrammar.Instances.Traces.Examples
open import TheoryGrammar.Instances.Traces.Mode
open import TheoryGrammar.Instances.Traces.ModeTests
