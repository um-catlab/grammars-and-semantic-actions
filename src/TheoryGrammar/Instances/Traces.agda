{-
  INDEX for the PARTIALLY COMMUTATIVE MONOID (Mazurkiewicz traces): the
  free monoid on Σ modulo `ab = ba` at a symmetric irreflexive
  INDEPENDENCE relation `I`.  The operation stays TOTAL and only the
  EQUATION is conditional, so -- exactly as for `Bags` -- nothing is
  quotiented: the carrier stays `List Σ`, the commutation goes into
  `Split`, and Ordered/Commutative are the two endpoints of one family,
  both isos proved rather than asserted.  Each piece lives in
  `Instances/Traces/`.

    Shuffle      PRIMITIVE: `ITr`, the I-indexed shuffle, and `IndepAll`
    Base         the promodel, its lax point, and the connectives
    Ordered      ENDPOINT: `ITr ⊥I ≅ Split3`   (Strings, unchanged)
    Commutative  ENDPOINT: `ITr ⊤I ≅ Ilv`      (Bags,    unchanged)
    Refinement   `Refinable`: two shuffles of `w` cross, for every `Ind`
    Enumeration  the shuffles of `w`, enumerated and complete
    Decidable    `DecEnumerable` / `DecSplittings` / `DecTensorRule`
    Examples     3 letters, 1 independent pair: 4 < 5 < 8
    Mode         `Modes/Core`'s `Uses` at this substrate
    ModeTests    the mode separates ordered from linear
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Traces where

-- The first eight are PARAMETERISED -- by the alphabet, and most of them
-- by the independence relation -- so they are imported rather than
-- opened: unapplied, their names would only shadow one another.
import TheoryGrammar.Instances.Traces.Shuffle
import TheoryGrammar.Instances.Traces.Base
import TheoryGrammar.Instances.Traces.Ordered
import TheoryGrammar.Instances.Traces.Commutative
import TheoryGrammar.Instances.Traces.Refinement
import TheoryGrammar.Instances.Traces.Enumeration
import TheoryGrammar.Instances.Traces.Decidable
import TheoryGrammar.Instances.Traces.Mode

-- ... and the two closed ones, which pick an alphabet and run.
open import TheoryGrammar.Instances.Traces.Examples
open import TheoryGrammar.Instances.Traces.ModeTests
