{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{-
  THE FIRST INSTANCE OF `Gluing`: A STRING PAIRED WITH ITS LENGTH.

  `Nat/LengthFib` gives `length` as a reindexing of promodels; handing it
  to `Gluing.Pullback` with the IDENTITY right leg makes the comma object
  `Determined`, so every string program lifts into the glue carrying its
  length.  Note the relation is the GRAPH of a function, so this glue is
  a reindexing in disguise -- `Strings/Aligned` is the non-degenerate
  instance.  What this file is good for is that its tests EVALUATE.

  The point of the file is the `refl` tests at the end.  Everything in
  `Gluing` was a convertibility claim about an abstract promodel; these
  are closed terms that must EVALUATE, which is the failure mode a green
  typecheck does not detect.
  PRIMITIVE: none -- the length reindexing is `Nat/LengthFib`.
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Nat.Glue (Char : Type₀) where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.List
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Theories.Monoid
open import TheoryGrammar.Fibered
open import TheoryGrammar.CarrierMap
open import TheoryGrammar.Gluing

import TheoryGrammar.Instances.Strings.Base as StB
module St = StB Char
import TheoryGrammar.Instances.Nat.Base as Nt
import TheoryGrammar.Instances.Nat.LengthFib as LF
module L = LF Char

-- ==================================================================
-- `length` AS A REINDEXING OF PROMODELS -- imported, not restated.
-- ==================================================================

-- The right leg of the comma object is the identity on `ℕ`, so it
-- reflects splittings for free.  (`Strings/Aligned` is where the right
-- leg is non-trivial and `LengthFib.cutS` earns its keep; here the
-- arithmetic side is not being refined, only recorded.)
natId : Reindex Nt.natFib Nt.natFib
natId .hom _ n = n

natIdReflects : (o : MonOp) → Along.ReflectsSplitAt natId o
natIdReflects o n sp = sp , λ _ → Eq.refl

-- ==================================================================
-- THE COMMA OBJECT, and its `Determined` structure.
-- ==================================================================

open Pullback St.strFib Nt.natFib L.lenIx natId public

-- An element of the glued carrier is a string, a number, and a proof
-- that the number is the string's length.
Sized : Type₀
Sized = glue .carrier tt

lenDetermined : Determined
lenDetermined = pullbackDetermined L.lenPres natIdReflects

-- ==================================================================
-- THE TESTS.  Closed terms, at an ABSTRACT pair of characters -- the
-- arithmetic never looks at them, which is the whole content of
-- `lenSplit3`.
-- ==================================================================

module _ (x y : Char) where

  private
    w2 : St.String
    w2 = x ∷ y ∷ []

    -- the glued element: `Eq.refl` typechecks only because `length w2`
    -- already reduces to `2`
    g2 : Sized
    g2 = w2 , 2 , Eq.refl

    -- the string splitting that cuts after one character
    cut1 : St.strFib .Split appop w2
    cut1 = (x ∷ []) , (y ∷ []) , St.cons St.nil

    -- ... and the arithmetic splitting it determines
    add1 : Nt.natFib .Split appop 2
    add1 = lenDetermined appop g2 cut1 .fst

  -- the cut lands at 1 + 1, computed through `coeSplit` and the
  -- reflection of the right leg
  _ : add1 .fst ≡ 1
  _ = refl

  _ : add1 .snd .fst ≡ 1
  _ = refl

  -- THE SHARPER TEST.  The relatedness datum is a composite of three
  -- `Eq` proofs (`homParts`, `coeParts`, the reflection), and it must
  -- collapse -- a stuck one would leave every glued program inert.
  _ : lenDetermined appop g2 cut1 .snd true ≡ Eq.refl
  _ = refl

  _ : lenDetermined appop g2 cut1 .snd false ≡ Eq.refl
  _ = refl

  -- The whole splitting of the glue, assembled from the string side
  -- alone, has the right parts at BOTH components.
  private
    glued : glue .Split appop g2
    glued = cut1 , lenDetermined appop g2 cut1

  _ : glue .parts appop g2 glued true .fst ≡ x ∷ []
  _ = refl

  _ : glue .parts appop g2 glued true .snd .fst ≡ 1
  _ = refl

  _ : glue .parts appop g2 glued false .snd .fst ≡ 1
  _ = refl
