{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{-
  GUARDEDNESS OVER THE GLUE.

  `TransducerMu` showed `Inductive` accepts a glued substrate; `fold` is
  structural recursion on `μ`, so it never touched `Grading`.  This file
  supplies what `Grading` wants -- and the point is that it supplies
  almost nothing: `Gluing.Graded.gradeLeft` inherits the whole grading
  from the input tape, because the degree only ever looks through `π₁`.

  The one obligation left is the description's own: at the `cons` branch
  the recursive slot must shrink, which holds because the SHAPE at the
  other slot is a `Letter` and so pins that part to one character.  Note
  where that comes from -- the shape, not the splitting -- which is why
  guardedness is a property of the description and not of the substrate.
  PRIMITIVE: `ntOfLetter` (one `Eq.refl` match).
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Strings.TransducerGuard
  (In Out : Type₀) (f : In → Out) where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false; if_then_else_)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.List
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Theories.Monoid
open import TheoryGrammar.Fibered
open import TheoryGrammar.Grading
open import TheoryGrammar.Graded using (module Guard)
open import TheoryGrammar.Gluing
open import TheoryGrammar.CarrierMap using (Reindex; hom)
open import TheoryGrammar.Gluing.Graded

import TheoryGrammar.Instances.Strings.TransducerMu as TM
open TM In Out f public

import TheoryGrammar.Instances.Strings.Graded as SG
module SGI = SG In

-- ==================================================================
-- THE GRADED GLUE.  Everything is inherited; nothing is proved here.
-- ==================================================================

module GG = GradeGlue I.strFib O.strFib
              (λ s w v → LI.lenIx .hom s w Eq.≡ LO.lenIx .hom s v)

glueGraded : GradedFib monoidSig ℓ-zero ℓ-zero
glueGraded = GG.gradedGlue (gradingOf SGI.strGraded)

open Guard glueGraded ℓ-zero Unit (λ _ → tt)

-- ==================================================================
-- THE DESCRIPTION IS GUARDED.
-- ==================================================================

-- PRIMITIVE.  A part pinned to a single character is non-trivial, which
-- is the string instance's properness predicate.
ntOfLetter : {u : I.String} {c : In} → u Eq.≡ (c ∷ []) → SGI.NonTrivial u
ntOfLetter {c = c} Eq.refl = c , ((c ∷ []) , [] , I.cons I.nil) , pay
  where
  pay : (b : Bool) → (if b then SGI.⌈ c ∷ [] ⌉ else SGI.⊤G)
                       (SGI.MonParts appop (c ∷ []) ((c ∷ []) , [] , I.cons I.nil) b)
  pay true  = Eq.refl
  pay false = tt

transGuarded : Guarded (TransF tt)
transGuarded g (true  , sp , _)  (()    , _)
transGuarded g (false , sp , sh) (true  , ())
transGuarded g (false , sp , sh) (false , tt*) =
  glueGraded .deg< appop g sp false
    (lift (ntOfLetter (sh true .lower .snd .fst)))
