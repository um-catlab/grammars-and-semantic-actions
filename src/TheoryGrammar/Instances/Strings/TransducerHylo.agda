{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{-
  A GUARDED PROGRAM OVER THE GLUE.

  `TransducerGuard` proved the side condition; this runs the recursion.
  `transCase` is the decomposition axiom for aligned pairs -- `charCase`
  for a two-tape carrier -- and `complete` is `hyloC` at it, giving the
  converse of `TransducerMu.μ→Trans`: the `Eq`-predicate implies the
  inductive grammar, with the termination certificate being
  `transGuarded` and no recursion written at the use site.

  This is the last place a glued carrier could have got in the way:
  `löb` descends the degree rather than the structure, so the payload
  the splittings carry has to survive well-founded descent, not just
  pattern matching.  The `refl` test at the end is that it does.
  PRIMITIVE: `mapLen`, `transCase`.
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Strings.TransducerHylo
  (In Out : Type₀) (f : In → Out) where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.List
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Theories.Monoid
open import TheoryGrammar.Fibered
open import TheoryGrammar.Grading
open import TheoryGrammar.Graded using (module Guard)

import TheoryGrammar.Instances.Strings.TransducerGuard as TG
open TG In Out f public

open Guard glueGraded ℓ-zero Unit (λ _ → tt)

-- PRIMITIVE.  `map` preserves length -- the one arithmetic fact the
-- decomposition owes, and the only place the two tapes' degrees meet.
mapLen : (u : I.String) → length (map f u) Eq.≡ length u
mapLen []      = Eq.refl
mapLen (c ∷ u) = Eq.ap suc (mapLen u)

TransFam : Ix → Type ℓ-zero
TransFam i = Trans (i .snd)

-- ==================================================================
-- THE DECOMPOSITION AXIOM.
--
-- PRIMITIVE (phase 1).  Take an aligned transduced pair apart one
-- letter: the `Eq.refl` matches are on the TRANSDUCTION witness, which
-- determines the output tape, so the output splitting is not chosen --
-- it is read off.
-- ==================================================================

transCase : CoalgC TransF TransFam
transCase _ ([]    , v , e) Eq.refl = true  , (tt , tt , λ ()) , λ ()
transCase _ (c ∷ w , v , e) Eq.refl =
  false , (splitI , splitO , rel) , payload
  where
  splitI : I.strFib .Split appop (c ∷ w)
  splitI = (c ∷ []) , w , I.cons I.nil

  splitO : O.strFib .Split appop (f c ∷ map f w)
  splitO = (f c ∷ []) , map f w , O.cons O.nil

  rel : (a : MonAr appop)
      → length (I.strFib .parts appop (c ∷ w) splitI a)
        Eq.≡ length (O.strFib .parts appop (f c ∷ map f w) splitO a)
  rel true  = Eq.refl
  rel false = Eq.sym (mapLen w)

  payload : (a : MonAr appop)
          → ⟦ consSlot a ⟧c TransFam
              (glue .parts appop (c ∷ w , f c ∷ map f w , e)
                                 (splitI , splitO , rel) a)
  payload true  = lift (c , Eq.refl , Eq.refl)
  payload false = Eq.refl

-- the algebra is `μ` itself, in connective form
μAlgC : AlgC TransF (μ TransF)
μAlgC x m t = μ-alg TransF x m (fromC (TransF x) m t)

-- ==================================================================
-- THE PROGRAM.  No recursion at the use site; `transGuarded` is the
-- termination certificate.
-- ==================================================================

complete : (g : Aligned) → Trans g → TransM (tt , g)
complete g t = hyloC {F = TransF} (λ _ → transGuarded) transCase μAlgC (tt , g) t

-- ==================================================================
-- ... AND IT EVALUATES.
-- ==================================================================

module _ (x : In) where

  private
    g1 : Aligned
    g1 = (x ∷ []) , (f x ∷ []) , Eq.refl

    tr : Trans g1
    tr = Eq.refl

  -- the round trip: build the inductive derivation by well-founded
  -- descent, then fold it back to the predicate
  _ : μ→Trans g1 (complete g1 tr) ≡ Eq.refl
  _ = refl
