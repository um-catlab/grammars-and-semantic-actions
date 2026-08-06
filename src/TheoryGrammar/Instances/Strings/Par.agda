{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Associativity of the CONJUNCTIVE product over decompositions.

   The linear-logic par is disjunctive, `∀(u,v). uv=w → (A u ⊎ B v)`,
   and is not associative here -- `⊎` does not commute with `∀`.  The
   conjunctive product has no `⊎`, and `∀` commutes with `×` freely, so
   it should associate.  This file checks that it does. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Strings.Par (Char : Type₀) where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Unit
open import Cubical.Data.List

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib

open import TheoryGrammar.Instances.Strings.Laws Char public

-- the binary conjunctive product, spelled directly
Par2 : Gr → Gr → Gr
Par2 A B w = (u v : String) → Split3 u v w → A u × B v

-- ==================================================================
-- Two facts about splittings that the proof needs.
-- ==================================================================

-- every word splits with nothing on the right
splitRightNil : (u : String) → Split3 u [] u
splitRightNil []      = nil
splitRightNil (c ∷ u) = cons (splitRightNil u)

-- the other rebracketing: from `w = x·z` and `x = u·v` get `w = u·(v·z)`
splitAssoc⁻ : ∀ {u v x z w} → Split3 x z w → Split3 u v x
            → Σ[ y ∈ String ] (Split3 u y w × Split3 v z y)
splitAssoc⁻ s        nil       = _ , nil , s
splitAssoc⁻ (cons s) (cons s2) =
  let (y , p , q) = splitAssoc⁻ s s2 in y , cons p , q

-- ==================================================================
-- Associativity, both directions.
-- ==================================================================

module _ {A B C : Gr} where

  par-assoc→ : Par2 (Par2 A B) C ⊢ Par2 A (Par2 B C)
  par-assoc→ w f u y t = av , inner
    where
      -- instantiate at the trivial split of `u` to read off the A
      av : A u
      av = f u y t .fst u [] (splitRightNil u) .fst

      inner : (v z : String) → Split3 v z y → B v × C z
      inner v z t2 = bv , cz
        where
          r  = splitAssoc t t2            -- w = (u·v)·z
          fr = f (r .fst) z (r .snd .snd)
          bv : B v
          bv = fr .fst u v (r .snd .fst) .snd
          cz : C z
          cz = fr .snd

  par-assoc← : Par2 A (Par2 B C) ⊢ Par2 (Par2 A B) C
  par-assoc← w g x z s = inner , cz
    where
      -- instantiate at the trivial split of `w` to read off the C
      cz : C z
      cz = g [] w nil .snd x z s .snd

      inner : (u v : String) → Split3 u v x → A u × B v
      inner u v s2 = au , bv
        where
          r  = splitAssoc⁻ s s2           -- w = u·(v·z)
          gr = g u (r .fst) (r .snd .fst)
          au : A u
          au = gr .fst
          bv : B v
          bv = gr .snd v z (r .snd .snd) .fst

-- ==================================================================
-- What would upgrade the two maps to an ISOMORPHISM, and why it is not
-- here.
--
-- The round trips reduce to `f` applied at a DIFFERENT splitting proof
-- of the same three words -- so they follow from `Split3` being
-- propositional, which it morally is: the cut position is determined by
-- the parts.
--
-- But `isProp (Split3 u v w)` is BLOCKED in Cubical Agda.  `nil` has
-- type `Split3 [] v v`, repeating `v` in two index positions, so
-- matching two `nil`s asks the unifier to solve `v ≟ v₁` twice and it
-- gets stuck (SplitError.UnificationStuck).  Not a proof difficulty --
-- an encoding one.
--
-- The fix, if the iso is wanted, is to define `Split3` by RECURSION on
-- the first component rather than as an indexed family:
--
--   Split3 []      v w       = v Eq.≡ w
--   Split3 (c ∷ u) v []      = ⊥
--   Split3 (c ∷ u) v (d ∷ w) = (c Eq.≡ d) × Split3 u v w
--
-- Then propositionality is structural.  That is the same trade seen at
-- `IsNil`, and it would ripple through the instance.
-- ==================================================================
