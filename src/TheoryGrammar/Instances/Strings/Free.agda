{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Strings are FREE: the scan has exactly one parse.

   `Free F = ∀ i → isContr (μ F i)` was stated generically and nothing
   satisfied it, so both it and `scanμ-scanner-irrelevant` were
   vacuous.  This discharges it for the string scan, via
   `shapeContr→Free` -- so it suffices that the ONE-STEP shape is
   contractible, and the recursion is handled generically.

   The two cases are the decomposition axiom in h-level form:

     at ε      -- the `ε'` branch is contractible, the `⊗` branch empty
                  (its left factor would have to be an atom, and no
                  atom is empty);
     at c ∷ w  -- the reverse, and the `⊗` branch is contractible
                  because the atom pins the cut (`split3App` plus cons
                  injectivity) and `split3IsProp` pins the witness.

   Both halves of `PartsFaithful` appear, and they do different jobs:
   the parts are pinned by the ATOM, the witness by SET-NESS. -}
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sum using (_⊎_; inl; inr)
import Cubical.Data.Equality as Eq
open import TheoryGrammar.Enumerable using (No)

module TheoryGrammar.Instances.Strings.Free
  (Char : Type₀)
  (decChar : (a b : Char) → (a Eq.≡ b) ⊎ No (a Eq.≡ b))
  where

open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Unit
open import Cubical.Data.List
open import Cubical.Data.List.Properties using (cons-inj₁; cons-inj₂)
open import Cubical.Data.Empty as E using (⊥)

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded

open import TheoryGrammar.Instances.Strings.Automata Char decChar public

private
  variable ℓ : Level

  propEqStr : isSet String → {x y : String} → isProp (x Eq.≡ y)
  propEqStr ss {x} {y} = subst isProp Eq.PathPathEq (ss x y)

  -- a Σ over Bool with one branch empty is the other branch
  ΣBoolT : {P : Bool → Type ℓ}
         → isContr (P true) → (P false → ⊥) → isContr (Σ Bool P)
  ΣBoolT ct ne .fst = true , ct .fst
  ΣBoolT ct ne .snd (true  , p) = ΣPathP (refl , ct .snd p)
  ΣBoolT ct ne .snd (false , p) = E.rec (ne p)

  ΣBoolF : {P : Bool → Type ℓ}
         → isContr (P false) → (P true → ⊥) → isContr (Σ Bool P)
  ΣBoolF cf ne .fst = false , cf .fst
  ΣBoolF cf ne .snd (false , p) = ΣPathP (refl , cf .snd p)
  ΣBoolF cf ne .snd (true  , p) = E.rec (ne p)

-- ==================================================================
-- An atom is a proposition, and determines its character.
-- ==================================================================

charIsProp : isSet String → (u : String) → isProp (char u)
charIsProp ss u (c₁ , e₁) (c₂ , e₂) =
  ΣPathP (cEq , isProp→PathP (λ _ → propEqStr ss) e₁ e₂)
  where
    cEq : c₁ ≡ c₂
    cEq = cons-inj₁ (sym (Eq.eqToPath e₁) ∙ Eq.eqToPath e₂)

-- ==================================================================
-- The one-step shape, at each of the two cases.
-- ==================================================================

private
  εAt[] : isContr (Sh (starAlt char true) [])
  εAt[] .fst = lift (tt , λ ())
  εAt[] .snd (lift (tt , f)) = cong lift (ΣPathP (refl , funExt λ ()))

  ⊗At[] : Sh (starAlt char false) [] → ⊥
  ⊗At[] ((u , v , s) , h) = go s (lower (h true))
    where go : Split3 u v [] → char u → ⊥
          go nil (c , ())

  εAt∷ : (c : Char) (w : String) → Sh (starAlt char true) (c ∷ w) → ⊥
  εAt∷ c w (lift (() , _))

  ⊗At∷ : isSet String → (c : Char) (w : String)
       → isContr (Sh (starAlt char false) (c ∷ w))
  ⊗At∷ ss c w .fst =
    (c ∷ [] , w , cons nil) , λ { true → lift (c , Eq.refl) ; false → tt* }
  ⊗At∷ ss c w .snd ((u , v , s) , h) =
    ΣPathP (spEq , isProp→PathP
      (λ i → isPropΠ λ { true  → isOfHLevelLift 1 (charIsProp ss _)
                       ; false → isPropUnit* }) _ h)
    where
      atom : char u
      atom = lower (h true)

      -- the atom pins the left part, hence (with `split3App`) the cut
      uEq : u ≡ (c ∷ [])
      uEq = Eq.eqToPath (atom .snd) ∙ cong (_∷ []) (sym cChar)
        where
          splitP : (c ∷ w) ≡ (atom .fst ∷ v)
          splitP = Eq.eqToPath (split3App s)
                ∙ cong (_++ v) (Eq.eqToPath (atom .snd))
          cChar : c ≡ atom .fst
          cChar = cons-inj₁ splitP

      vEq : v ≡ w
      vEq = sym (cons-inj₂ (Eq.eqToPath (split3App s)
                          ∙ cong (_++ v) (Eq.eqToPath (atom .snd))))

      spEq : (c ∷ [] , w , cons nil) ≡ (u , v , s)
      spEq = strPartsFaithful ss (c ∷ w) (c ∷ [] , w , cons nil) (u , v , s)
               (funExt λ { true → sym uEq ; false → sym vEq })

-- ==================================================================
-- ... and hence freeness.
-- ==================================================================

scanShapeContr : isSet String → (x : Unit) (m : String)
               → isContr (Sh (ScanF x) m)
scanShapeContr ss tt []      = ΣBoolT εAt[] ⊗At[]
scanShapeContr ss tt (c ∷ w) = ΣBoolF (⊗At∷ ss c w) (εAt∷ c w)

strFree : isSet String → Free ScanF
strFree ss = shapeContr→Free (scanShapeContr ss) scanGuarded
