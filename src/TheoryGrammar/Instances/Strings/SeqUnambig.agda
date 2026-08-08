{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Levi's lemma, and sequential unambiguity on top of it. -}
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sum using (_⊎_; inl; inr)
import Cubical.Data.Equality as Eq
open import TheoryGrammar.Enumerable using (No)

module TheoryGrammar.Instances.Strings.SeqUnambig
  (Char : Type₀)
  (decChar : (a b : Char) → (a Eq.≡ b) ⊎ No (a Eq.≡ b))
  where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.List
open import Cubical.Data.Nat
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty as E using (⊥; ⊥*)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.BaseChange
open import TheoryGrammar.Fibered
open import TheoryGrammar.Enumerable using (No)

open import TheoryGrammar.Instances.Strings.RegExp Char decChar public

-- LEVI'S LEMMA now lives in `Strings/Levi.agda`, which takes NO `decChar`:
-- both splittings are of the SAME word, so the `cons`/`cons` case has no
-- letters to compare and the disjunction is resolved by the recursion.

open import TheoryGrammar.Instances.Strings.Levi Char

import TheoryGrammar.Instances.Strings.Recompose as Rcm
module Rc = Rcm Char

-- FIRST and FOLLOWLAST, as derivatives rather than as subsets.

∉First : Char → Gr → Type₀
∉First c A = Derivᶜ.δ c A ⊢ ⊥G

-- "no complete parse of A extends, by c, to another parse of A"
∉FollowLast : Char → Gr → Type₀
∉FollowLast c A = ∀ {u v w} → A u → Split3 u (c ∷ v) w → A w → ⊥*

_⊛_ : Gr → Gr → Type₀
A ⊛ B = (c : Char) → ∉FollowLast c A ⊎ ∉First c B

infix 10 _⊛_

private
  split3Nil : ∀ {u w} → Split3 u [] w → u Eq.≡ w
  split3Nil = split3-nilʳ                     -- `Base`, not a fifth copy

-- THE THEOREM. Under `A ⊛ B` a word has AT MOST ONE splitting compatible
-- with A and B -- so `A ⊗ B` is read deterministically, and the `length w
-- + 1` cuts collapse to one.

sameSplit : {A B : Gr} → A ⊛ B
          → ∀ {u₁ v₁ u₂ v₂ w} → Split3 u₁ v₁ w → Split3 u₂ v₂ w
          → A u₁ → B v₁ → A u₂ → B v₂ → u₁ Eq.≡ u₂
sameSplit {A} {B} su sp sp' a₁ b₁ a₂ b₂ = go (levi sp sp')
  where
    go : _ → _
    -- the cuts coincide
    go (inl (_ , p , nil))  = split3Nil p
    go (inr (_ , p , nil))  = flip (split3Nil p)
      where flip : _ → _
            flip Eq.refl = Eq.refl
    -- they differ, by a middle piece starting with c' -- impossible
    go (inl (_ , p , cons {c = c'} q')) = clash (su c')
      where clash : _ → _
            clash (inl nf)  = E.rec (lower (nf a₁ p a₂))
            clash (inr nfi) = E.rec (lower (nfi _ b₁))
    go (inr (_ , p , cons {c = c'} q')) = clash (su c')
      where clash : _ → _
            clash (inl nf)  = E.rec (lower (nf a₂ p a₁))
            clash (inr nfi) = E.rec (lower (nfi _ b₂))

-- The cheapest source of `⊛`: a literal can never be followed, since
-- a one-character parse has no proper extension that is still a
-- one-character parse.  So `literal a ⊛ B` for EVERY B.

-- NOTE: this cannot be done by matching the splitting.
split3Len : ∀ {u v w} → Split3 u v w → length u + length v Eq.≡ length w
split3Len nil      = Eq.refl
split3Len (cons s) = Eq.ap suc (split3Len s)

litNoFollow : (a c : Char) → ∉FollowLast c (literal a)
litNoFollow a c {v = v} Eq.refl sp Eq.refl = go (split3Len sp)
  where go : (suc (suc (length v)) Eq.≡ 1) → ⊥*
        go ()

lit⊛ : (a : Char) (B : Gr) → literal a ⊛ B
lit⊛ a B c = inl (litNoFollow a c)

-- The cut determines the remainder, so `sameSplit` upgrades to both
-- components.
split3App = Rc.recompose
++cancelL = Rc.appCancel

split3Fun : ∀ {u v v' w} → Split3 u v w → Split3 u v' w → v Eq.≡ v'
split3Fun {u} {v} {v'} s s' = go (split3App s) s'
  where go : ∀ {w'} → w' Eq.≡ (u ++ v) → Split3 u v' w' → v Eq.≡ v'
        go Eq.refl s'' = ++cancelL u (split3App s'')

sameParts : {A B : Gr} → A ⊛ B
          → ∀ {u₁ v₁ u₂ v₂ w} → Split3 u₁ v₁ w → Split3 u₂ v₂ w
          → A u₁ → B v₁ → A u₂ → B v₂
          → (u₁ Eq.≡ u₂) × (v₁ Eq.≡ v₂)
sameParts su sp sp' a₁ b₁ a₂ b₂ = go (sameSplit su sp sp' a₁ b₁ a₂ b₂)
  where go : _ → _
        go Eq.refl = Eq.refl , split3Fun sp sp'

-- WHY THIS IS NOT `DecReadable`. `Decidable/Rule.fromUnique` consumes
-- `DecReadable`, whose `splitProp` says the `Fibered` has at most one
-- decomposition.

-- `Split3` IS A PROPOSITION -- the parts pin the witness.

split3Of : ∀ {u v w} → w Eq.≡ (u ++ v) → Split3 u v w
split3Of {u = u} {v = v} Eq.refl = splitAll u v

private
  -- `split3Of` commutes with consing, which is the only step the
  -- induction needs
  split3Of-∷ : ∀ {c u v w} (e : w Eq.≡ (u ++ v))
             → split3Of {c ∷ u} {v} (Eq.ap (λ z → c ∷ z) e) ≡ cons (split3Of e)
  split3Of-∷ Eq.refl = refl

  split3-retract : ∀ {u v w} (s : Split3 u v w) → split3Of (split3App s) ≡ s
  split3-retract nil      = refl
  split3-retract (cons t) = split3Of-∷ (split3App t) ∙ cong cons (split3-retract t)

  propEqStr : isSet String → {x y : String} → isProp (x Eq.≡ y)
  propEqStr ss {x} {y} = subst isProp Eq.PathPathEq (ss x y)

split3IsProp : isSet String → ∀ {u v w} → isProp (Split3 u v w)
split3IsProp ss =
  isOfHLevelRetract 1 split3App split3Of split3-retract (propEqStr ss)

-- ... and hence the general property, discharged.  `PartsFaithful` says
-- a decomposition is determined by its parts; for strings the parts
-- give the two components and `split3IsProp` gives the third.
strPartsFaithful : isSet String → PartsFaithful strFib appop
strPartsFaithful ss m (u , v , s) (u' , v' , s') e =
  ΣPathP (eu , ΣPathP (ev , isProp→PathP (λ _ → split3IsProp ss) s s'))
  where
    eu : u ≡ u'
    eu = funExt⁻ e true
    ev : v ≡ v'
    ev = funExt⁻ e false

-- UNAMBIGUITY OF THE TENSOR, INTERNALLY. `isProp ((A ⊗ B) w)` is an
-- EXTERNAL statement -- a claim about the semantic type.

module _ (ss : isSet String) {A B : Gr} (su : A ⊛ B) where

  -- THIS IS `DetPair` (TheoryGrammar.BaseChange) at the splitting
  -- relation, spelled concretely.
  ⊛→detSplit : (w : String) (sp sp' : MonSplit appop w)
         → A (MonParts appop w sp true)  → B (MonParts appop w sp false)
         → A (MonParts appop w sp' true) → B (MonParts appop w sp' false)
         → sp ≡ sp'
  ⊛→detSplit w (u , v , s) (u' , v' , s') a b a' b' =
    strPartsFaithful ss w (u , v , s) (u' , v' , s')
      (funExt λ { true  → Eq.eqToPath (sameParts su s s' a b a' b' .fst)
                ; false → Eq.eqToPath (sameParts su s s' a b a' b' .snd) })

  private
    -- the payload of a splitting, which is what the two sides carry
    Pay : (w : String) → MonSplit appop w → Type₀
    Pay w sp = (a : MonAr appop) → (if a then A else B) (MonParts appop w sp a)

    -- ... and `⊛→detSplit` is exactly `Σ-det` for it
    detAt : (w : String) → Σ-det (Pay w) (Pay w)
    detAt w sp sp' h h' =
      ⊛→detSplit w sp sp' (h true) (h false) (h' true) (h' false)

  -- DERIVED from `BaseChange.Σ-&-conv`. The only string-specific input is
  -- `detAt`; the distribution itself is generic, and `go` is the Π/×
  -- shuffle that `if` forces (`if a then (A & A) else (B & B)` and `(if a
  -- then A else B) × (if a then A else B)` agree at each literal slot but
  -- not at a neutral one).
  ⊗-align : ((A ⊗' B) & (A ⊗' B)) ⊢ ((A & A) ⊗' (B & B))
  ⊗-align w x = go (Σ-&-conv (detAt w) x)
    where
      go : Σ (MonSplit appop w) (λ sp → Pay w sp × Pay w sp)
         → ((A & A) ⊗' (B & B)) w
      go (sp , h , h') =
        sp , λ { true → h true , h' true ; false → h false , h' false }

  -- The external statement, for comparison.  Note where the work is:
  -- `eq` -- the alignment -- is the whole content, and the two
  -- propositions only collapse the paired payloads afterwards.
  ⊗-unambiguous : ((w : String) → isProp (A w))
                → ((w : String) → isProp (B w))
                → (w : String) → isProp ((A ⊗' B) w)
  ⊗-unambiguous pa pb w (sp , h) (sp' , h') =
    ΣPathP (eq , isProp→PathP
                   (λ _ → isPropΠ λ { true → pa _ ; false → pb _ }) h h')
    where eq : sp ≡ sp'
          eq = ⊛→detSplit w sp sp' (h true) (h false) (h' true) (h' false)
