{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- THE THIRD ROUTE INTO `DecSplittings`: THE DERIVATIVE. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Strings.DerivDec (Char : Type₀) where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Unit
open import Cubical.Data.List
open import Cubical.Data.Empty as E using (⊥*)

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Decidable.Splittings

open import TheoryGrammar.Instances.Strings.Base Char public

-- THE INVERSION PRINCIPLE. A pattern match on a `Split3` whose OUTPUT
-- index is a constructor -- the only phase-1 content in the file.

-- PRIMITIVE (phase 1): a splitting of `c ∷ x` either has empty left
-- factor, or its left factor begins with `c` and the rest splits `x`.
-- This IS Levi at the free monoid, and it is two clauses.
data SplitCons (c : Char) (x : String) : (u v : String) → Type₀ where
  atNil  : SplitCons c x [] (c ∷ x)
  atCons : {u v : String} → Split3 u v x → SplitCons c x (c ∷ u) v

splitCons : {c : Char} {x u v : String} → Split3 u v (c ∷ x) → SplitCons c x u v
splitCons nil      = atNil
splitCons (cons s) = atCons s

-- ... AND THE DECISION, by recursion on the world.

private
  Slots : Type₁
  Slots = Bool → Gr

  -- the deciders `dec-⊗ˢ` is handed, at one word
  Deciders : Slots → String → Type₀
  Deciders A w = (sp : MonSplit appop w) (a : Bool)
               → Dec⟨ A a ⟩ (MonParts appop w sp a)

  yes⊗ : (A : Slots) {w u v : String} (s : Split3 u v w)
       → A true u → A false v → (⊗ˢ appop A) w
  yes⊗ A {u = u} {v} s p q = (u , v , s) , λ { true → p ; false → q }

  -- THE DERIVATIVE FAMILY: slot `true` differentiated, slot `false`
  -- untouched.
  δSlots : Char → Slots → Slots
  δSlots c A true  = λ u → A true (c ∷ u)
  δSlots c A false = A false

  -- ... and the deciders transport onto it with NO new hypothesis: the
  -- decider for `δ_c (A true)` at `u` is the decider for `A true` at the
  -- left part of the cut `(c ∷ u , v)`.
  δDeciders : (c : Char) (x : String) (A : Slots)
            → Deciders A (c ∷ x) → Deciders (δSlots c A) x
  δDeciders c x A d (u , v , s) true  = d (c ∷ u , v , cons s) true
  δDeciders c x A d (u , v , s) false = d (c ∷ u , v , cons s) false

  -- move a decided derivative-tensor back across the isomorphism
  shift : (c : Char) (x : String) (A : Slots)
        → (⊗ˢ appop (δSlots c A)) x → (⊗ˢ appop A) (c ∷ x)
  shift c x A ((u , v , s) , h) = yes⊗ A (cons s) (h true) (h false)

  go : (A : Slots) (w : String) → Deciders A w → Dec⟨ ⊗ˢ appop A ⟩ w

  -- `[]`: the empty cut is the only one, so the two slot decisions
  -- settle it outright.
  go A [] d =
    dec-elim (A true) []
      (λ pT → dec-elim (A false) []
                (λ pF → dec-yes (⊗ˢ appop A) [] (yes⊗ A nil pT pF))
                (λ kF → dec-no (⊗ˢ appop A) [] (missNil kF))
                (d ([] , [] , nil) false))
      (λ kT → dec-no (⊗ˢ appop A) [] (missNil' kT))
      (d ([] , [] , nil) true)
    where
      -- both refutations refute EVERY splitting of `[]`, via `splitNil`
      missNil : (A false [] → ⊥*) → (⊗ˢ appop A) [] → ⊥*
      missNil k ((u , v , nil) , h) = k (h false)

      missNil' : (A true [] → ⊥*) → (⊗ˢ appop A) [] → ⊥*
      missNil' k ((u , v , nil) , h) = k (h true)

  -- `c ∷ x`: try the empty-left cut; failing that, recurse at the
  -- derivative.  No cut is enumerated in either branch.
  go A (c ∷ x) d =
    dec-elim (A true) []
      (λ pT → dec-elim (A false) (c ∷ x)
                (λ pF → dec-yes (⊗ˢ appop A) (c ∷ x) (yes⊗ A nil pT pF))
                (λ kF → rest kF)
                (d ([] , c ∷ x , nil) false))
      (λ kT → rest' kT)
      (d ([] , c ∷ x , nil) true)
    where
      -- the recursive call, with its refutation glued to the caller's
      combine : ((A true [] × A false (c ∷ x)) → ⊥*)
              → Dec⟨ ⊗ˢ appop A ⟩ (c ∷ x)
      combine kNil =
        dec-elim (⊗ˢ appop (δSlots c A)) x
          (λ t → dec-yes (⊗ˢ appop A) (c ∷ x) (shift c x A t))
          (λ kRest → dec-no (⊗ˢ appop A) (c ∷ x) (miss kRest))
          (go (δSlots c A) x (δDeciders c x A d))
        where
          -- EVERY splitting of `c ∷ x` is refuted: `splitCons` says it is
          -- the empty-left cut (killed by `kNil`) or a splitting of `x`
          -- at the derivative (killed by `kRest`).
          miss : ((⊗ˢ appop (δSlots c A)) x → ⊥*) → (⊗ˢ appop A) (c ∷ x) → ⊥*
          miss kRest ((u , v , s) , h) = out (splitCons {c = c} s) h
            where
              out : SplitCons c x u v
                  → ((a : Bool) → A a (MonParts appop (c ∷ x) (u , v , s) a))
                  → ⊥*
              out atNil       g = kNil (g true , g false)
              out (atCons s') g = kRest ((_ , _ , s') , λ { true  → g true
                                                          ; false → g false })

      rest  : (A false (c ∷ x) → ⊥*) → Dec⟨ ⊗ˢ appop A ⟩ (c ∷ x)
      rest  k = combine λ p → k (p .snd)

      rest' : (A true [] → ⊥*) → Dec⟨ ⊗ˢ appop A ⟩ (c ∷ x)
      rest' k = combine λ p → k (p .fst)

-- THE ROUTE.  `nilop` needs no recursion -- `MonSplit nilop w = IsNil w`
-- is decided by looking at `w`, and it has no slots to decide.

strDecDeriv : DecSplittings strFib ℓ-zero
strDecDeriv .dec-⊗ˢ nilop A []      d = dec-yes (⊗ˢ nilop A) [] (tt , λ ())
strDecDeriv .dec-⊗ˢ nilop A (c ∷ w) d = dec-no  (⊗ˢ nilop A) (c ∷ w) λ ()
strDecDeriv .dec-⊗ˢ appop A m       d = go A m d
