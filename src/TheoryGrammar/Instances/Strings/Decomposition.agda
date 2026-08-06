{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The decomposition axiom -- peel one character -- and its guardedness. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Strings.Decomposition (Char : Type₀) where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.List
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded
open import TheoryGrammar.View

open import TheoryGrammar.Instances.Strings.Graded Char public

open Views strFib public

-- THE decomposition view: every string is empty or has a first
-- character.  `Cover` is `⊤G ⊢ _`, so this is the same term it always
-- was -- naming it records that it is a view and not an ad hoc lemma.
charCase : Cover (⌈ [] ⌉ ⊕ NonTrivial)
charCase []      _ = inl Eq.refl
charCase (c ∷ w) _ = inr (c , ⊗-mk (cons nil) Eq.refl tt)

decompSlot : Char → Bool → Functor tt
decompSlot c true  = ⌜ ⌈ c ∷ [] ⌉ ⌝
decompSlot c false = Var tt

decompAlt : Bool → Functor tt
decompAlt true  = ⌜ ⌈ [] ⌉ ⌝
decompAlt false = ⊕e Char (λ c → ⊗e appop (decompSlot c))

decompF : Unit → Functor tt
decompF _ = ⊕e Bool decompAlt

decompGuarded : (x : Unit) → Guarded (decompF x)
decompGuarded tt = <⊕e Bool decompAlt alt
  where
    go : (c : Char) (m : String) (sp : MonSplit appop m)
         (sh : (a : Bool) → Sh (decompSlot c a) (MonParts appop m sp a))
         (a : Bool) (p : Pos (decompSlot c a) _ (sh a))
       → degIx (nx (decompSlot c a) _ (sh a) p) < length m
    go c m sp sh true ()
    go c m (u , v , s) sh false p =
      slotProper appop m (u , v , s) false (≤Var tt) (one (lower (sh true))) (sh false) p
      where one : u Eq.≡ c ∷ [] → NonTrivial u
            one Eq.refl = c , ⊗-mk (cons nil) Eq.refl tt

    alt : (b : Bool) → Guarded (decompAlt b)
    alt true  = <⌜⌝ ⌈ [] ⌉
    alt false = <⊕e Char _ (λ c → ⊗-guard appop (decompSlot c) (go c))

-- ================================================================
-- ... and it is COMPLETE, with a POSITIVE complement on both sides.
--
-- `charCase` was already total.  What is added here is the exclusion --
-- a word cannot be both empty and headed by a character -- which makes
-- it a `Complete` view in the sense of `TheoryGrammar.View`.
--
-- The refinement over `Dec⟨ ⌈ [] ⌉ ⟩` is not logical: `¬G ⌈ [] ⌉` is a
-- grammar and `contra` excludes it just as well.  It is descriptive.
-- Rejecting `⌈ [] ⌉` here HANDS BACK `NonTrivial` -- the character and
-- the rest of the word -- rather than a function into `⊥`, and that is
-- what the parser downstream actually needs.  `certifies` maps this
-- back to the negative reading, so nothing is lost either way.
-- ================================================================

-- PRIMITIVE, and the only content of the exclusion: the empty word is
-- trivial.  A splitting of `[]` cannot have a one-character left part.
nil-trivial : NonTrivial [] → E.⊥
nil-trivial (c , (u , v , s) , h) = go (h true) s
  where go : u Eq.≡ c ∷ [] → Split3 u v [] → E.⊥
        go Eq.refl ()

EmptyOr : Bool → Gr
EmptyOr b = if b then ⌈ [] ⌉ else NonTrivial

emptyOrNot : Complete Bool EmptyOr
emptyOrNot .total =
  ⊕-E (⊕ᴰ-I Bool {A = EmptyOr} true) (⊕ᴰ-I Bool {A = EmptyOr} false)
  ∘g charCase
emptyOrNot .exclusive true  true  d = λ _ _ → E.rec (d refl)
emptyOrNot .exclusive false false d = λ _ _ → E.rec (d refl)
emptyOrNot .exclusive true  false _ =
  λ { .([]) (Eq.refl , nt) → E.rec (nil-trivial nt) }
emptyOrNot .exclusive false true  _ =
  λ { .([]) (nt , Eq.refl) → E.rec (nil-trivial nt) }
