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
open import TheoryGrammar.Substrate
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded

open import TheoryGrammar.Instances.Strings.Graded Char public

charCase : ⊤G ⊢ (⌈ [] ⌉ ⊕ ⊕ᴰ Char (λ c → ⌈ c ∷ [] ⌉ ⊗' ⊤G))
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
      where one : u Eq.≡ c ∷ [] → 0 < length u
            one Eq.refl = ≤-refl

    alt : (b : Bool) → Guarded (decompAlt b)
    alt true  = <⌜⌝ ⌈ [] ⌉
    alt false = <⊕e Char _ (λ c → ⊗-guard appop (decompSlot c) (go c))
