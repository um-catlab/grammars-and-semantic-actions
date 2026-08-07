{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The grading: deg = length, and a slot is proper when its complement is nonempty. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Strings.Graded (Char : Type₀) where

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
open import TheoryGrammar.Enumerable

open import TheoryGrammar.Instances.Strings.Connectives Char public

split3LenL : ∀ {u v w} → Split3 u v w → length u ≤ length w
split3LenL nil      = zero-≤
split3LenL (cons s) = suc-≤-suc (split3LenL s)

split3LenR : ∀ {u v w} → Split3 u v w → length v ≤ length w
split3LenR nil      = ≤-refl
split3LenR (cons s) = ≤-suc (split3LenR s)

split3LenL< : ∀ {u v w} → Split3 u v w → 0 < length v → length u < length w
split3LenL< nil      pr = pr
split3LenL< (cons s) pr = suc-≤-suc (split3LenL< s pr)

split3LenR< : ∀ {u v w} → Split3 u v w → 0 < length u → length v < length w
split3LenR< nil      pr = E.rec (¬-<-zero pr)
split3LenR< (cons s) pr = suc-≤-suc (split3LenR s)

-- THE RESOURCE PREDICATE, internally: `w` is non-trivial when it
-- decomposes with an ATOM on the left.  Nothing about length appears;
-- this is `⌈_⌉`, `⊗`, `⊕ᴰ` and `⊤` only, so it makes sense at any
-- promodel that has atoms.
NonTrivial : Gr
NonTrivial = ⊕ᴰ Char (λ c → ⌈ c ∷ [] ⌉ ⊗' ⊤G)

-- PRIMITIVE (phase 1).  The ONE bridge from the internal predicate to
-- the grading, confined to the promodel where the grading is defined.
ntLen : {v : String} → NonTrivial v → 0 < length v
ntLen {v} (c , (u' , v' , s) , h) = go (h true) s
  where go : u' Eq.≡ c ∷ [] → Split3 u' v' v → 0 < length v
        go Eq.refl s' = split3LenL s'

StrProper : (o : MonOp) (m : String) → MonSplit o m → MonAr o → Type₀
StrProper nilop m sp ()
StrProper appop w (u , v , _) b = NonTrivial (if b then v else u)

strGraded : GradedFib monoidSig ℓ-zero ℓ-zero
strGraded .fib    = strFib
strGraded .deg _  = length
strGraded .Proper = StrProper
strGraded .deg≤ nilop m sp ()
strGraded .deg≤ appop m (u , v , s) true  = split3LenL s
strGraded .deg≤ appop m (u , v , s) false = split3LenR s
strGraded .deg< nilop m sp ()
strGraded .deg< appop m (u , v , s) true  pr = split3LenL< s (ntLen pr)
strGraded .deg< appop m (u , v , s) false pr = split3LenR< s (ntLen pr)

open Guard strGraded ℓ-zero Unit (λ _ → tt) public

-- THE RESOURCE LAW.  "If every slot of a cut is non-trivial then every
-- slot is a proper part" -- one line, because properness of a slot IS
-- non-triviality of its complement.  A fact about the grading, of the
-- same kind as `deg<`, and what `Decidable.Guarded.resourceOf` needs in
-- order to derive a cut's resource test from terms.
ntProper : (w : String) (sp : MonSplit appop w)
         → ((a : Bool) → NonTrivial (MonParts appop w sp a))
         → (a : Bool) → StrProper appop w sp a
ntProper w sp h true  = h false
ntProper w sp h false = h true

appAr : List Bool
appAr = true ∷ false ∷ []

appArComplete : (a : Bool) → a ∈L appAr
appArComplete true  = here
appArComplete false = there here
