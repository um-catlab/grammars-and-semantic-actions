{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The grading: deg = length, a slot is proper when its complement is nonempty. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Bags.Graded (A : Type₀) where

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

open import TheoryGrammar.Instances.Bags.Commutativity A public

ilvLenL : ∀ {u v w} → Ilv u v w → length u ≤ length w
ilvLenL nil       = ≤-refl
ilvLenL (left s)  = suc-≤-suc (ilvLenL s)
ilvLenL (right s) = ≤-suc (ilvLenL s)

ilvLenR : ∀ {u v w} → Ilv u v w → length v ≤ length w
ilvLenR nil       = ≤-refl
ilvLenR (left s)  = ≤-suc (ilvLenR s)
ilvLenR (right s) = suc-≤-suc (ilvLenR s)

-- a nonempty COMPLEMENT makes the slot strictly smaller
ilvLenL< : ∀ {u v w} → Ilv u v w → 0 < length v → length u < length w
ilvLenL< nil       pr = E.rec (¬-<-zero pr)
ilvLenL< (left s)  pr = suc-≤-suc (ilvLenL< s pr)
ilvLenL< (right s) pr = suc-≤-suc (ilvLenL s)

ilvLenR< : ∀ {u v w} → Ilv u v w → 0 < length u → length v < length w
ilvLenR< nil       pr = E.rec (¬-<-zero pr)
ilvLenR< (left s)  pr = suc-≤-suc (ilvLenR s)
ilvLenR< (right s) pr = suc-≤-suc (ilvLenR< s pr)

-- The resource predicate, internally: `m` is non-trivial when it
-- decomposes with an ATOM on the left.  No length, so it makes sense at
-- any `Fibered` with atoms.
NonTrivial : Gr
NonTrivial = ⊕ᴰ A (λ x → ⌈ x ∷ [] ⌉ ⊗' ⊤G)

-- PRIMITIVE (phase 1).  The one bridge from the internal predicate to
-- the grading, confined to where the grading is defined.
ntLen : {v : Bag} → NonTrivial v → 0 < length v
ntLen {v} (x , (u , v' , ilv) , h) = go (h true) ilv
  where go : u Eq.≡ x ∷ [] → Ilv u v' v → 0 < length v
        go Eq.refl s = ilvLenL s

Proper' : (o : MonOp) (m : Bag) → MonSplit o m → MonAr o → Type₀
Proper' nilop m sp ()
Proper' appop m (u , v , _) b = NonTrivial (if b then v else u)

bagGraded : GradedFib monoidSig ℓ-zero ℓ-zero
bagGraded .fib    = bagFib
bagGraded .deg _  = length
bagGraded .Proper = Proper'
bagGraded .deg≤ nilop m sp ()
bagGraded .deg≤ appop m (u , v , s) true  = ilvLenL s
bagGraded .deg≤ appop m (u , v , s) false = ilvLenR s
bagGraded .deg< nilop m sp ()
bagGraded .deg< appop m (u , v , s) true  pr = ilvLenL< s (ntLen pr)
bagGraded .deg< appop m (u , v , s) false pr = ilvLenR< s (ntLen pr)

-- `Small` is `NonTrivial`'s internal complement: empty, or one atom.
-- No length anywhere.
Small : Gr
Small = ⌈ [] ⌉ ⊕ ⊕ᴰ A (λ x → ⌈ x ∷ [] ⌉)

-- a non-trivial bag, from its first element
ntCons : (x : A) (u : Bag) → NonTrivial (x ∷ u)
ntCons x u = x , ⊗-mk (left (ilvApp [] u)) Eq.refl tt

-- THE DECOMPOSITION AXIOM. A bag is empty or it is an element and a rest,
-- and the two cases exclude each other.

open Views bagFib using (Cover; Complete; total; exclusive)

bagCase : Cover (⌈ [] ⌉ ⊕ NonTrivial)
bagCase []       _ = inl Eq.refl
bagCase (x ∷ xs) _ = inr (x , ⊗-mk (left (ilvApp [] xs)) Eq.refl tt)

-- `[]` admits no one-element splitting: the exclusion half.
nil-empty : NonTrivial [] → E.⊥
nil-empty (x , (u , v , s) , h) = go (h true) s
  where go : u Eq.≡ x ∷ [] → Ilv u v [] → E.⊥
        go Eq.refl ()

BagCase : Bool → Gr
BagCase b = if b then ⌈ [] ⌉ else NonTrivial

bagComplete : Complete Bool BagCase
bagComplete .total =
  ⊕-E (⊕ᴰ-I Bool {A = BagCase} true) (⊕ᴰ-I Bool {A = BagCase} false) ∘g bagCase
bagComplete .exclusive true  true  d = λ _ _ → E.rec (d refl)
bagComplete .exclusive false false d = λ _ _ → E.rec (d refl)
bagComplete .exclusive true  false _ =
  λ { .([]) (Eq.refl , ne) → E.rec (nil-empty ne) }
bagComplete .exclusive false true  _ =
  λ { .([]) (ne , Eq.refl) → E.rec (nil-empty ne) }

open Guard bagGraded ℓ-zero Unit (λ _ → tt) public
