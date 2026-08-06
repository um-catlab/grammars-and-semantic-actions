{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Quicksort: the two primitives (decomposition, partition) and the sort,
   run both plainly and at the specification. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Bags.Quicksort (A : Type₀) where

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
open import TheoryGrammar.SemanticAction

open import TheoryGrammar.Instances.Bags.QuicksortFunctor A public

open Views bagFib
open ActFib bagFib public using (Δ; Action; tagA; observe; run; pureA; mapA; caseA; ⊕A; idA; accepts?; runResult; runEither; okA; maybeA)

partition : (p : A → Bool) (xs : Bag)
          → Σ[ lo ∈ Bag ] Σ[ hi ∈ Bag ] Ilv lo hi xs
partition p [] = [] , [] , nil
partition p (y ∷ xs) with p y
... | true  = let (lo , hi , s) = partition p xs in (y ∷ lo) , hi , left s
... | false = let (lo , hi , s) = partition p xs in lo , (y ∷ hi) , right s

-- element and a rest.  This is the bag instance of "⊤ is the initial
-- algebra of the shape functor" -- no comparison appears in it.
bagCase : Cover (⌈ [] ⌉ ⊕ ⊕ᴰ A (λ x → ⌈ x ∷ [] ⌉ ⊗' ⊤G))
bagCase []       _ = inl Eq.refl
bagCase (x ∷ xs) _ = inr (x , ⊗-mk (left (ilvApp [] xs)) Eq.refl tt)

-- (2) PARTITION.  Given the pivot and the rest, split the rest by
-- comparison and regroup so the pivot sits in the middle.  This is
-- the ONLY place the ordering `le` is used.
--
-- Typed as `⇛`: a VIEW MORPHISM, re-analysing one pattern as another.
-- `_⇛_` is `_⊢_`; the name records the role, not a new notion.
splitAround : (le : A → A → Bool) (x : A)
            → (⌈ x ∷ [] ⌉ ⊗' ⊤G) ⇛ (⊤G ⊗' (⌈ x ∷ [] ⌉ ⊗' ⊤G))
splitAround le x w ((u , v , s) , h) = go (h true) s
  where
    go : u Eq.≡ x ∷ [] → Ilv u v w → (⊤G ⊗' (⌈ x ∷ [] ⌉ ⊗' ⊤G)) w
    go Eq.refl s' =
      let (lo , hi , t) = partition (λ y → le y x) v
          (rest , e1 , e2) = ilvAssoc s' t
      in ⊗-mk e1 tt (⊗-mk e2 Eq.refl tt)

-- THE INTRINSIC SPECIFICATION.  The motive of the hylomorphism IS the
-- statement to be proved: "a bag equivalent to the input".  Nothing is
-- rechecked afterwards -- the algebra produces the proof as it builds
-- the output, so a wrong implementation cannot be written.

Spec : Ix → Type₀
Spec (_ , m) = Σ[ out ∈ Bag ] Perm out m

specNil : {w : Bag} → w Eq.≡ [] → Spec (tt , w)
specNil Eq.refl = [] , nil

specJoin : (piv : A) {lo rest w p1 hi : Bag}
         → Ilv lo rest w → Ilv p1 hi rest → p1 Eq.≡ piv ∷ []
         → Spec (tt , lo) → Spec (tt , hi) → Spec (tt , w)
specJoin piv e1 e2 Eq.refl (loOut , pl) (hiOut , ph) =
  (loOut ++ (piv ∷ hiOut)) , permMerge pl (cons ph e2) e1

module Sort (le : A → A → Bool) where

  -- Plumbing between two spellings of one type: the description's ⊗e
  -- carries a Lift on the representable, and its arity-family is not
  -- `if`-shaped, so the implicits must be pinned.  Pure coercion.
  intoQ : (x : A) → (⊤G ⊗' (⌈ x ∷ [] ⌉ ⊗' ⊤G))
                  ⊢ ⟦ ⊗e appop (QG x) ⟧c (λ _ → Unit)
  intoQ x w ((lo , rest , e1) , h) =
    ⊗I {P = λ a → ⟦ QG x a ⟧c (λ _ → Unit)} e1 tt
      (⊗E {P = λ a → if a then ⌈ x ∷ [] ⌉ else ⊤G}
          (λ p1 hi e2 pf _ →
             ⊗I {P = λ a → ⟦ QG' x a ⟧c (λ _ → Unit)} e2 (lift pf) tt)
          (h false))

  -- THE COALGEBRA, point-free: decompose, then for each pivot
  -- partition around it and inject.  No list pattern is matched here.
  --
  -- Read as a VIEW (TheoryGrammar.View): `bagCase` is the view, the two
  -- branches are the right-hand sides, and `splitAround` is a view
  -- MORPHISM `⇛` -- the only place the ordering `le` appears.  Since the
  -- source is `⊤G` there is no payload to carry past the analysis, so
  -- `withView` degenerates to `caseOf`.  A coalgebra out of ⊤ and a view
  -- are the same thing; this term did not have to change to become one.
  qcoalg : CoalgC QF (λ _ → Unit)
  qcoalg tt =
    caseOf bagCase
      (⊕ᴰ-I _ true ∘g liftg)
      (⊕ᴰ-E (λ x → ⊕ᴰ-I _ false ∘g ⊕ᴰ-I _ x
                      ∘g intoQ x ∘g splitAround le x))

  -- THE ALGEBRA, point-free: the empty branch returns ε, the pivot
  -- branch concatenates around the pivot.
  qalg : AlgC QF (λ _ → Bag)
  qalg tt =
    ⊕ᴰ-E λ { true  → λ _ _ → []
              ; false → ⊕ᴰ-E λ piv → λ w t →
                  ⊗E {P = λ a → ⟦ QG piv a ⟧c (λ _ → Bag)} {w = w}
                     (λ _ _ _ sLo inner →
                        sLo ++ (piv ∷ ⊗E {P = λ a → ⟦ QG' piv a ⟧c (λ _ → Bag)}
                                          (λ _ _ _ _ sHi → sHi) inner)) t }

  quicksort : Bag → Bag
  quicksort m = hyloC qfGuarded qcoalg qalg (tt , m) tt

  -- ... and the same coalgebra, run at the SPECIFICATION.
  qalgV : AlgC QF Spec
  qalgV tt =
    ⊕ᴰ-E λ { true  → λ w e → specNil (lower e)
              ; false → ⊕ᴰ-E λ piv → λ w t →
                  ⊗E {P = λ a → ⟦ QG piv a ⟧c Spec} {w = w}
                     (λ lo rest e1 sLo inner →
                        ⊗E {P = λ a → ⟦ QG' piv a ⟧c Spec}
                           (λ p1 hi e2 pf sHi →
                              specJoin piv e1 e2 (lower pf) sLo sHi)
                           inner) t }

  -- INTRINSICALLY VERIFIED QUICKSORT.
  quicksortV : (m : Bag) → Σ[ out ∈ Bag ] Perm out m
  quicksortV m = hyloC qfGuarded qcoalg qalgV (tt , m) tt

  -- ... and it is a MAP OUT OF TOP, so the generic interface applies.
  -- The specification grammar IS a `⊕ᴰ` over the output bag, so reading
  -- the sorted bag off it is the GENERIC `tagA` and running the program
  -- is the GENERIC `observe` (TheoryGrammar.SemanticAction).  The `.fst`
  -- that use sites used to write was exactly that, by hand -- and going
  -- through `tagA` is what keeps the permutation proof in the type
  -- right up to the externalisation.
  SpecG : TheoryTy ℓ-zero tt
  SpecG m = Σ[ out ∈ Bag ] Perm out m

  quicksortC : Cover SpecG
  quicksortC m _ = quicksortV m

  qsortV : Bag → Bag
  qsortV = observe quicksortC (tagA Bag)

-- It computes.
