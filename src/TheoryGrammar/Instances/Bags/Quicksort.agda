{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Quicksort: the primitives, then the sort, run both plainly and at the
   specification.

   THE PRIMITIVES, counted honestly (the "two primitives" this header
   used to claim were the two that carry CONTENT, not the whole list):

     bagCase      decomposition -- ⊤'s coalgebra, no comparison in it
     splitAround  partition -- the ONLY place `le` is used
     intoQ        a coercion between two spellings of one type; pure
                  plumbing, and the one primitive here that would
                  disappear given `⊗e`-with-`if`-shaped arities
     nil-empty    `[]` admits no one-element splitting; the exclusion
                  half of `bagComplete`

   `partitionOrd` is `splitAround`'s worker, not a separate entry.
   Everything else in the file is composition or a semantic action. -}
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

open Views bagFib using (Cover; Complete; total; exclusive; completeCase; certifies; fromUnique; caseOf; caseOfᴰ; refine; withView; viewCase; viewCaseᴰ; cover→probe; Probe; _⇛_)
-- (the semantic actions now arrive via `DecFib` in Base)

-- PRIMITIVE (phase 1).  (1) DECOMPOSITION: a bag is empty, or it is an
-- element and a rest.  This is the bag instance of "⊤ is the initial
-- algebra of the shape functor" -- no comparison appears in it.
bagCase : Cover (⌈ [] ⌉ ⊕ ⊕ᴰ A (λ x → ⌈ x ∷ [] ⌉ ⊗' ⊤G))
bagCase []       _ = inl Eq.refl
bagCase (x ∷ xs) _ = inr (x , ⊗-mk (left (ilvApp [] xs)) Eq.refl tt)

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

module Sort (le : A → A → Bool)
            (leTotal : (x y : A) → le x y Eq.≡ false → le y x Eq.≡ true)
            (leTrans : (x y z : A) → le x y Eq.≡ true → le y z Eq.≡ true
                     → le x z Eq.≡ true)
            where

  open QSF le leTrans public

  -- (2) PARTITION.  Split the rest by comparison against the pivot,
  -- KEEPING the two ordering facts discovered along the way.  Those
  -- facts are not an afterthought: they are precisely what the algebra
  -- needs to conclude sortedness, so they travel with the parts.
  -- This is the ONLY place the ordering `le` is used.
  partitionOrd : (x : A) (xs : Bag)
    → Σ[ lo ∈ Bag ] Σ[ hi ∈ Bag ] (Ilv lo hi xs × Above x lo × Below x hi)
  partitionOrd x []       = [] , [] , nil , []ᵃ , []ᵇ
  partitionOrd x (y ∷ xs) = go (le y x) Eq.refl (partitionOrd x xs)
    where
      Res : Bag → Type₀
      Res b = Σ[ lo ∈ Bag ] Σ[ hi ∈ Bag ] (Ilv lo hi b × Above x lo × Below x hi)

      go : (bl : Bool) → le y x Eq.≡ bl → Res xs → Res (y ∷ xs)
      go true  e (lo , hi , t , aa , bb) =
        (y ∷ lo) , hi , left t , (e ∷ᵃ aa) , bb
      go false e (lo , hi , t , aa , bb) =
        lo , (y ∷ hi) , right t , aa , (leTotal y x e ∷ᵇ bb)

  -- PRIMITIVE (phase 1).
  -- Typed as `⇛`: a VIEW MORPHISM, re-analysing one pattern as another.
  -- `_⇛_` is `_⊢_`; the name records the role, not a new notion.  The
  -- codomain now says `lo` is below the pivot and `hi` above it.
  splitAround : (x : A)
              → (⌈ x ∷ [] ⌉ ⊗' ⊤G)
              ⇛ ((⊤G & Above x) ⊗' (⌈ x ∷ [] ⌉ ⊗' (⊤G & Below x)))
  splitAround x w ((u , v , s) , h) = go (h true) s
    where
      go : u Eq.≡ x ∷ [] → Ilv u v w
         → ((⊤G & Above x) ⊗' (⌈ x ∷ [] ⌉ ⊗' (⊤G & Below x))) w
      go Eq.refl s' =
        let (lo , hi , t , aa , bb) = partitionOrd x v
            (rest , e1 , e2)        = ilvAssoc s' t
        in ⊗-mk e1 (tt , aa) (⊗-mk e2 Eq.refl (tt , bb))

  -- PRIMITIVE (phase 1), and the one here with no content.
  -- Plumbing between two spellings of one type: the description's ⊗e
  -- carries a Lift on the representable, and its arity-family is not
  -- `if`-shaped, so the implicits must be pinned.  Pure coercion.
  intoQ : (x : A) → ((⊤G & Above x) ⊗' (⌈ x ∷ [] ⌉ ⊗' (⊤G & Below x)))
                  ⊢ ⟦ ⊗e appop (QG x) ⟧c (λ _ → Unit)
  intoQ x w ((lo , rest , e1) , h) =
    ⊗I {P = λ a → ⟦ QG x a ⟧c (λ _ → Unit)} e1
      (λ { true → tt ; false → lift (h true .snd) })
      (⊗E {P = λ a → if a then ⌈ x ∷ [] ⌉ else (⊤G & Below x)}
          (λ p1 hi e2 pf bb →
             ⊗I {P = λ a → ⟦ QG' x a ⟧c (λ _ → Unit)} e2 (lift pf)
               (λ { true → tt ; false → lift (bb .snd) }))
          (h false))

  -- ... and `bagCase` is COMPLETE, with a positive complement on both
  -- sides: a bag is empty, or it has an element and a rest.  The
  -- exclusion is the only thing that was missing, and it is the same
  -- fact the sorters' termination already rests on -- `[]` admits no
  -- one-element splitting.
  BagCase : Bool → TheoryTy ℓ-zero tt
  BagCase b = if b then ⌈ [] ⌉ else ⊕ᴰ A (λ x → ⌈ x ∷ [] ⌉ ⊗' ⊤G)

  -- PRIMITIVE (phase 1): `[]` admits no one-element splitting.
  nil-empty : (⊕ᴰ A (λ x → ⌈ x ∷ [] ⌉ ⊗' ⊤G)) [] → E.⊥
  nil-empty (x , (u , v , s) , h) = go (h true) s
    where go : u Eq.≡ x ∷ [] → Ilv u v [] → E.⊥
          go Eq.refl ()

  bagComplete : Complete Bool BagCase
  bagComplete .total =
    ⊕-E (⊕ᴰ-I Bool {A = BagCase} true) (⊕ᴰ-I Bool {A = BagCase} false) ∘g bagCase
  bagComplete .exclusive true  true  d = λ _ _ → E.rec (d refl)
  bagComplete .exclusive false false d = λ _ _ → E.rec (d refl)
  bagComplete .exclusive true  false _ =
    λ { .([]) (Eq.refl , ne) → E.rec (nil-empty ne) }
  bagComplete .exclusive false true  _ =
    λ { .([]) (ne , Eq.refl) → E.rec (nil-empty ne) }

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
                      ∘g intoQ x ∘g splitAround x))

  -- THE ALGEBRA.  Not point-free, and it cannot be: the carrier is the
  -- CONSTANT family `λ _ → Bag`, so there is no index for a combinator
  -- to preserve and the two branches are metalanguage `++`/`∷` on the
  -- payload.  That is a SEMANTIC ACTION, which is allowed -- but it is
  -- also exactly the information `qalgV` keeps and this one throws
  -- away.  Read the pair as the measurement: the constant carrier is
  -- what makes permutation-correctness a separate obligation.
  qalg : AlgC QF (λ _ → Bag)
  qalg tt =
    ⊕ᴰ-E λ { true  → λ _ _ → []
              ; false → ⊕ᴰ-E λ piv → λ w t →
                  ⊗E {P = λ a → ⟦ QG piv a ⟧c (λ _ → Bag)} {w = w}
                     (λ _ _ _ sLo inner →
                        sLo true ++ (piv ∷ ⊗E {P = λ a → ⟦ QG' piv a ⟧c (λ _ → Bag)}
                                          (λ _ _ _ _ sHi → sHi true) inner)) t }

  -- The plain sort, still as a TERM.  `Bag → Bag` would have left the
  -- calculus in a definition; `Δ Bag` is the grammar that carries the
  -- answer, and `run` is then the single exit, in a test.
  qsortP : ⊤G ⊢ Δ Bag
  qsortP m x = hyloC qfGuarded qcoalg qalg (tt , m) tt , x

  -- ... and the same coalgebra, run at the SPECIFICATION.
  qalgV : AlgC QF Spec
  qalgV tt =
    ⊕ᴰ-E λ { true  → λ w e → specNil (lower e)
              ; false → ⊕ᴰ-E λ piv → λ w t →
                  ⊗E {P = λ a → ⟦ QG piv a ⟧c Spec} {w = w}
                     (λ lo rest e1 sLo inner →
                        ⊗E {P = λ a → ⟦ QG' piv a ⟧c Spec}
                           (λ p1 hi e2 pf sHi →
                              specJoin piv e1 e2 (lower pf) (sLo true) (sHi true))
                           inner) t }

  -- INTRINSICALLY VERIFIED QUICKSORT.  Stated directly as the `Cover`
  -- below: there is deliberately no `(m : Bag) → Σ[ out ] Perm out m`
  -- spelling of it, because that name would already be outside.
  --
  -- It is a MAP OUT OF TOP, so the generic interface applies.
  -- The specification grammar IS a `⊕ᴰ` over the output bag, so reading
  -- the sorted bag off it is the GENERIC `tagA` and running the program
  -- is the GENERIC `observe` (TheoryGrammar.SemanticAction).  The `.fst`
  -- that use sites used to write was exactly that, by hand -- and going
  -- through `tagA` is what keeps the permutation proof in the type
  -- right up to the externalisation.
  SpecG : TheoryTy ℓ-zero tt
  SpecG m = Σ[ out ∈ Bag ] Perm out m

  quicksortC : Cover SpecG
  quicksortC m _ = hyloC qfGuarded qcoalg qalgV (tt , m) tt

  qsortV : ⊤G ⊢ Δ Bag
  qsortV = tagA Bag ∘g quicksortC

-- It computes.
