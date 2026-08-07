{-
  IS `Proper` THE NON-IDENTITY MAPS?

  In a direct category the dichotomy is forced: a map either is the
  identity or is not, and `Direct/StrictDownset.agda`'s sieve `↡c`
  contains exactly the maps that strictly raise degree.  `↡-proper` says
  the identity is never in ↡; `Reflecting` -- an EXTRA hypothesis there,
  not a consequence -- says the converse, that every non-identity is in
  ↡, i.e. that ↡ is the maximal proper sieve.

  `Grading` does not have that dichotomy.  `Proper` is a field: a chosen
  family of types, constrained only by `deg<`.  This file settles what
  the relationship is, in both directions.

  ------------------------------------------------------------------
  THEOREM 1 (`proper→≢`, in `Direct/Divisibility.agda`).  Proper implies
  non-identity, always and unconditionally.  The proof is one line and
  goes entirely through the degree: `deg<` gives `deg n < deg m`, and if
  `n ≡ m` then `deg n ≡ deg m`, contradicting irreflexivity of `<` on ℕ.
  So `Proper ⊆ non-identity` is not a design choice, it is forced -- and
  it is the exact analogue of `↡-proper`.

  THEOREM 2 (`Proper-undetermined`).  The converse FAILS, and fails as
  badly as possible: `Proper` is not a function of the promodel.  ONE
  promodel here carries TWO gradings, `full` and `triv`, that disagree on
  the very same splitting.  So `Grading` is a PROPER generalisation of
  "direct category with Proper = non-identity": it is

      a direct structure  +  a chosen sub-relation of the non-identities
                             on which the degree is certified to drop,

  and the maximal choice is a property of the grading -- called
  `Saturated` below -- not part of the definition.  This is exactly ccl's
  `Reflecting`, restated where `Grading` can see it.

  THEOREM 3 (`no-saturated`).  And `Saturated` is not merely unrequired,
  it is sometimes UNACHIEVABLE.  The two-element promodel whose only
  operation is negation has a non-identity slot over every element and
  therefore -- by the `deg≤`-antisymmetry argument of
  `Instances/Group/NoGrading.agda`, in miniature -- a constant degree, so
  NO grading of it is saturated.  Demanding `Proper = non-identity` in
  the definition would have made `Grading` uninhabited there, rather than
  degenerately inhabited; degeneracy is the better failure mode, because
  it keeps the rigidity theorem statable.

  ------------------------------------------------------------------
  VERDICT.  `Proper` is strictly more general than "non-identity".  The
  inclusion `Proper ⊆ non-identity` always holds; the reverse is an
  optional property (`Saturated`) which is (i) not implied, (ii) not
  always satisfiable, and (iii) exactly ccl's `Reflecting`.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Direct.Proper where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Bool
  using (Bool ; true ; false ; not ; notnot ; true≢false ; false≢true)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as E using (⊥ ; ⊥*)
open import Cubical.Relation.Nullary using (¬_)

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Grading
open import TheoryGrammar.Direct.Divisibility

private variable ℓS ℓ ℓ' ℓX ℓP : Level

-- ==================================================================
-- PART A.  SATURATION -- "Proper IS non-identity".
--
-- Note the shape: this is a property OF A GRADING, mentioning only the
-- promodel and `Proper`.  Together with `Div.Graded.proper→≢` it pins
-- `Proper` to the non-identity slots up to logical equivalence.
-- ==================================================================

module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (Fib : Fibered σ ℓX ℓP) where

  open Div Fib

  Saturated : Grading Fib → Type (ℓ-max ℓS (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓX ℓP))))
  Saturated G =
    (o : σ .ops) (m : Fib .carrier (σ .resultSort o))
    (sp : Fib .Split o m) (a : σ .arities o)
    → ¬ (Path Elt (σ .sortOf o a , Fib .parts o m sp a) (σ .resultSort o , m))
    → G .Proper o m sp a

-- ==================================================================
-- PART B.  THE PROMODEL THAT SEPARATES THEM.
--
-- One sort, one UNARY operation, carrier ℕ, and a splitting of `m` is a
-- proof that `m` is a successor.  So `_◃₁_` is the predecessor relation:
-- the smallest promodel with a non-identity slot.  (Unary is deliberate:
-- nothing about the phenomenon needs a tensor.)
-- ==================================================================

predSig : SortedSig Unit ℓ-zero ℓ-zero
predSig .ops          = Unit
predSig .arities _    = Unit
predSig .sortOf _ _   = tt
predSig .resultSort _ = tt

predFib : Fibered predSig ℓ-zero ℓ-zero
predFib .carrier _     = ℕ
predFib .Split _ m     = Σ[ k ∈ ℕ ] (m ≡ suc k)
predFib .parts _ m sp _ = sp .fst

-- the honest grading: degree = the number itself, every slot proper
full : Grading predFib
full .deg _ n           = n
full .Proper _ _ _ _    = Unit
full .deg≤ _ m (k , p) _   = subst (k ≤_) (sym p) (≤-suc ≤-refl)
full .deg< _ m (k , p) _ _ = subst (k <_) (sym p) ≤-refl

-- the degenerate grading: it always exists (`Group/NoGrading`'s header
-- makes this point), and it is what makes `Proper` structure rather than
-- property
triv : Grading predFib
triv .deg _ _        = 0
triv .Proper _ _ _ _ = ⊥*
triv .deg≤ _ _ _ _   = ≤-refl
triv .deg< _ _ _ _ ()

module D    = Div predFib
module Full = D.Graded full
module Triv = D.Graded triv

-- 0 is the predecessor of 1 ...
step01 : (tt , 0) D.◃₁ (tt , 1)
step01 = D.slot tt 1 (0 , refl) tt

-- ... and this is a NON-IDENTITY map of the divisibility preorder
step01-≢ : ¬ (Path D.Elt (tt , 0) (tt , 1))
step01-≢ e = znots (cong snd e)

-- under `full` it is proper ...
step01-proper : (tt , 0) Full.◃ᵖ (tt , 1)
step01-proper = Full.pslot tt 1 (0 , refl) tt tt

-- ... and under `triv` NOTHING is proper.
triv-no-proper : {n m : D.Elt} → ¬ (n Triv.◃ᵖ m)
triv-no-proper (Triv.pslot o m sp a ())

-- ==================================================================
-- THEOREM 2.  `Proper` is not determined by the promodel: two gradings
-- of `predFib` disagree on the very same slot.
--
-- Read categorically: `Div predFib` is a fixed category, `full` and
-- `triv` are two direct structures on it, and the SIEVES they cut out
-- differ -- `full`'s ↡ is everything below, `triv`'s is empty.  A direct
-- category has one ↡; a graded promodel chooses one.
-- ==================================================================

Proper-undetermined :
  ((tt , 0) Full.◃ᵖ (tt , 1)) × (¬ ((tt , 0) Triv.◃ᵖ (tt , 1)))
Proper-undetermined = step01-proper , triv-no-proper

-- correspondingly: `full` is saturated, `triv` is not
full-saturated : Saturated predFib full
full-saturated o m sp a ne = tt

triv-not-saturated : ¬ (Saturated predFib triv)
triv-not-saturated sat = E.rec* (sat tt 1 (0 , refl) tt step01-≢)

-- ==================================================================
-- PART C.  SATURATION IS NOT ALWAYS ACHIEVABLE.
--
-- One sort, one unary operation, carrier `Bool`, and the unique
-- splitting of `m` has `not m` in its slot.  Every element is therefore
-- a non-identity slot of every element -- the two-object version of
-- `Group/NoGrading`'s `GroupLike` -- and the `deg≤`-antisymmetry
-- argument there collapses the degree, so `deg<` becomes unsatisfiable.
-- ==================================================================

notFib : Fibered predSig ℓ-zero ℓ-zero
notFib .carrier _      = Bool
notFib .Split _ _      = Unit
notFib .parts _ m _ _  = not m

module N = Div notFib

-- deg≤ instantiated at both elements, then antisymmetry: verbatim
-- `GroupObstruction.deg-const`, with `not` in place of `h ↦ h⁻¹ · m`.
not-deg-const : (G : Grading notFib) (b : Bool) → G .deg tt (not b) ≡ G .deg tt b
not-deg-const G b =
  ≤-antisym (G .deg≤ tt b tt tt)
            (subst (λ z → G .deg tt z ≤ G .deg tt (not b))
                   (notnot b)
                   (G .deg≤ tt (not b) tt tt))

not-≢ : (b : Bool) → ¬ (Path N.Elt (tt , not b) (tt , b))
not-≢ b e = ¬not≡ b (cong snd e)
  where
    ¬not≡ : (c : Bool) → ¬ (not c ≡ c)
    ¬not≡ false p = true≢false p
    ¬not≡ true  p = false≢true p

-- THEOREM 3.  No grading of `notFib` is saturated.
no-saturated : (G : Grading notFib) → ¬ (Saturated notFib G)
no-saturated G sat =
  ¬m<m (subst (λ n → n < G .deg tt true)
              (not-deg-const G true)
              (G .deg< tt true tt tt (sat tt true tt tt (not-≢ true))))
