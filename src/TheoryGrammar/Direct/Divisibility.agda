{-
  THE DIVISIBILITY PREORDER OF A PROMODEL IS A DIRECT CATEGORY.

  `Instances/Group/NoGrading.agda` closes with a criterion rather than a
  theorem:

      inductive grammars exist exactly when the DIVISIBILITY PREORDER
      of the theory is well-founded.

  That sentence names an object -- the divisibility preorder -- which the
  development had never built.  This file builds it, and identifies the
  structure `Grading` puts on it with the DIRECT-CATEGORY structure of
  `Cubical.Categories.Direct.Base`.

  ------------------------------------------------------------------
  What a direct category is.

  ccl's `DirectStr C Wo` is a functor `C → (D,≤)` into (the thin category
  on) a well-founded order: a degree on objects such that EVERY map is
  non-decreasing.  `Direct/StrictDownset.agda` then carves out the strict
  part: `x ≺ y` is `deg x < deg y`, `↡ y` is the sieve of maps into `y`
  from strictly smaller objects, and `▷` is "sections over ↡".  The
  identity is never in `↡ y` (`↡-proper`), so ↡ is a proper sieve; the
  extra hypothesis under which it is the LARGEST proper sieve -- i.e.
  under which "strict" and "non-identity" coincide -- is called
  `Reflecting`, and it is an assumption, not a consequence.

  ------------------------------------------------------------------
  The divisibility preorder, and why the closure is real work.

  `Fibered` gives a RELATION, not a category:

      slot :  n  is the a-th part of some o-splitting of  m.

  Write this `n ◃₁ m`.  It is reflexive for no reason and transitive for
  no reason, so the category one wants is its reflexive-transitive
  closure `n ≼ m`, built here as a data type of CHAINS.

  The transitivity failure is not hypothetical.  Take strings with binary
  concatenation.  Then `n ◃₁ m` says "n is a prefix or a suffix of m",
  and

      "a"  ◃₁  "ab"      (prefix)
      "ab" ◃₁  "cab"     (suffix)
      "a"  ◃₁  "cab"     is FALSE -- "a" is neither a prefix nor a suffix

  so `◃₁` is not transitive at the very instance the development is built
  around.  The closure `≼` is the INFIX relation, and the fact that it is
  strictly bigger than `◃₁` is exactly why `Grammar/Later/Infix.agda`
  exists as a separate order from `Grammar/Later/SuffixOrder.agda`.
  See `Direct/Associativity.agda` for what would have to be assumed to
  make `◃₁` transitive on the nose.

  Everything below is nevertheless UNCONDITIONAL: no associativity, no
  identities, no `LaxPoint`.  The chains carry the bookkeeping, and the
  degree bound composes along them because `≤` is transitive.

  ------------------------------------------------------------------
  The theorem.

      deg≤  is  "every map of Div is non-decreasing"      (⟹ DirectStr)
      deg<  is  "a PROPER map is ≺-strict"                (⟹ lands in ↡)

  so `mkDirectStr` applies verbatim, and `DirectNotation`'s `_≺_` on
  `Div` is DEFINITIONALLY the relation `Grading`'s `Grade` module pulls
  back from ℕ to build `▷` (`≺≡≺Grade` below is `refl`).

  ------------------------------------------------------------------
  Orientation.  `Div [ n , m ]` is "n divides m", so maps point from
  divisor to multiple and the degree RISES: that is ccl's `DirectStr`
  on the nose, and `Div ^op` is the inverse category.  The recursion of
  a parser runs the other way -- from a whole to its parts, degree
  falling -- so the parser lives over `Div ^op`, which is the sense in
  which the reader will want to call this "inverse".

  ------------------------------------------------------------------
  ccl NOTE.  `Cubical.Categories.Direct.Base` and
  `Cubical.Categories.Direct.StrictDownset` resolve from this repo and
  are imported for real.  `Direct/Instances/Nat.agda` and
  `Direct/LaterPresentation.agda` do NOT -- they live on ccl's `lob`
  branch, not on the branch checked out at `~/cubical-categorical-logic`.
  `ℕWFOrder` below is therefore re-derived locally, and is a copy of
  `Cubical/Categories/Direct/Instances/Nat.agda`'s except that it uses
  the Σ-style `<` of `Cubical.Data.Nat.Order` (which is what `Grading`
  is stated with) rather than the recursive one.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Direct.Divisibility where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as E using (⊥)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Induction.WellFounded
open import Cubical.HITs.PropositionalTruncation as PT
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Direct.Base
  using (WFOrder ; WFOrder→Cat ; DirectStr ; mkDirectStr ; module DirectNotation)

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Grading

private variable ℓS ℓ ℓ' ℓX ℓP ℓA ℓV : Level

-- a sub-relation of a well-founded relation is well-founded
wfSub : {ℓI ℓR ℓQ : Level} {I : Type ℓI}
        {_R_ : I → I → Type ℓR} {_Q_ : I → I → Type ℓQ}
      → ({x y : I} → x R y → x Q y) → WellFounded _Q_ → WellFounded _R_
wfSub {I = I} {_R_ = _R_} {_Q_ = _Q_} sub wq i = go i (wq i)
  where
    go : (x : I) → Acc _Q_ x → Acc _R_ x
    go x (acc h) = acc λ y r → go y (h y (sub r))

-- ==================================================================
-- ℕ AS A WELL-FOUNDED ORDER.  (Local copy; see the ccl NOTE above.)
-- ==================================================================

ℕWFOrder : WFOrder ℓ-zero ℓ-zero
ℕWFOrder = record
  { D       = ℕ
  ; isSetD  = isSetℕ
  ; _<_     = _<_
  ; isProp< = λ a b → isProp≤ {suc a} {b}
  ; trans<  = λ {a} {b} {c} → <-trans {a} {b} {c}
  ; wf<     = <-wellfounded
  }

-- `Grading` speaks the Σ-style `≤`; `WFOrder` speaks `< ⊎ Eq.≡`.  The
-- translation is `≤-split`, and it is the only friction between the two
-- developments.
≤→Wo≤ : {a b : ℕ} → a ≤ b → WFOrder._≤_ ℕWFOrder a b
≤→Wo≤ p with ≤-split p
... | inl q = inl q
... | inr q = inr (Eq.pathToEq q)

-- LEVEL BUREAUCRACY, isolated here so it does not pollute the theorems.
--
-- `Direct/StrictDownset.agda` -- the file that actually builds ↡ and ▷
-- -- is stated for `{C : Category ℓ ℓ'} {Wo : WFOrder ℓD ℓ'}`: the
-- order's `<` must live at C's HOM level.  Our hom-sets are truncated
-- chains, so they sit at the signature's level, while ℕ's `<` sits at
-- ℓ-zero.  `Lift` is the whole of the mismatch.
ℕWFOrder↑ : (ℓ : Level) → WFOrder ℓ-zero ℓ
ℕWFOrder↑ ℓ = record
  { D       = ℕ
  ; isSetD  = isSetℕ
  ; _<_     = λ a b → Lift ℓ (a < b)
  ; isProp< = λ a b → isOfHLevelLift 1 (isProp≤ {suc a} {b})
  ; trans<  = λ p q → lift (<-trans (lower p) (lower q))
  ; wf<     = wfSub lower <-wellfounded
  }

≤→Wo≤↑ : {ℓ : Level} {a b : ℕ} → a ≤ b → WFOrder._≤_ (ℕWFOrder↑ ℓ) a b
≤→Wo≤↑ p with ≤-split p
... | inl q = inl (lift q)
... | inr q = inr (Eq.pathToEq q)

-- ==================================================================
-- PART A.  THE DIVISIBILITY RELATION AND ITS CLOSURE.
--
-- Objects live in the TOTAL SPACE of the carrier: a slot of an
-- o-splitting sits at `sortOf o a`, the whole sits at `resultSort o`,
-- and in a genuinely many-sorted theory those differ.  So the preorder
-- cannot be fibrewise -- it is on `Σ S carrier`, and its very existence
-- is a statement about the total space.  (For `S = Unit` this is a
-- distinction without a difference, and every instance in the
-- development that has a grading is single-sorted or nearly so.)
-- ==================================================================

module Div {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (Fib : Fibered σ ℓX ℓP) where

  Elt : Type (ℓ-max ℓS ℓX)
  Elt = Σ[ s ∈ S ] Fib .carrier s

  private
    ℓ◃ : Level
    ℓ◃ = ℓ-max ℓS (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓX ℓP)))

    ℓ≼ : Level
    ℓ≼ = ℓ◃

  -- ONE-STEP DIVISIBILITY.  Data, not a proposition: a `◃₁` is a choice
  -- of operation, of splitting, and of slot -- i.e. a PARSE STEP.  It is
  -- truncated only when it is made into a hom-set, below.
  data _◃₁_ : Elt → Elt → Type ℓ◃ where
    slot : (o : σ .ops) (m : Fib .carrier (σ .resultSort o))
           (sp : Fib .Split o m) (a : σ .arities o)
         → (σ .sortOf o a , Fib .parts o m sp a) ◃₁ (σ .resultSort o , m)

  -- ... AND ITS REFLEXIVE-TRANSITIVE CLOSURE, as chains.
  infixr 5 _∷_
  data _≼_ : Elt → Elt → Type ℓ≼ where
    nil  : {m : Elt} → m ≼ m
    _∷_  : {n k m : Elt} → n ◃₁ k → k ≼ m → n ≼ m

  one : {n m : Elt} → n ◃₁ m → n ≼ m
  one s = s ∷ nil

  ≼-trans : {n k m : Elt} → n ≼ k → k ≼ m → n ≼ m
  ≼-trans nil      q = q
  ≼-trans (s ∷ p)  q = s ∷ ≼-trans p q

  -- ================================================================
  -- THE CATEGORY.
  --
  -- The chains are NOT a set (nothing makes them one), so the hom-sets
  -- are the propositional truncations: `Div` is the preorder REFLECTION
  -- of the parse-step graph.  Keeping the chains untruncated would be a
  -- different, larger category -- the free category on `◃₁` -- and
  -- nothing below distinguishes them, because every statement made about
  -- `Div` is about degrees and degrees are proof-irrelevant.
  -- ================================================================

  Div : Category (ℓ-max ℓS ℓX) ℓ≼
  Div .Category.ob            = Elt
  Div .Category.Hom[_,_] n m  = ∥ n ≼ m ∥₁
  Div .Category.id            = ∣ nil ∣₁
  Div .Category._⋆_ f g       = PT.rec2 squash₁ (λ p q → ∣ ≼-trans p q ∣₁) f g
  Div .Category.⋆IdL _        = squash₁ _ _
  Div .Category.⋆IdR _        = squash₁ _ _
  Div .Category.⋆Assoc _ _ _  = squash₁ _ _
  Div .Category.isSetHom      = isProp→isSet squash₁

  -- ==================================================================
  -- PART B.  A GRADING IS A DIRECT STRUCTURE.
  -- ==================================================================

  module Graded (G : Grading Fib) where

    degE : Elt → ℕ
    degE (s , m) = G .deg s m

    -- `deg≤` -- verbatim, one step
    mono₁ : {n m : Elt} → n ◃₁ m → degE n ≤ degE m
    mono₁ (slot o m sp a) = G .deg≤ o m sp a

    -- ... and along a chain, because `≤` is transitive.  THIS is where
    -- the missing associativity is paid for, and the price is nil.
    mono : {n m : Elt} → n ≼ m → degE n ≤ degE m
    mono nil     = ≤-refl
    mono (s ∷ p) = ≤-trans (mono₁ s) (mono p)

    monoT : {n m : Elt} → ∥ n ≼ m ∥₁ → degE n ≤ degE m
    monoT = PT.rec isProp≤ mono

    -- ================================================================
    -- THEOREM.  The divisibility preorder of a graded promodel is a
    -- direct category, with `deg` as its degree functor.
    -- ================================================================

    DivDirect : DirectStr Div ℕWFOrder
    DivDirect = mkDirectStr Div ℕWFOrder degE (λ f → ≤→Wo≤ (monoT f))

    open DirectNotation DivDirect public using (_≺_ ; isProp≺ ; wf≺ ; ≺-precomp ; ≺-postcomp)

    -- `_≺_` unfolds to `degE x < degE y` -- which is, on the nose, the
    -- relation `Grading`'s `Grade` module pulls back from ℕ.  So the two
    -- developments are not merely analogous here; they are the same
    -- definition, and the identification is `refl`.
    ≺≡deg< : (x y : Elt) → (x ≺ y) ≡ (degE x < degE y)
    ≺≡deg< x y = refl

    -- The same structure at the `Lift`ed order, which is the form
    -- `Direct/StrictDownset.agda` can consume (see `ℕWFOrder↑`).  It is
    -- the same theorem; only the level annotation differs.
    DivDirect↑ : DirectStr Div (ℕWFOrder↑ ℓ≼)
    DivDirect↑ = mkDirectStr Div (ℕWFOrder↑ ℓ≼) degE (λ f → ≤→Wo≤↑ (monoT f))

    -- ================================================================
    -- PROPER DIVISIBILITY: the part of the relation that lands in ↡.
    -- ================================================================

    data _◃ᵖ_ : Elt → Elt → Type ℓ◃ where
      pslot : (o : σ .ops) (m : Fib .carrier (σ .resultSort o))
              (sp : Fib .Split o m) (a : σ .arities o)
            → G .Proper o m sp a
            → (σ .sortOf o a , Fib .parts o m sp a) ◃ᵖ (σ .resultSort o , m)

    forget : {n m : Elt} → n ◃ᵖ m → n ◃₁ m
    forget (pslot o m sp a _) = slot o m sp a

    -- `deg<` -- verbatim
    strict₁ : {n m : Elt} → n ◃ᵖ m → n ≺ m
    strict₁ (pslot o m sp a pr) = G .deg< o m sp a pr

    -- A chain is ≺-strict as soon as it contains ONE proper step: the
    -- non-strict prefix and suffix are absorbed by `≤`.  This is
    -- `≺-precomp` / `≺-postcomp` of `DirectNotation`, seen concretely.
    _≺ᵈ_ : Elt → Elt → Type ℓ≼
    n ≺ᵈ m = Σ[ k ∈ Elt ] Σ[ l ∈ Elt ] ((n ≼ k) × (k ◃ᵖ l) × (l ≼ m))

    strict : {n m : Elt} → n ≺ᵈ m → n ≺ m
    strict (k , l , nk , kl , lm) =
      ≤-trans (≤<-trans (mono nk) (strict₁ kl)) (mono lm)

    ≺ᵈ-one : {n m : Elt} → n ◃ᵖ m → n ≺ᵈ m
    ≺ᵈ-one {n} {m} s = n , m , nil , s , nil

    -- ================================================================
    -- THEOREM.  Proper divisibility is well-founded.
    --
    -- This is the criterion `Group/NoGrading` names, discharged: the
    -- grading IS the proof that the divisibility preorder is
    -- well-founded, because well-foundedness transfers along the degree.
    -- ================================================================

    wf≺ᵈ : WellFounded _≺ᵈ_
    wf≺ᵈ = wfSub strict wf≺

    wf◃ᵖ : WellFounded _◃ᵖ_
    wf◃ᵖ = wfSub ≺ᵈ-one wf≺ᵈ

    -- ================================================================
    -- ... and the identity is never proper.  In ccl this is
    -- `StrictDownset.↡-proper` ("↡c omits the identity"); here it says
    -- `Proper` never holds of a slot equal to its own whole.  Note the
    -- proof goes entirely through the DEGREE -- which is why it is
    -- generic in the sorts, and why `Proper` can be compared to
    -- "non-identity" at all.  See `Direct/Proper.agda`.
    -- ================================================================

    ≺-irrefl : {x : Elt} → ¬ (x ≺ x)
    ≺-irrefl = ¬m<m

    proper→≢ : {n m : Elt} → n ◃ᵖ m → ¬ (n ≡ m)
    proper→≢ {n} {m} s e = ≺-irrefl (subst (λ z → z ≺ m) e (strict₁ s))

-- ==================================================================
-- PART C.  THE OBSTRUCTION, RE-READ.
--
-- `Instances/Group/NoGrading.agda` is imported and cited, not reproved,
-- in `Direct/Group.agda`.  The one-line summary: group-likeness makes
-- `_◃₁_` TOTAL (every element is a slot of every element), so `Div` is
-- the indiscrete category on the carrier -- one connected component,
-- every hom present, no object below any other.  A degree functor out of
-- it must be constant (that is `GroupObstruction.deg-const`), hence `↡`
-- is empty at every object, hence `▷` is terminal and `löb` is the
-- identity: it proves `∀ x. A x` from `∀ x. A x`.  "The divisibility
-- preorder collapses to a point" and "there is no induction" are the
-- same sentence.
-- ==================================================================
