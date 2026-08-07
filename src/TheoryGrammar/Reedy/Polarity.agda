{-
  IS `⊗ˢ` / `Focus` A REEDY STRUCTURE?  AND CAN POSITIVITY BE STATED?

  Two conjectures are tested here, and the file's job is to separate the
  half of each that is true from the half that is not.  The Reedy
  structure itself is in `TheoryGrammar.Reedy.Base`; c-c-l has none.

  ================================================================
  (b)  THE ⊗ˢ / Focus SPLIT.
  ================================================================

  Conjecture: `⊗ˢ` (whole → parts, degree LOWERING) and `⊸ᶠ`/`Focus`
  (part → whole, degree RAISING) are the C₋ / C₊ of a Reedy structure,
  with `Focus` playing the latching/matching object.

  VERDICT: half right, and the false half is the axiom that carries all
  the content.

  TRUE — the direction claim, and the shape claim.  §1 below makes the
  two motions into honest relations on the total space of the promodel
  and PROVES the degree conditions:

      ≽-lowers  :  m ≽ x  →  deg x ≤ deg m          (from Grading.deg≤)
      ≽-strict  :  proper →  deg x <  deg m          (from Grading.deg<)
      ≼-raises  :  x ≼ w  →  deg x ≤ deg w

  and the shape claim is right too:  ⊗ˢ o A m = Σ over splittings of a Π
  over slots, a COLIMIT over the decompositions below m; ⊸ᶠ A B x = Π
  over focused splittings, a LIMIT over the embeddings above x.  Those
  are literally the latching and matching shapes.  Compare c-c-l's
  `Direct/StrictDownset.↡Psh` (a Σ over maps INTO c of lower degree) and
  `Direct/StrictUpset.↟Fun` (a Σ over maps OUT OF x of higher degree).

  FALSE — that this is a Reedy structure.  Three independent reasons,
  in increasing order of severity.

  (i)  ≽ and ≼ are not two subcategories of one category; they are one
       span read in two directions.  `Focus` is by its own comment "a
       splitting seen from slot i" — the same datum as `Split`, reindexed.
       In a Reedy category C₋ and C₊ generate C and meet only in the
       identities; here each is the opposite of the other, so their
       composites run back and forth and generate a groupoid-flavoured
       thing, not a factorisation system.

  (ii) `Focus` is not even CONNECTED to `Split`.  The record has fields
       `SplitAt / whole / Rest / restOf / restSlot` and NO axiom relating
       `SplitAt x` to `Fib .Split o (whole sa)`.  So nothing about the
       degree of `whole sa` is derivable from a `Grading`, which grades
       only `Split`.  §1 has to add `FocusCoherent` to say it.  That gap
       is a genuine defect independent of Reedy, and is improvement #1
       of the report.

  (iii) UNIQUE FACTORISATION IS FALSE, and provably so.  §2.  The Reedy
       axiom, specialised to this span at the identity of a whole `m`,
       says: the object you pass through when you lower out of `m` and
       raise back into `m` is unique.  Here that object is
       `parts o m sp a`, which varies with BOTH the splitting `sp` and
       the slot `a`.  `Fibered`'s header is explicit that `Split o m` is
       deliberately not a proposition ("`w` has `length w + 1` cuts"),
       so the axiom is contradicted by design, not by accident.  §2
       proves it for a fifteen-line self-contained promodel (ℕ under
       addition) so that the refutation depends on no instance file.

  So the honest categorical reading of `⊗ˢ` / `⊸ᶠ` is: a multicategorical
  tensor and its residual, i.e. LEFT AND RIGHT ADJOINTS along one span
  (a Day convolution and its right Kan extension).  Latching and matching
  objects are also a left and a right Kan extension along an inclusion,
  which is exactly why the two look alike — but the resemblance is the
  generic "Lan lowers, Ran raises" pattern, not Reedy.  The Reedy content
  is the factorisation, and the factorisation is what fails.

  ================================================================
  (c)  KORONKEVICH & BOWMAN'S LEVEL ALGEBRA, AND POSITIVITY.
  ================================================================

  §3.  The level algebra transfers exactly, and needs no Reedy at all.
  Their data is a set of levels L, a reference relation with
  `l_s + 1 R l_s`, and a composite rule `l_f = F(l_i, l_o, l_c, …)` with
  `F ≥` each argument.  Written against a signature that is, verbatim,

      F ≥ each argument      ==   Grading.deg≤   (a part never outgrows
                                                  the whole)
      l_s + 1  R  l_s        ==   Grading.deg<   at a `Proper` slot

  and `gradingIsKB` below is the (content-free, as it should be)
  translation.  `Grading` IS a KB level algebra with L = ℕ, ≼ = ≤,
  R = >.  If a level algebra needs several level arguments combined
  non-uniformly, c-c-l's `Direct/Product.agda` already supplies
  `_×ˡᵉˣWFOrder_` and the product order, and `Grading` would need only
  its ℕ replaced by an abstract `WFOrder` — improvement #2.

  §4.  POSITIVITY IS NOT A REEDY STRUCTURE, and the obstruction is
  elementary.  Polarity composes by multiplication in {±1}: a positive
  occurrence inside a negative one is negative, and a negative inside a
  negative is POSITIVE.  Hence

      {positive occurrences}  is closed under composition and contains
                              the identities — a wide subcategory;
      {negative occurrences}  contains no identity (identities are
                              positive) and is NOT closed under
                              composition (neg ∘ neg = pos).

  So C₋ = negative occurrences is not a candidate for a wide subcategory
  at all, and the unique-factorisation axiom has nothing to hold OF.
  `negNotClosed` and `negLacksId` below prove both halves by `refl`.
  The user's proposed dictionary

      stratification : direct  ::  positivity : Reedy

  therefore fails on the right-hand side.  The left-hand side is fine
  and is §3.

  What positivity actually is, categorically, is the statement that a
  mixed-variance functor C^op × C → C factors through the projection —
  a variance condition, whose payoff is the existence of an initial
  algebra, by a DIFFERENT argument from well-founded degree descent.
  Reedy cannot bridge them because Reedy is still a degree argument.

  AND THE PUNCHLINE THAT MAKES THE QUESTION MOOT HERE.  This development
  already enforces positivity, and it does so by exactly the mechanism
  Koronkevich & Bowman conjecture: a hierarchy.  `TheoryGrammar.
  Inductive`'s description language

      ⌜_⌝ | Var | ⊕e | &e | ⊗e

  has NO exponential former, so every occurrence in a description is
  positive syntactically, with nothing to polarise; and
  `TheoryGrammar.Grading`'s `Guarded` — "`Var` at the top of a
  description is exactly what fails to be guarded, that is left
  recursion, correctly rejected" — is STRICT positivity, enforced by the
  ℕ-degree.  So the conjecture "a universe hierarchy could enforce
  positivity rather than stratification" is, in this framework, already
  true, realised by `deg<` at `⊗e`.  Extending it to Tranquilli's
  genuinely mixed-variance setting requires adding an exponential former
  to `Functor`, at which point the correct extra structure is a Z/2
  polarity grading on positions — `PolGrading` in §4 — and NOT a second
  wide subcategory.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Reedy.Polarity where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Bool
  using (Bool ; true ; false ; not ; if_then_else_ ; true≢false)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as ⊥
open import Cubical.Relation.Nullary using (¬_)

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Grading

private variable ℓS ℓ ℓ' ℓX ℓP ℓL ℓR : Level

-- ==================================================================
-- §1.  THE TWO MOTIONS, AS RELATIONS ON THE TOTAL SPACE.
--
-- Both are given as inductive families so that no sort-coercion or
-- transport ever appears; this is the same trick `Fibered` uses to keep
-- `Split` indexed by its output.
-- ==================================================================

module Motions {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
               (Fib : Fibered σ ℓX ℓP) (G : Grading Fib) where

  Tot : Type (ℓ-max ℓS ℓX)
  Tot = Σ[ s ∈ S ] Fib .carrier s

  degT : Tot → ℕ
  degT (s , m) = G .deg s m

  val : Tot → Σ[ s ∈ S ] Fib .carrier s
  val t = t

  -- ------------------------------------------------------------------
  -- LOWERING: the projection out of a splitting.  This is the motion
  -- `⊗ˢ` ranges over -- `⊗ˢ o A m` is a Σ over `Split o m` of a Π over
  -- the slots, i.e. a colimit over exactly the `m ≽ _` below `m`.
  -- ------------------------------------------------------------------
  data _≽_ : Tot → Tot → Type (ℓ-max ℓS (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓX ℓP)))) where
    proj : (o : σ .ops) (m : Fib .carrier (σ .resultSort o))
           (sp : Fib .Split o m) (a : σ .arities o)
         → (σ .resultSort o , m) ≽ (σ .sortOf o a , Fib .parts o m sp a)

  -- PROVED: lowering never gains degree.
  ≽-lowers : {u v : Tot} → u ≽ v → degT v ≤ degT u
  ≽-lowers (proj o m sp a) = G .deg≤ o m sp a

  -- PROVED: at a `Proper` slot it strictly drops.
  ≽-strict : (o : σ .ops) (m : Fib .carrier (σ .resultSort o))
             (sp : Fib .Split o m) (a : σ .arities o)
           → G .Proper o m sp a
           → degT (σ .sortOf o a , Fib .parts o m sp a)
             < degT (σ .resultSort o , m)
  ≽-strict o m sp a pr = G .deg< o m sp a pr

  -- ------------------------------------------------------------------
  -- RAISING: embedding a part into a whole, via `Focus`.
  --
  -- IMPROVEMENT #1.  `Focus` as it stands in `TheoryGrammar.Fibered`
  -- has no field relating `SplitAt x` to `Fib .Split o (whole sa)`, so
  -- a `Grading` -- which grades only `Split` -- says NOTHING about
  -- `deg (whole sa)`.  The raising condition is therefore not derivable
  -- as the record is written.  `FocusCoherent` is the missing axiom,
  -- and it is the obvious one: a focused splitting forgets to a genuine
  -- splitting of its own whole, whose slot i is what you focused on.
  --
  -- Proposed as an addition to `Focus` itself (two fields, no proof
  -- obligation on existing instances beyond what they already have,
  -- since every instance builds `SplitAt` out of `Split` anyway).
  -- ------------------------------------------------------------------
  record FocusCoherent (o : σ .ops) (i : σ .arities o) (Φ : Focus Fib o i)
    : Type (ℓ-max ℓ' (ℓ-max ℓX ℓP)) where
    field
      forget : {x : Fib .carrier (σ .sortOf o i)} (sa : Φ .SplitAt x)
             → Fib .Split o (Φ .whole sa)
      at-i   : {x : Fib .carrier (σ .sortOf o i)} (sa : Φ .SplitAt x)
             → Fib .parts o (Φ .whole sa) (forget sa) i ≡ x

  open FocusCoherent public

  module _ (o : σ .ops) (i : σ .arities o)
           (Φ : Focus Fib o i) (Φc : FocusCoherent o i Φ) where

    data _≼_ : Tot → Tot → Type (ℓ-max ℓS (ℓ-max ℓ' (ℓ-max ℓX ℓP))) where
      emb : (x : Fib .carrier (σ .sortOf o i)) (sa : Φ .SplitAt x)
          → (σ .sortOf o i , x) ≼ (σ .resultSort o , Φ .whole sa)

    -- PROVED (given coherence): raising never loses degree.
    ≼-raises : {u v : Tot} → u ≼ v → degT u ≤ degT v
    ≼-raises (emb x sa) =
      subst (λ z → G .deg (σ .sortOf o i) z ≤ G .deg (σ .resultSort o) (Φ .whole sa))
            (Φc .at-i sa)
            (G .deg≤ o (Φ .whole sa) (Φc .forget sa) i)

-- ==================================================================
-- §2.  UNIQUE FACTORISATION FAILS.
--
-- The Reedy axiom, specialised to the identity of a whole `m`: lower
-- out of `m` and raise straight back in.  The intermediate object is
-- `parts o m sp a`, determined by a splitting AND a slot, and the axiom
-- demands it be unique.
-- ==================================================================

module Interpolant {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
                   (Fib : Fibered σ ℓX ℓP) where

  Tot : Type (ℓ-max ℓS ℓX)
  Tot = Σ[ s ∈ S ] Fib .carrier s

  -- an interpolant of `id m`: a splitting together with a slot to pass
  -- through
  Interp : (o : σ .ops) → Fib .carrier (σ .resultSort o) → Type (ℓ-max ℓ' ℓP)
  Interp o m = Fib .Split o m × σ .arities o

  through : (o : σ .ops) (m : Fib .carrier (σ .resultSort o))
          → Interp o m → Tot
  through o m (sp , a) = σ .sortOf o a , Fib .parts o m sp a

  -- THE REEDY AXIOM at `id m`, in the only form it can take here.
  UniqueInterp : (o : σ .ops) → Fib .carrier (σ .resultSort o)
               → Type (ℓ-max ℓS (ℓ-max ℓ' (ℓ-max ℓX ℓP)))
  UniqueInterp o m = (u v : Interp o m) → through o m u ≡ through o m v

-- ------------------------------------------------------------------
-- The counterexample, self-contained: ℕ under addition, one sort, one
-- binary operation.  `Split o n` = the ways of writing n as u + v, of
-- which there are n+1 -- the arithmetic shadow of `Fibered`'s own
-- remark that a string `w` has `length w + 1` cuts.
-- ------------------------------------------------------------------
module ℕCounterexample where

  σℕ : SortedSig Unit ℓ-zero ℓ-zero
  σℕ .ops        = Unit
  σℕ .arities _  = Bool
  σℕ .sortOf _ _ = tt
  σℕ .resultSort _ = tt

  Fibℕ : Fibered σℕ ℓ-zero ℓ-zero
  Fibℕ .carrier _ = ℕ
  Fibℕ .Split _ n = Σ[ u ∈ ℕ ] Σ[ v ∈ ℕ ] (u + v ≡ n)
  Fibℕ .parts _ n (u , v , _) b = if b then u else v

  open Interpolant Fibℕ

  -- two ways of cutting 1
  cut₀ cut₁ : Fibℕ .Split tt 1
  cut₀ = 0 , 1 , refl
  cut₁ = 1 , 0 , refl

  proj₂nd : Tot → ℕ
  proj₂nd (_ , n) = n

  -- THEOREM.  The whole-to-parts / parts-to-whole span does NOT admit
  -- unique lowering-then-raising factorisation.  Hence it is not a
  -- Reedy structure, and no amount of extra coherence on `Focus` can
  -- make it one: the failure is in `Fibered` itself.
  noUniqueInterp : ¬ (UniqueInterp tt 1)
  noUniqueInterp u = znots (cong proj₂nd (u (cut₀ , true) (cut₁ , true)))

  -- for the record: the two interpolants really are 0 and 1
  _ : through tt 1 (cut₀ , true) ≡ (tt , 0)
  _ = refl

  _ : through tt 1 (cut₁ , true) ≡ (tt , 1)
  _ = refl

-- ==================================================================
-- §3.  THE KORONKEVICH–BOWMAN LEVEL ALGEBRA.
--
-- "Type Universes as Kripke Worlds" §5 abstracts their system to: a set
-- of levels L; a relation `l_r R l_s` between a reference's level and
-- what it stores, with `l_s + 1 R l_s`; and a function
-- `l_f = F(l_i, l_o, l_c, …)` giving a composite's level from its
-- parts', theirs being `≥`.
--
-- Read over a signature, `F ≥ each part` is precisely "no part
-- outgrows its whole", and `l_s + 1 R l_s` is precisely "a reference
-- step is a strict increase".  Those are `deg≤` and `deg<`.
-- ==================================================================

record KBLevelAlgebra {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
                      (Fib : Fibered σ ℓX ℓP) ℓL ℓR
  : Type (ℓ-max ℓS (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓX (ℓ-max (ℓ-suc ℓP)
          (ℓ-max (ℓ-suc ℓL) (ℓ-suc ℓR))))))) where
  field
    -- the levels
    L    : Type ℓL
    lvl  : (s : S) → Fib .carrier s → L
    -- KB's `≥`, oriented part-below-whole
    _≼_  : L → L → Type ℓR
    -- KB's reference relation R, oriented stored-below-reference
    _R_  : L → L → Type ℓR

    -- which slots are REFERENCES (KB's `l_s + 1 R l_s` applies at these)
    Ref  : (o : σ .ops) (m : Fib .carrier (σ .resultSort o))
         → Fib .Split o m → σ .arities o → Type ℓP

    -- F: the composite's level dominates every part's level
    F-dom : (o : σ .ops) (m : Fib .carrier (σ .resultSort o))
            (sp : Fib .Split o m) (a : σ .arities o)
          → lvl _ (Fib .parts o m sp a) ≼ lvl _ m

    -- R: at a reference slot the stored level is strictly below
    R-step : (o : σ .ops) (m : Fib .carrier (σ .resultSort o))
             (sp : Fib .Split o m) (a : σ .arities o)
           → Ref o m sp a
           → lvl _ (Fib .parts o m sp a) R lvl _ m

open KBLevelAlgebra public

-- A grading IS a KB level algebra, with L = ℕ, ≼ = ≤, R = <, and KB's
-- reference slots = `Proper` slots.  Every component is the identity:
-- there is no content here, which is the finding.
gradingIsKB : {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (Fib : Fibered σ ℓX ℓP)
            → Grading Fib → KBLevelAlgebra Fib ℓ-zero ℓ-zero
gradingIsKB Fib G .L      = ℕ
gradingIsKB Fib G .lvl    = G .deg
gradingIsKB Fib G ._≼_    = _≤_
gradingIsKB Fib G ._R_    = _<_
gradingIsKB Fib G .Ref    = G .Proper
gradingIsKB Fib G .F-dom  = G .deg≤
gradingIsKB Fib G .R-step = G .deg<

-- ==================================================================
-- §4.  POLARITY, AND WHY IT IS NOT A REEDY SPLIT.
--
-- Polarity is a Z/2 grading on OCCURRENCES: an occurrence to the left
-- of an arrow flips sign, and polarities of nested occurrences
-- multiply.  Write + as `true`.
-- ==================================================================

Pol : Type
Pol = Bool

pattern + = true
pattern - = false

-- the polarity of an occurrence-inside-an-occurrence
infixl 7 _∘p_
_∘p_ : Pol → Pol → Pol
+ ∘p q = q
- ∘p q = not q

-- the identity occurrence is positive
idPol : Pol
idPol = +

-- ------------------------------------------------------------------
-- THE POSITIVE CLASS IS A WIDE SUBCATEGORY.
-- ------------------------------------------------------------------

posHasId : idPol ≡ +
posHasId = refl

posClosed : (p q : Pol) → p ≡ + → q ≡ + → p ∘p q ≡ +
posClosed p q pp qq i = pp i ∘p qq i

-- ------------------------------------------------------------------
-- THE NEGATIVE CLASS IS NOT.  Two independent failures, both by `refl`.
--
-- This is the refutation of "C₋ = negative occurrences": a Reedy C₋ must
-- be a WIDE SUBCATEGORY, and the negative occurrences are neither wide
-- (no identity) nor a subcategory (not closed under composition).  With
-- no candidate for C₋ there is nothing for the unique-factorisation
-- axiom to be true or false of, so the conjecture does not merely fail
-- -- it does not typecheck as a conjecture.
-- ------------------------------------------------------------------

negNotClosed : - ∘p - ≡ +
negNotClosed = refl

negLacksId : ¬ (idPol ≡ -)
negLacksId = true≢false

-- and, stated as the closure property directly: any composition-closed
-- class containing a negative occurrence contains a positive one
negClosureCollapses : (N : Pol → Type ℓ)
                    → ((p q : Pol) → N p → N q → N (p ∘p q))
                    → N - → N +
negClosureCollapses N cl n = cl - - n n

-- ------------------------------------------------------------------
-- WHAT TO USE INSTEAD.  A polarity grading is an EXTRA Z/2 label on
-- slots, orthogonal to the ℕ degree, not a second subcategory.  The
-- termination condition then reads: an occurrence at NEGATIVE polarity
-- must strictly drop degree (that is stratification, still needed
-- because negative recursion has no initial algebra); an occurrence at
-- POSITIVE polarity need not (that is positivity, and it is discharged
-- by the initial-algebra argument instead).
--
-- Stated over an existing `Grading`, this is a two-line refinement --
-- and note it degenerates to the present `Grading` when every slot is
-- negative, which is why nothing in the development changes.
-- ------------------------------------------------------------------

record PolGrading {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
                  (Fib : Fibered σ ℓX ℓP) (G : Grading Fib)
  : Type (ℓ-max ℓS (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓX ℓP)))) where
  field
    -- the polarity of each slot of each operation
    pol : (o : σ .ops) → σ .arities o → Pol

    -- ONLY negative slots owe a strict decrease; positive ones are
    -- discharged by positivity, and may sit at the same level.
    neg-strict : (o : σ .ops) (m : Fib .carrier (σ .resultSort o))
                 (sp : Fib .Split o m) (a : σ .arities o)
               → pol o a ≡ -
               → G .Proper o m sp a

open PolGrading public

-- The present development is the all-negative case: `Guarded` in
-- `TheoryGrammar.Grading` demands a strict drop at every recursive
-- occurrence, which is stratification everywhere.  It is SOUND because
-- the description language (`⌜_⌝ | Var | ⊕e | &e | ⊗e`) has no
-- exponential, hence no negative occurrence to be conservative about.
allNegative : {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (Fib : Fibered σ ℓX ℓP)
              (G : Grading Fib)
            → ((o : σ .ops) (m : Fib .carrier (σ .resultSort o))
               (sp : Fib .Split o m) (a : σ .arities o) → G .Proper o m sp a)
            → PolGrading Fib G
allNegative Fib G allProper .pol _ _ = -
allNegative Fib G allProper .neg-strict o m sp a _ = allProper o m sp a
