{-
  THE MISSING RULE: consuming a `▷` INSIDE a tensor.

  `Graded.Guard.löb` is stated over `Ix`-families, and `Guard` gives no
  combinators at that level -- no `&`, no `⊕ᴰ`, no `Dec⟨_⟩`, no intro or
  elim.  So the moment a program uses `▷`, the only thing it can do with
  it is apply it at a point, and that pointfulness propagates upward
  through the whole step: every intermediate definition becomes an
  ELEMENT `X m` rather than a map `A ⊢ B`.  That is what happened to
  both CYKs, and the fix is here.

  Two things are needed and both are in this file.

  (1) `▷ᴬ`, the later at the level of GRAMMARS.  A "chart" is a family
      over the sorts, `M : (s : S) → TheoryTy ℓM s`, and

          ▷ᴬ M  :  TheoryTy _ s

      is again a grammar -- "M at every strictly smaller world".  So
      `▷ᴬ M ⊢ M s` is a map OF THE CALCULUS, and `löbᵍ` turns one into a
      cover `⊤G ⊢ M s`.  Nothing about this is new mathematics; it is
      `Guard`'s `▷`/`löb` with the nonterminal index removed, which is
      exactly what makes the result a grammar.

  (2) `dec-⊗▷`, the rule.  Deciding `⊗ˢ o A` needs the slot deciders AT
      THE SLOTS, and a guarded recursion has them only at strictly
      smaller worlds -- which is what the slots of a PROPER splitting
      are.  So the slot decider is a map `M (sortOf o a) ⊢ Dec⟨ A a ⟩`,
      the chart is available LATER, and the conclusion is

          ▷ᴬ M  ⊢  Dec⟨ ⊗ˢ o A ⟩

      a term.  This is the generic analogue of `Grammar/Later/Properties`'s

          ▷-app-NE : ⟨¬Nullable B⟩ → (B ⊗ ⊤) & ▷ A ⊢ B ⊗ A

      and it is what `Instances.Strings.CYK` used to have a FIXME about.

  WHAT STAYS POINTFUL, AND WHY IT MUST.  `dec-⊗▷` takes one hypothesis
  that is not a `⊢`:

      resource : (m) (sp) → ((a) → Proper o m sp a) ⊎ Refutes o A m sp

  "at this cut, either every slot is a proper part, or the cut is
  refuted".  It is indexed by a SPLITTING, and `TheoryTy` is a family
  over the CARRIER, so no grammar states it -- the same structural fact
  that makes the cut scan itself external.  It is one named obligation
  per instance and it is the ONLY one; everything downstream composes.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Decidable.Guarded where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.List
open import Cubical.Induction.WellFounded

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Graded
open import TheoryGrammar.Enumerable
open import TheoryGrammar.DP
open import TheoryGrammar.Decidable.Enumerated
open import TheoryGrammar.Decidable.Listable

private variable ℓS ℓ ℓ' ℓX ℓP ℓA ℓR ℓM ℓV ℓY : Level

module DecGuard {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
                (GS : GradedFib σ ℓX ℓP) where

  private
    Fib : Fibered σ ℓX ℓP
    Fib = GS .fib

  open DecEnum Fib public

  -- the DEPENDENCY order of the theory (`DP.DPGraded`): `v ≺ᵖ w` is "v
  -- is a proper slot of some splitting of w", read off `Split` /
  -- `parts` / `Proper`.  Every guarded consultation below goes through
  -- it rather than through the degree, which is what lets a schedule
  -- LIST the consultations -- see the note on `▷ᴾ`.
  open DPGraded GS public

  -- the level `_≺ᵖ_` lives at, named once
  ℓ≺ᵖ : Level
  ℓ≺ᵖ = ℓ-max ℓS (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓX ℓP)))

  -- ================================================================
  -- (1)  THE LATER, AT THE LEVEL OF GRAMMARS.
  -- ================================================================

  -- a CHART is a grammar at every sort at once
  SortFam : (ℓM : Level) → Type (ℓ-max ℓS (ℓ-max ℓX (ℓ-suc ℓM)))
  SortFam ℓM = (s : S) → TheoryTy ℓM s

  -- ... and its later is again a grammar
  ▷ᴬ : SortFam ℓM → {s : S} → TheoryTy (ℓ-max ℓS (ℓ-max ℓX ℓM)) s
  ▷ᴬ M {s} m = (s' : S) (m' : Fib .carrier s')
             → GS .deg s' m' < GS .deg s m → M s' m'

  -- the later is functorial, and forgetting to a smaller chart is a map
  ▷ᴬ-map : {M : SortFam ℓM} {N : SortFam ℓM} {s : S}
         → ((s' : S) → M s' ⊢ N s') → ▷ᴬ M {s} ⊢ ▷ᴬ N {s}
  ▷ᴬ-map f m r s' m' q = f s' m' (r s' m' q)

  -- DOWNWARD CLOSURE.  `▷ᴬ M` at `m` yields `▷ᴬ M` at every strictly
  -- smaller world -- transitivity of `<`, nothing more.  This is what
  -- lets the description recursion NEST: a `⊗e` inside a `⊗e` needs the
  -- later again at the slot, and without this it would only have the
  -- chart there.
  ▷ᴬ-dn : (M : SortFam ℓM) {s : S} (m : Fib .carrier s) → ▷ᴬ M m
        → (s' : S) (m' : Fib .carrier s')
        → GS .deg s' m' < GS .deg s m → ▷ᴬ M {s'} m'
  ▷ᴬ-dn M m later s' m' q s'' m'' q' = later s'' m'' (<-trans q' q)

  -- ================================================================
  -- LÖB, at the level of grammars.  The step is a TERM `▷ᴬ M ⊢ M s`,
  -- never an Agda function on an index -- which is the discipline
  -- `Grammar/Parser/RecursiveDescent.fixP` sets and which the
  -- `Ix`-level `Guard.löb` cannot enforce, since `Ix` is not a sort.
  -- ================================================================

  private
    descend : (M : SortFam ℓM) (st : (s : S) → ▷ᴬ M {s} ⊢ M s)
              (n : ℕ) → Acc _<_ n
            → (s : S) (m : Fib .carrier s) → GS .deg s m ≡ n → M s m
    descend M st n (acc h) s m p =
      st s m λ s' m' q →
        descend M st (GS .deg s' m')
                (h (GS .deg s' m') (subst (GS .deg s' m' <_) p q))
                s' m' refl

  löbᵍ : (M : SortFam ℓM) → ((s : S) → ▷ᴬ M {s} ⊢ M s)
       → (s : S) → ⊤G {s} ⊢ M s
  löbᵍ M st s m _ = descend M st (GS .deg s m) (<-wellfounded _) s m refl

  -- ================================================================
  -- (1b)  THE LATER OVER THE *DEPENDENCY* ORDER -- and it is the one a
  -- chart can be built from.
  --
  -- `▷ᴬ` is indexed by the DEGREE: "M at every strictly shorter world".
  -- That is enough to recurse and NOT enough to tabulate, because the
  -- worlds below a given degree are infinitely many (`DP`'s header:
  -- every span of length < 20, at every start position).  `▷ᴾ` is
  -- indexed by `_≺ᵖ_` instead -- "M at every PROPER SLOT of a splitting
  -- of this world" -- which is finitely many, is exactly what the
  -- recursion actually consults, and is therefore schedulable.
  --
  -- Nothing else changes: `▷ᴾ M` is again a grammar, `▷ᴾ M ⊢ M s` is
  -- again a map of the calculus, and `dec-⊗▷ᴾ` below is `dec-⊗▷` with
  -- `deg<` replaced by the `slot` constructor -- which carries the same
  -- fact, as data rather than as an inequality.
  -- ================================================================

  ▷ᴾ : SortFam ℓM → {s : S} → TheoryTy (ℓ-max ℓ≺ᵖ ℓM) s
  ▷ᴾ M {s} m = (w : World) → w ≺ᵖ (s , m) → M (w .fst) (w .snd)

  -- `▷ᴬ` is stronger, so a step written against `▷ᴾ` may be run by
  -- either.  (`≺ᵖ-deg` is the whole proof.)
  ▷ᴬ→▷ᴾ : (M : SortFam ℓM) {s : S} → ▷ᴬ M {s} ⊢ ▷ᴾ M {s}
  ▷ᴬ→▷ᴾ M m later w q = later (w .fst) (w .snd) (≺ᵖ-deg q)

  -- ================================================================
  -- (2)  THE RESOURCE HYPOTHESIS, DERIVED FROM TERMS.
  --
  -- `dec-⊗▷` below needs "at this cut, either every slot is a proper
  -- part, or the cut is refuted".  That statement is indexed by a
  -- SPLITTING, so it is not a grammar and instances were writing it by
  -- hand.  They need not: it FOLLOWS from three things, two of which
  -- are terms of the calculus and one of which is a fact about the
  -- grading, of the same kind as `deg<`:
  --
  --     probeR : ⊤G ⊢ Dec⟨ R s ⟩        the resource is decidable
  --     cert   : A a ⊢ R _              every slot certifies itself
  --     rProper                         all slots resourceful ⟹ all proper
  --
  -- `findΠ` (Enumerable) is what makes it work: it hands back the
  -- OFFENDING slot, which is exactly what `slotMiss` consumes.  So the
  -- last pointful definition leaves the instances and lands here, once.
  -- ================================================================

  module _ (o : σ .ops)
           (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
           (R : (s : S) → TheoryTy ℓR s)
           (probeR : (s : S) → ⊤G {s} ⊢ Dec⟨ R s ⟩)
           (cert : (a : σ .arities o) → A a ⊢ R (σ .sortOf o a))
           (rProper : (m : Fib .carrier (σ .resultSort o))
                      (sp : Fib .Split o m)
                    → ((a : σ .arities o) → R _ (Fib .parts o m sp a))
                    → (a : σ .arities o) → GS .Proper o m sp a)
           (ars : List (σ .arities o))
           (arsComplete : (a : σ .arities o) → a ∈L ars)
           where

    resourceOf : (m : Fib .carrier (σ .resultSort o)) (sp : Fib .Split o m)
               → ((a : σ .arities o) → GS .Proper o m sp a)
               ⊎ Refutes o A m sp
    resourceOf m sp =
      out (findΠ ars arsComplete λ a → probeR _ (Fib .parts o m sp a) tt)
      where
        out : _ → ((a : σ .arities o) → GS .Proper o m sp a)
                ⊎ Refutes o A m sp
        out (inl h)       = inl (rProper m sp h)
        out (inr (a , k)) = inr (slotMiss o A m sp a (R _) (cert a) k)

  -- ================================================================
  -- (3)  THE RULE.
  -- ================================================================

  module _ (o : σ .ops)
           (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
           (M : SortFam ℓM)
           -- the cut space, as for `dec-⊗-cuts`
           (sps : (m : Fib .carrier (σ .resultSort o))
                → List (Fib .Split o m))
           (complete : (m : Fib .carrier (σ .resultSort o))
                       (sp : Fib .Split o m) → sp ∈L sps m)
           -- THE ONE NON-`⊢` HYPOTHESIS.  See the header.
           (resource : (m : Fib .carrier (σ .resultSort o))
                       (sp : Fib .Split o m)
                     → ((a : σ .arities o) → GS .Proper o m sp a)
                     ⊎ Refutes o A m sp)
           -- slotwise decisions combine at ONE cut (arity finiteness)
           (atCut : (m : Fib .carrier (σ .resultSort o))
                    (sp : Fib .Split o m)
                  → ((a : σ .arities o) → Dec⟨ A a ⟩ (Fib .parts o m sp a))
                  → ⊗at o A m sp ⊎ Refutes o A m sp)
           -- and the slot decider: a MAP, out of the chart at that slot
           (d : (a : σ .arities o) → M (σ .sortOf o a) ⊢ Dec⟨ A a ⟩)
           where

    dec-⊗▷ : ▷ᴬ M {σ .resultSort o} ⊢ Dec⟨ ⊗ˢ o A ⟩
    dec-⊗▷ m later =
      dec-⊗-cuts o A m (sps m) (complete m) cut
      where
        -- at a cut whose slots are all proper, every slot is strictly
        -- smaller (`deg<`), so `later` supplies the chart there and the
        -- slot decider `d` is applied to it.  That is the whole content
        -- of "the recursive call is legal at a proper part".
        use : (sp : Fib .Split o m)
            → ((a : σ .arities o) → GS .Proper o m sp a)
            → ⊗at o A m sp ⊎ Refutes o A m sp
        use sp pr = atCut m sp λ a →
          d a (Fib .parts o m sp a)
              (later _ (Fib .parts o m sp a) (GS .deg< o m sp a (pr a)))

        cut : (sp : Fib .Split o m) → ⊗at o A m sp ⊎ Refutes o A m sp
        cut sp = go (resource m sp)
          where go : _ → ⊗at o A m sp ⊎ Refutes o A m sp
                go (inl pr) = use sp pr
                go (inr k)  = inr k

    -- THE SAME RULE, OVER `_≺ᵖ_`.  Line for line `dec-⊗▷`, except that
    -- the licence to recurse at a slot is the `slot` CONSTRUCTOR --
    -- "this is a proper slot of this splitting of this world" -- rather
    -- than the inequality `deg<` it implies.  Keeping the constructor is
    -- what makes the consultation addressable: a schedule can list the
    -- slots of a splitting, and cannot list the worlds of smaller
    -- degree.
    dec-⊗▷ᴾ : ▷ᴾ M {σ .resultSort o} ⊢ Dec⟨ ⊗ˢ o A ⟩
    dec-⊗▷ᴾ m later =
      dec-⊗-cuts o A m (sps m) (complete m) cut
      where
        use : (sp : Fib .Split o m)
            → ((a : σ .arities o) → GS .Proper o m sp a)
            → ⊗at o A m sp ⊎ Refutes o A m sp
        use sp pr = atCut m sp λ a →
          d a (Fib .parts o m sp a)
              (later (σ .sortOf o a , Fib .parts o m sp a)
                     (slot o m sp a (pr a)))

        cut : (sp : Fib .Split o m) → ⊗at o A m sp ⊎ Refutes o A m sp
        cut sp = go (resource m sp)
          where go : _ → ⊗at o A m sp ⊎ Refutes o A m sp
                go (inl pr) = use sp pr
                go (inr k)  = inr k

  -- ================================================================
  -- (4)  LÖB, TABULATED.
  --
  -- `löbᵍ` solves the recurrence by re-descending: its `later` is a
  -- FUNCTION, so every consultation recomputes and nothing is shared.
  -- `löbᵀ` solves the SAME recurrence -- the same step term, unchanged
  -- -- against a `DP.Chain`, where the answers so far are DATA and a
  -- consultation is a projection.
  --
  -- The instance supplies one thing: a schedule at each world, i.e. an
  -- enumeration of its subproblems in which every element's
  -- dependencies appear later in the list.  `DP.solveAt≡` then says the
  -- tabulated answer IS `löb`'s, so the swap cannot change an answer
  -- and no test is a check on semantics.
  -- ================================================================

  module Tab (M : SortFam ℓM) where

    Motive : World → Type ℓM
    Motive w = M (w .fst) (w .snd)

    open Problem Motive public

    -- a schedule FOR ONE WORLD: a chain that contains it
    Sched : World → Type ℓ≺ᵖ
    Sched w = Σ[ is ∈ List World ] Σ[ _ ∈ Chain is ] (w ∈L is)

    -- the step of the calculus, as a `DP.Step`.  Σ-η and Unit-η are the
    -- whole of it: `▷ᴾ M {w .fst} (w .snd)` IS `▷ Motive w`.
    stepᵀ : ((s : S) → ▷ᴾ M {s} ⊢ M s) → Step
    stepᵀ st w later = st (w .fst) (w .snd) later

    löbᵀ : ((s : S) → ▷ᴾ M {s} ⊢ M s)
         → ((w : World) → Sched w)
         → (s : S) → ⊤G {s} ⊢ M s
    löbᵀ st sch s m _ = go (sch (s , m))
      where
        -- `sch` is forced ONCE and its chain is shared with its
        -- membership proof; that binding is the point of the `where`.
        go : Sched (s , m) → M s m
        go (is , ch , p) = solveAt (stepᵀ st) ch (s , m) p

    -- ... AND IT IS THE SAME ANSWER.  One appeal to `DP.solveAt≡`, and
    -- with it every pinned test becomes a check on the WIRING.
    löbᵀ≡ : (st : (s : S) → ▷ᴾ M {s} ⊢ M s)
            (sch : (w : World) → Sched w) (s : S) (m : Fib .carrier s)
          → löbᵀ st sch s m tt ≡ löb (stepᵀ st) (s , m)
    löbᵀ≡ st sch s m =
      solveAt≡ (stepᵀ st) (sch (s , m) .snd .fst) (s , m) (sch (s , m) .snd .snd)

-- ==================================================================
-- THE KERNEL: a guarded description has a DECIDABLE fixed point.
--
-- CYK is not about strings, or spans, or context-free grammars.  It is
-- this theorem, and both `Instances.Strings.CYK.Decide` and
-- `Instances.Spans.CYK.Decide` -- which were the same 41 lines twice --
-- are instances of it.
--
-- The proof is structural recursion on the DESCRIPTION, and it has the
-- same two-level shape as the guardedness proof it consumes, for the
-- same reason:
--
--     decF≤   source `Chart⁺`      mirrors `Guarded≤`
--     decF<   source `▷ᴬ Chart`    mirrors `Guarded`
--
-- `Var` is decidable at the ≤ level and NOT at the < level -- which is
-- exactly the statement that `Var` at the top of a description is left
-- recursion, correctly rejected.  `⊗e` is the one former that moves
-- between the levels, exactly as it is the one former that contributes
-- strictness.
--
-- `Chart⁺ = Chart & ▷ᴬ Chart` -- "the answers here, and everywhere
-- smaller".  Both components are needed: `Var` reads the first,
-- a nested `⊗e` reads the second.  `⁺-later` below shows the pair is
-- closed under the later, which is what lets the recursion nest.
-- ==================================================================

module DecDesc {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
               (GS : GradedFib σ ℓX ℓP) (ℓA : Level)
               (X : Type ℓV) (xs : X → S) where

  open DecGuard GS public
  open Guard GS ℓA X xs public
    using (Functor; ⌜_⌝; Var; ⊕e; &e; ⊗e; μ; ⟦_⟧c; Guarded; Guarded≤;
           roll; unroll; toC; fromC; Sh; Pos; nx; Ix)
  open DecList (GS .fib .carrier) using (dec-⊕ᴰ; dec-&ᴰL)

  -- NOT YET: the chart, generically.  See the note in the header of
  -- this block -- `Ix` is `Σ[ x ∈ X ] carrier (xs x)`, so turning an
  -- `Ix`-family into a GRAMMAR at sort `s` means restricting to the `x`
  -- with `xs x ≡ s`, and that equation has to be transported at every
  -- `Var`.  Single-sorted instances dodge it (every `x` qualifies); the
  -- many-sorted statement needs `Ind` to index `X` by the sort.
