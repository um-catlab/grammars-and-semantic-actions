{- THE MISSING RULE: consuming a `▷` INSIDE a tensor. -}
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
open import TheoryGrammar.DP.Seq
open import TheoryGrammar.Decidable.Enumerated
open import TheoryGrammar.Decidable.Listable

private variable ℓS ℓ ℓ' ℓX ℓP ℓA ℓR ℓM ℓV ℓY : Level

module DecGuard {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
                (GS : GradedFib σ ℓX ℓP) where

  private
    Fib : Fibered σ ℓX ℓP
    Fib = GS .fib

  open DecEnum Fib public

  -- the DEPENDENCY order of the theory (`DP.DPGraded`): `v ≺ᵖ w` is "v is
  -- a proper slot of some splitting of w", read off `Split` / `parts` /
  -- `Proper`.
  open DPGraded GS public

  -- the level `_≺ᵖ_` lives at, named once
  ℓ≺ᵖ : Level
  ℓ≺ᵖ = ℓ-max ℓS (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓX ℓP)))

  -- (1)  THE LATER, AT THE LEVEL OF GRAMMARS.

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

  -- DOWNWARD CLOSURE. `▷ᴬ M` at `m` yields `▷ᴬ M` at every strictly
  -- smaller world -- transitivity of `<`, nothing more.
  ▷ᴬ-dn : (M : SortFam ℓM) {s : S} (m : Fib .carrier s) → ▷ᴬ M m
        → (s' : S) (m' : Fib .carrier s')
        → GS .deg s' m' < GS .deg s m → ▷ᴬ M {s'} m'
  ▷ᴬ-dn M m later s' m' q s'' m'' q' = later s'' m'' (<-trans q' q)

  -- LÖB, at the level of grammars. The step is a TERM `▷ᴬ M ⊢ M s`, never
  -- an Agda function on an index -- which is the discipline
  -- `Grammar/Parser/RecursiveDescent.fixP` sets and which the `Ix`-level
  -- `Guard.löb` cannot enforce, since `Ix` is not a sort.

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

  -- (1b) THE LATER OVER THE *DEPENDENCY* ORDER -- and it is the one a
  -- chart can be built from.

  ▷ᴾ : SortFam ℓM → {s : S} → TheoryTy (ℓ-max ℓ≺ᵖ ℓM) s
  ▷ᴾ M {s} m = (w : World) → w ≺ᵖ (s , m) → M (w .fst) (w .snd)

  -- ... and it is functorial, exactly as `▷ᴬ` is.
  ▷ᴾ-map : {M : SortFam ℓM} {N : SortFam ℓV} {s : S}
         → ((s' : S) → M s' ⊢ N s') → ▷ᴾ M {s} ⊢ ▷ᴾ N {s}
  ▷ᴾ-map f m r w q = f (w .fst) (w .snd) (r w q)

  -- `▷ᴬ` is stronger, so a step written against `▷ᴾ` may be run by
  -- either.  (`≺ᵖ-deg` is the whole proof.)
  ▷ᴬ→▷ᴾ : (M : SortFam ℓM) {s : S} → ▷ᴬ M {s} ⊢ ▷ᴾ M {s}
  ▷ᴬ→▷ᴾ M m later w q = later (w .fst) (w .snd) (≺ᵖ-deg q)

  -- (2) THE RESOURCE HYPOTHESIS, DERIVED FROM TERMS.

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

  -- (3)  THE RULE.

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
        -- slot decider `d` is applied to it.
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

    -- THE SAME RULE, OVER `_≺ᵖ_`. Line for line `dec-⊗▷`, except that the
    -- licence to recurse at a slot is the `slot` CONSTRUCTOR -- "this is a
    -- proper slot of this splitting of this world" -- rather than the
    -- inequality `deg<` it implies.
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

  -- (4) LÖB, TABULATED. `löbᵍ` solves the recurrence by re-descending: its
  -- `later` is a FUNCTION, so every consultation recomputes and nothing is
  -- shared.

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

    -- THE SAME THING ON THE TREE SPINE -- and this is the one to use.

    SchedQ : World → Type ℓ≺ᵖ
    SchedQ w = Σ[ s ∈ Seq World ] Σ[ _ ∈ ChainQ s εQ ] (w ∈Q s)

    löbᵀQ : ((s : S) → ▷ᴾ M {s} ⊢ M s)
          → ((w : World) → SchedQ w)
          → (s : S) → ⊤G {s} ⊢ M s
    löbᵀQ st sch s m _ = go (sch (s , m))
      where
        go : SchedQ (s , m) → M s m
        go (sq , ch , p) = solveQ (stepᵀ st) ch (s , m) p

    löbᵀQ≡ : (st : (s : S) → ▷ᴾ M {s} ⊢ M s)
             (sch : (w : World) → SchedQ w) (s : S) (m : Fib .carrier s)
           → löbᵀQ st sch s m tt ≡ löb (stepᵀ st) (s , m)
    löbᵀQ≡ st sch s m =
      buildQ-correct (stepᵀ st) (sch (s , m) .snd .fst) tt*
                     (λ _ ()) (s , m) (sch (s , m) .snd .snd)

  -- (5) THE CELL MUST BE DATA -- and this is the generic statement of the
  -- single largest cost fact in the development.

  module TabΠ {ℓY ℓN : Level} (Y : Type ℓY) (N : Y → SortFam ℓN)
              (ys : List Y) (ysOk : (y : Y) → y ∈L ys) where

    -- the chart as written: an inner index that is a function
    ΠChart : SortFam (ℓ-max ℓY ℓN)
    ΠChart s m = (y : Y) → N y s m

    -- ... and the same chart with that index pushed into the data
    DChart : SortFam (ℓ-max ℓY ℓN)
    DChart s m = AllYes' (λ y → N y s m) ys

    fromD : (s : S) → DChart s ⊢ ΠChart s
    fromD s m t y = lookupYes' ys y (ysOk y) t

    toD : (s : S) → ΠChart s ⊢ DChart s
    toD s m f = tabulate' ys f

    -- THE CONJUGATION.  The step is unchanged; only the representative
    -- of the chart it reads and writes moves.
    conj : ((s : S) → ▷ᴾ ΠChart {s} ⊢ ΠChart s)
         → (s : S) → ▷ᴾ DChart {s} ⊢ DChart s
    conj st s = toD s ∘g st s ∘g ▷ᴾ-map fromD

    private module TD = Tab DChart

    open TD public using (SchedQ; Motive)

    -- THE SOLVED CHART, shared in both indices.
    löbᴰ : ((s : S) → ▷ᴾ ΠChart {s} ⊢ ΠChart s)
         → ((w : World) → SchedQ w)
         → (s : S) → ⊤G {s} ⊢ ΠChart s
    löbᴰ st sch s = fromD s ∘g TD.löbᵀQ (conj st) sch s

    -- ... AND IT IS THE SAME ANSWER.

    private module TΠ = Tab ΠChart

    fromToD : (s : S) (m : Fib .carrier s) (f : ΠChart s m)
            → fromD s m (toD s m f) ≡ f
    fromToD s m f = funExt λ y → lookup-tabulate ys f y (ysOk y)

    löbᴰ≡ : (st : (s : S) → ▷ᴾ ΠChart {s} ⊢ ΠChart s)
            (sch : (w : World) → SchedQ w) (s : S) (m : Fib .carrier s)
          → löbᴰ st sch s m tt ≡ TΠ.löb (TΠ.stepᵀ st) (s , m)
    löbᴰ≡ st sch s m =
        cong (fromD s m) (TD.löbᵀQ≡ (conj st) sch s m)
      ∙ cong (fromD s m)
             (TΠ.löb-retract (TΠ.stepᵀ st)
                             (λ w → toD (w .fst) (w .snd))
                             (λ w → fromD (w .fst) (w .snd))
                             (λ w → fromToD (w .fst) (w .snd)) (s , m))
      ∙ fromToD s m _

-- THE KERNEL: a guarded description has a DECIDABLE fixed point.

module DecDesc {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
               (GS : GradedFib σ ℓX ℓP) (ℓA : Level)
               (X : Type ℓV) (xs : X → S) where

  open DecGuard GS public
  open Guard GS ℓA X xs public
    using (Functor; ⌜_⌝; Var; ⊕e; &e; ⊗e; μ; ⟦_⟧c; Guarded; Guarded≤;
           roll; unroll; toC; fromC; Sh; Pos; nx; Ix)
  open DecList (GS .fib .carrier) using (dec-⊕ᴰ; dec-&ᴰL)

  -- NOT YET: the chart, generically. See the note in the header of this
  -- block -- `Ix` is `Σ[ x ∈ X ] carrier (xs x)`, so turning an
  -- `Ix`-family into a GRAMMAR at sort `s` means restricting to the `x`
  -- with `xs x ≡ s`, and that equation has to be transported at every
  -- `Var`.
