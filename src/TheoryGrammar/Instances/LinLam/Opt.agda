{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  PHASE 3.  OPTIMISATION PASSES OVER THE LINEAR CALCULUS -- and the
  theorems that make them interesting.

  `Syntax.agda` ends with the claim this file is here to cash:

      Pass = TmG ⊢ TmG

  and `_⊢_` preserves the index, so a pass CANNOT silently drop or
  duplicate a variable.  Three things need saying about that claim
  before any pass is written, because they are what the file is
  organised around.

  ------------------------------------------------------------------
  1.  WHY THIS IS DIFFERENT FROM `Instances/Lambda/Passes`.
  ------------------------------------------------------------------

  Compare the untyped development's `Passes/Framework.agda`.  There a
  pass has type

      Scoped Γ ⊢ Out Γ,        Out Γ = ⊕ᴰ Raw (λ t' → Scoped Γ t')

  and its own header says the decisive thing: `Out Γ` is CONSTANT in
  the index, so "the index pins nothing; what is free is the
  recursion."  A pass there is a map into an existential over the
  carrier, i.e. it has already forgotten which term it started from.
  That is why `Passes/Dead.agda` can discard the argument of a redex
  invisibly: the existential form is affine by construction.

  Here the domain and the codomain are the SAME grammar at the SAME
  index.  A pass is an endomorphism of `TmG` over `Usage`, so the
  usage -- which variables this subterm is responsible for -- survives
  the pass definitionally.  Nothing had to be arranged for that; it is
  the difference between rewriting terms of a family and rewriting
  terms of a family INDEXED BY THE RESOURCE.

  What that actually buys, concretely, is listed at the end of the
  file under "WHAT THE INDEX BOUGHT".  It is less than one might hope
  and more than nothing, and both halves are worth stating.

  ------------------------------------------------------------------
  2.  β IS SAFE HERE, AND THE REASON IS THE TYPE OF SUBSTITUTION.
  ------------------------------------------------------------------

  `Instances/Lambda/Passes/Inline.agda` proves a negative result:
  substitution in the untyped calculus is a CARRIER MAP `Raw → Raw`,
  and `¬subSplitPres` refutes `SplitPresAt` at `varOp` -- substituting
  into a variable produces something that is not a variable, so the
  multiplicative structure does not transport.  Inlining is unsound as
  a structural operation, and the restricted positive case
  (`Passes/Rename`) is exactly renaming.

  Linear substitution is not a carrier map at all.  It is

      substT : (BodyOf TmG ⊛ TmG) ⊢ TmG

  where `BodyOf A u = A (true ∷ u)` is `A` reindexed along weakening
  and `⊛ = ⊗ˢ appop` is the splitting.  Read the type: the body owns
  `u₁`, the argument owns `u₂`, `u₁ ⊎ u₂ = u`, and the result owns
  `u`.  That IS the substitution lemma

      Γ₁ , x:A ⊢ b : B     Γ₂ ⊢ a : A
      -------------------------------  Γ₁ # Γ₂
           Γ₁ ⊎ Γ₂ ⊢ b[a/x] : B

  with no side condition to discharge, because `⊛` is the side
  condition.  And it is why β cannot duplicate: duplicating `a` would
  need `u₂` on both sides of the splitting, and `Use⊎` has no
  constructor taking `true` twice (`noDupUse`, in `Context.agda`).
  The general λ-calculus fails precisely because `Raw` has no index to
  be split.

  So the contrast between the two files is not "one pass works and one
  does not".  It is that the SAME operation has two different types,
  and the linear one is a term of the calculus while the untyped one
  is a map of carriers that is asked, and fails, to preserve the
  splittings.

  §3.4 pushes this to its proper form.  Giving the usage promodel its
  FOCUSED splittings (`Focus linFib appop true`, the zipper view) makes
  the residual `⊸ᶠ` a plain Π, and then

      substUP : Iso ((BodyOf TmG ⊛ TmG) ⊢ B) (BodyOf TmG ⊢ ⊸ᶠ Redex B)

  says substitution IS the internal hom and β IS its evaluation map --
  `substIsApp` holds by `refl`.  One direction of the iso is
  definitional; the other costs exactly one `boolΠ`-η, which is the
  documented "arities have no η" trap appearing in the one place it
  genuinely bites.

  ------------------------------------------------------------------
  3.  DEAD-CODE ELIMINATION IS VACUOUS -- as a theorem, not an absence.
  ------------------------------------------------------------------

  This is the most interesting item, and it lands.

  The untyped `Passes/Dead.agda` rewrites `(λx. b) a ↦ b` when `x` is
  unused in `b`.  In this calculus the premise cannot be stated: the
  body of a binder has type `Tm (true ∷ u)`, and the `true` says the
  bound variable is live.  There is no `Tm (false ∷ u)` masquerading
  as a body.

  That is not yet a theorem -- "you cannot write it down" is a remark
  about the syntax.  The theorem is quantitative.  Fold the term with
  the motive

      Budget u = Σ[ oc ∈ ℕ ] Σ[ lm ∈ ℕ ] (oc ≡ live u + lm)

  ("occurrences = live variables + binders").  This is the Quicksort
  idiom: the motive of the fold IS the statement being proved, so the
  algebra produces the invariant as it computes the counts and there
  is nothing to re-check afterwards.  The three branches are the three
  typing rules and each contributes one line of arithmetic --
  `soloLive` for a variable, `liveSplit` (already a primitive of
  `Context.agda`) for an application, `+-suc` for a binder.

  With the budget in hand, "the binder is dead" says: there is a body
  `b : Tm (true ∷ u)` and a replacement `c : Tm u` -- the term DCE
  would put in its place -- with the same occurrence profile.  Then

      occ b = live (true ∷ u) + lm b = suc (live u + lm b)
      occ c = live u + lm c          = live u + lm b

  and `suc n ≡ n` is absurd.  So

      deadBinder : DeadBinder ⊢ ⊥G

  the dead-binder grammar is the EMPTY grammar, and a dead-code
  eliminator's rewriting branch is `⊥-E`.  Any two of them agree; the
  pass is the identity.  Note the hypothesis is only that the profiles
  agree, which is far weaker than syntactic equality -- so the theorem
  is correspondingly stronger.

  ------------------------------------------------------------------
  4.  HOW A PASS IS BUILT.
  ------------------------------------------------------------------

  `Tm` is a data type, so somebody has to recurse on it.  That is done
  ONCE, in `foldTm`, and every pass below is an algebra

      StepG A = SoloG ⊕ ((A ⊛ A) ⊕ BodyOf A)
      foldTm  : (A : Ctx) → StepG A ⊢ A → TmG ⊢ A

  whose three summands are the three rules of `Syntax.agda`.  In
  particular

      roll = ⊕-E varT (⊕-E appT lamT) : StepG TmG ⊢ TmG

  is the algebra of the typing rules themselves, and `foldRoll` proves
  `foldTm TmG roll ≡ idPass` -- the untyped `Framework.agda` asserts
  the corresponding fact about `idAlg` without proving it.  A pass is
  then literally `roll` with one branch replaced.

  The recursion CANNOT come from `hyloC`.  `linGrading` grades by
  `live`, and going under a binder makes `live` go UP, so the
  well-founded recursion the graded framework supplies descends on the
  wrong thing.  Structural recursion on `Tm` is a genuine primitive
  here, and it is marked as one.

  ------------------------------------------------------------------
  5.  THE PRIMITIVES, AND WHY EACH IS ONE.
  ------------------------------------------------------------------

  Everything pointful is in §1-§3, and it comes in TWO LAYERS that this
  header used to run together.  Counting the `PRIMITIVE` labels:

    13 in §1-§2, at the INDEX.  `useEmptyL`, `useEmptyR`, `soloLive`,
       `useAssoc`, `useExch`, `markF-Empty→`, `markT-¬Empty`,
       `insSplit`, `freshSplit`, and the three `⊛` structural maps.
       These are metalanguage functions on `Usage`/`Use⊎`/`Mark` -- they
       do NOT have `⊢` types, because the resource algebra is not a
       grammar.  That is the substrate being built, phase 1 proper.

    10 in §3, at the TERM, every one with a `⊢` type.

  Ten is more than "a handful" and the number should be read, not
  glossed: this instance pays for linearity with a thicker primitive
  layer than any other in the tree.  The seven that carry content:

    `insT` / `delT`     a variable that is not used can be inserted
                        into, or deleted from, the scope.  Both are
                        `⊢`-maps at a reindexed motive, exactly as
                        `lamT` is.  `delT` is STRENGTHENING, and it is
                        what η-contraction has to pay for.

    `freshSplit`        THE linearity lemma: in an application under a
                        binder, the fresh variable is used in exactly
                        ONE of the two premises.  In a cartesian
                        calculus this map does not exist -- the
                        variable may appear in both, or in neither.

    `soloUnit`          an application whose argument is exactly the
                        fresh variable is its own function part.  This
                        is the unit law of `⊛` at an `Empty` slot, and
                        it is where η actually happens.

    `substT`            substitution, discussed above.

    `⊛-distR`/`⊛-distL` `⊗ˢ` is a Σ, so it distributes over `⊕`.
                        Structural; needed because branching on a
                        subterm has to happen INSIDE a tensor slot.

  `boolΠ` is used for every arity-indexed family, never an extended
  lambda -- arities have no η and two extended lambdas written in
  different places are nominally distinct, which has bitten this
  codebase before.
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.LinLam.Opt where

open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order using (_<_; ¬-<-zero)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib

open import TheoryGrammar.Instances.LinLam.Syntax public

private variable ℓA ℓB : Level

-- ==================================================================
-- §0  NOTATION.
--
-- `BodyOf A` is `A` pulled back along the weakening map `u ↦ true ∷ u`
-- -- the Cartesian lift `Syntax.agda` already uses to type `lamT`.
-- Giving it a name makes the passes readable and makes `under` (the
-- functorial action of that pullback) statable.
-- ==================================================================

BodyOf : TheoryTy ℓA tt → TheoryTy ℓA tt
BodyOf A u = A (true ∷ u)

SoloG : Ctx
SoloG u = Solo u

-- PRIMITIVE (phase 1): reindexing is functorial.  This is
-- `CarrierMap.pullTerm` along `u ↦ true ∷ u`, written out because the
-- carrier map in question is not a model homomorphism (it does not
-- preserve `Use⊎`; it is the weakening map of the fibration).
under : {A : TheoryTy ℓA tt} {B : TheoryTy ℓB tt}
      → A ⊢ B → BodyOf A ⊢ BodyOf B
under f u = f (true ∷ u)

-- ==================================================================
-- §1  THE INDEX ALGEBRA.
--
-- Usages form a partial commutative monoid; the passes need its
-- associativity, its unit laws, and one fact about scope extension.
-- All of it is phase 1 and none of it mentions `Tm`.
-- ==================================================================

-- ------------------------------------------------------------------
-- 1.1  Unit laws.  An `Empty` slot contributes nothing, so the other
-- slot IS the whole.  Stated in `Eq`-world so that consumers match
-- `Eq.refl` rather than transporting -- a `subst` at a family over a
-- variable usage would not reduce, and every `refl` test downstream
-- would break far from here.
-- ------------------------------------------------------------------

-- PRIMITIVE (phase 1)
useEmptyL : ∀ {u₁ u₂ u} → Use⊎ u₁ u₂ u → Empty u₁ → u₂ Eq.≡ u
useEmptyL unil       e = Eq.refl
useEmptyL (uleft  s) e = E.rec e
useEmptyL (uright s) e = Eq.ap (true  ∷_) (useEmptyL s e)
useEmptyL (uskip  s) e = Eq.ap (false ∷_) (useEmptyL s e)

-- PRIMITIVE (phase 1)
useEmptyR : ∀ {u₁ u₂ u} → Use⊎ u₁ u₂ u → Empty u₂ → u₁ Eq.≡ u
useEmptyR unil       e = Eq.refl
useEmptyR (uleft  s) e = Eq.ap (true  ∷_) (useEmptyR s e)
useEmptyR (uright s) e = E.rec e
useEmptyR (uskip  s) e = Eq.ap (false ∷_) (useEmptyR s e)

-- PRIMITIVE (phase 1): a `Solo` usage has exactly one live variable.
soloLive : (u : Usage) → Solo u → live u ≡ 1
soloLive (true  ∷ u) e = cong suc (emptyLive u e)
  where
  emptyLive : (v : Usage) → Empty v → live v ≡ 0
  emptyLive []          _ = refl
  emptyLive (false ∷ v) e = emptyLive v e
soloLive (false ∷ u) e = soloLive u e

-- ------------------------------------------------------------------
-- 1.2  Associativity, in the two shapes the passes actually need.
-- Both are proved by simultaneous induction; the clauses that are
-- ABSENT are the ones where the two derivations disagree about
-- whether a variable is live, and Agda discharges them by index
-- unification.
-- ------------------------------------------------------------------

-- PRIMITIVE (phase 1):  (p ⊎ q) ⊎ r  ↦  p ⊎ (q ⊎ r)
useAssoc : ∀ {p q pq r s} → Use⊎ p q pq → Use⊎ pq r s
         → Σ[ t ∈ Usage ] (Use⊎ q r t × Use⊎ p t s)
useAssoc unil        unil       = [] , unil , unil
useAssoc (uleft s₁)  (uleft s₂) =
  let (t , a , b) = useAssoc s₁ s₂ in (false ∷ t) , uskip  a , uleft  b
useAssoc (uright s₁) (uleft s₂) =
  let (t , a , b) = useAssoc s₁ s₂ in (true  ∷ t) , uleft  a , uright b
useAssoc (uskip s₁)  (uright s₂) =
  let (t , a , b) = useAssoc s₁ s₂ in (true  ∷ t) , uright a , uright b
useAssoc (uskip s₁)  (uskip s₂) =
  let (t , a , b) = useAssoc s₁ s₂ in (false ∷ t) , uskip  a , uskip  b

-- PRIMITIVE (phase 1):  (p ⊎ q) ⊎ r  ↦  (p ⊎ r) ⊎ q   (the exchange)
useExch : ∀ {p q pq r s} → Use⊎ p q pq → Use⊎ pq r s
        → Σ[ t ∈ Usage ] (Use⊎ p r t × Use⊎ t q s)
useExch unil        unil       = [] , unil , unil
useExch (uleft s₁)  (uleft s₂) =
  let (t , a , b) = useExch s₁ s₂ in (true  ∷ t) , uleft  a , uleft  b
useExch (uright s₁) (uleft s₂) =
  let (t , a , b) = useExch s₁ s₂ in (false ∷ t) , uskip  a , uright b
useExch (uskip s₁)  (uright s₂) =
  let (t , a , b) = useExch s₁ s₂ in (true  ∷ t) , uright a , uleft  b
useExch (uskip s₁)  (uskip s₂) =
  let (t , a , b) = useExch s₁ s₂ in (false ∷ t) , uskip  a , uskip  b

-- ------------------------------------------------------------------
-- 1.3  MARKERS.  `Mark b n u v` says `v` is `u` with the bit `b`
-- inserted at position `n`.  The position is carried because the two
-- markers have to agree on it: when a splitting is pushed through an
-- insertion, the marked variable lands in one branch and the OTHER
-- branch has a `false` at the same place.  Without the `n` that
-- coincidence cannot be stated.
--
-- `Mark false` is scope extension by an unused variable (shifting);
-- `Mark true` is the position being substituted for.
-- ------------------------------------------------------------------

data Mark (b : Bool) : ℕ → Usage → Usage → Type₀ where
  mhere  : ∀ {u} → Mark b 0 u (b ∷ u)
  mthere : ∀ {n u v} (c : Bool) → Mark b n u v → Mark b (suc n) (c ∷ u) (c ∷ v)

-- PRIMITIVE (phase 1): an inserted `false` is invisible to `Empty`
markF-Empty→ : ∀ {n u v} → Mark false n u v → Empty u → Empty v
markF-Empty→ mhere            e = e
markF-Empty→ (mthere true  m) e = e
markF-Empty→ (mthere false m) e = markF-Empty→ m e

markF-Empty← : ∀ {n u v} → Mark false n u v → Empty v → Empty u
markF-Empty← mhere            e = e
markF-Empty← (mthere true  m) e = e
markF-Empty← (mthere false m) e = markF-Empty← m e

-- ... and to `Solo`
markF-Solo→ : ∀ {n u v} → Mark false n u v → Solo u → Solo v
markF-Solo→ mhere            s = s
markF-Solo→ (mthere true  m) s = markF-Empty→ m s
markF-Solo→ (mthere false m) s = markF-Solo→ m s

markF-Solo← : ∀ {n u v} → Mark false n u v → Solo v → Solo u
markF-Solo← mhere            s = s
markF-Solo← (mthere true  m) s = markF-Empty← m s
markF-Solo← (mthere false m) s = markF-Solo← m s

-- PRIMITIVE (phase 1): an inserted `true` is a live variable, so the
-- extended usage is never empty.  This is the clause that kills the
-- "the substituted variable is some OTHER variable" case below.
markT-¬Empty : ∀ {n u v} → Mark true n u v → Empty v → ⊥
markT-¬Empty mhere            e = e
markT-¬Empty (mthere true  m) e = e
markT-¬Empty (mthere false m) e = markT-¬Empty m e

markT-Solo : ∀ {n u v} → Mark true n u v → Solo v → Empty u
markT-Solo mhere            s = s
markT-Solo (mthere true  m) s = E.rec (markT-¬Empty m s)
markT-Solo (mthere false m) s = markT-Solo m s

-- PRIMITIVE (phase 1): a splitting survives inserting an unused
-- variable, in both directions.
insSplit : ∀ {n u v u₁ u₂} → Mark false n u v → Use⊎ u₁ u₂ u
         → Σ[ v₁ ∈ Usage ] Σ[ v₂ ∈ Usage ]
             (Mark false n u₁ v₁ × Mark false n u₂ v₂ × Use⊎ v₁ v₂ v)
insSplit mhere s = _ , _ , mhere , mhere , uskip s
insSplit (mthere true m) (uleft s) =
  let (v₁ , v₂ , m₁ , m₂ , s') = insSplit m s
  in _ , _ , mthere true m₁ , mthere false m₂ , uleft s'
insSplit (mthere true m) (uright s) =
  let (v₁ , v₂ , m₁ , m₂ , s') = insSplit m s
  in _ , _ , mthere false m₁ , mthere true m₂ , uright s'
insSplit (mthere false m) (uskip s) =
  let (v₁ , v₂ , m₁ , m₂ , s') = insSplit m s
  in _ , _ , mthere false m₁ , mthere false m₂ , uskip s'

delSplit : ∀ {n u v v₁ v₂} → Mark false n u v → Use⊎ v₁ v₂ v
         → Σ[ u₁ ∈ Usage ] Σ[ u₂ ∈ Usage ]
             (Mark false n u₁ v₁ × Mark false n u₂ v₂ × Use⊎ u₁ u₂ u)
delSplit mhere (uskip s) = _ , _ , mhere , mhere , s
delSplit (mthere true m) (uleft s) =
  let (u₁ , u₂ , m₁ , m₂ , s') = delSplit m s
  in _ , _ , mthere true m₁ , mthere false m₂ , uleft s'
delSplit (mthere true m) (uright s) =
  let (u₁ , u₂ , m₁ , m₂ , s') = delSplit m s
  in _ , _ , mthere false m₁ , mthere true m₂ , uright s'
delSplit (mthere false m) (uskip s) =
  let (u₁ , u₂ , m₁ , m₂ , s') = delSplit m s
  in _ , _ , mthere false m₁ , mthere false m₂ , uskip s'

-- PRIMITIVE (phase 1): THE LINEARITY LEMMA AT THE INDEX LEVEL.  A
-- splitting of an extended usage sends the marked variable to exactly
-- one branch, and the other branch has an unused slot in its place.
-- The `⊎` is exclusive because `Use⊎` has no (true,true) constructor.
atSplit : ∀ {n u v v₁ v₂} → Mark true n u v → Use⊎ v₁ v₂ v
        → (Σ[ p ∈ Usage ] Σ[ q ∈ Usage ]
             (Mark true n p v₁ × Mark false n q v₂ × Use⊎ p q u))
        ⊎ (Σ[ p ∈ Usage ] Σ[ q ∈ Usage ]
             (Mark false n p v₁ × Mark true n q v₂ × Use⊎ p q u))
atSplit mhere (uleft s)  = inl (_ , _ , mhere , mhere , s)
atSplit mhere (uright s) = inr (_ , _ , mhere , mhere , s)
atSplit (mthere true m) (uleft s) with atSplit m s
... | inl (p , q , m₁ , m₂ , s') =
        inl (_ , _ , mthere true m₁ , mthere false m₂ , uleft s')
... | inr (p , q , m₁ , m₂ , s') =
        inr (_ , _ , mthere true m₁ , mthere false m₂ , uleft s')
atSplit (mthere true m) (uright s) with atSplit m s
... | inl (p , q , m₁ , m₂ , s') =
        inl (_ , _ , mthere false m₁ , mthere true m₂ , uright s')
... | inr (p , q , m₁ , m₂ , s') =
        inr (_ , _ , mthere false m₁ , mthere true m₂ , uright s')
atSplit (mthere false m) (uskip s) with atSplit m s
... | inl (p , q , m₁ , m₂ , s') =
        inl (_ , _ , mthere false m₁ , mthere false m₂ , uskip s')
... | inr (p , q , m₁ , m₂ , s') =
        inr (_ , _ , mthere false m₁ , mthere false m₂ , uskip s')

-- ==================================================================
-- §2  THE MULTIPLICATIVE INTERFACE, once.
--
-- `⊛` is `⊗ˢ appop (boolΠ A B)`, so its intro and elim are `⊗ˢ-I` and
-- `⊗ˢ-E` with the arity family spelled by `boolΠ`.  Writing that here
-- ONCE is the point: every extended lambda over `Bool` in this file
-- would otherwise be a fresh nominal function that fails to reduce
-- against the ones in `Syntax.agda`.
-- ==================================================================

-- PRIMITIVE (phase 1): intro for `⊛`
⊛-mk : (A B : Ctx) (u u₁ u₂ : Usage) → Use⊎ u₁ u₂ u → A u₁ → B u₂ → (A ⊛ B) u
⊛-mk A B u u₁ u₂ s x y =
  ⊗ˢ-I appop {A = boolΠ A B} u (u₁ , u₂ , s)
    (boolΠ {M = λ a → boolΠ {M = λ _ → Ctx} A B a
                        (linFib .parts appop u (u₁ , u₂ , s) a)} x y)

-- PRIMITIVE (phase 1): elim for `⊛` -- `⊗ˢ-E`'s `MultiHomˢ` with the
-- two slots read off by `boolΠ`'s computation rules.  This is `appE`
-- from `Syntax.agda`, generalised in the two grammars.
⊛-E' : (A B : Ctx) {C : Ctx}
     → ((u u₁ u₂ : Usage) → Use⊎ u₁ u₂ u → A u₁ → B u₂ → C u)
     → (A ⊛ B) ⊢ C
⊛-E' A B {C} f = ⊗ˢ-E appop {A = boolΠ A B} {B = C}
  (λ u sp k → f u (sp .fst) (sp .snd .fst) (sp .snd .snd) (k true) (k false))

-- the functorial action, slotwise -- `⊗ˢ-map` at `boolΠ`
⊛-map : {A A' B B' : Ctx} → A ⊢ A' → B ⊢ B' → (A ⊛ B) ⊢ (A' ⊛ B')
⊛-map {A} {A'} {B} {B'} f g =
  ⊗ˢ-map appop {A = boolΠ A B} {B = boolΠ A' B'}
    (boolΠ {M = λ a → boolΠ {M = λ _ → Ctx} A B a
                    ⊢ boolΠ {M = λ _ → Ctx} A' B' a} f g)

-- PRIMITIVE (phase 1): `⊗ˢ` is a Σ, so it distributes over `⊕` in
-- either slot.  Needed because a pass has to BRANCH on a subterm, and
-- the subterm sits inside a tensor slot.
⊛-distR : (A B C : Ctx) → (A ⊛ (B ⊕ C)) ⊢ ((A ⊛ B) ⊕ (A ⊛ C))
⊛-distR A B C = ⊛-E' A (B ⊕ C) go
  where
  go : (u u₁ u₂ : Usage) → Use⊎ u₁ u₂ u → A u₁ → (B ⊕ C) u₂
     → ((A ⊛ B) ⊕ (A ⊛ C)) u
  go u u₁ u₂ s x (inl y) = inl (⊛-mk A B u u₁ u₂ s x y)
  go u u₁ u₂ s x (inr z) = inr (⊛-mk A C u u₁ u₂ s x z)

⊛-distL : (A B C : Ctx) → ((A ⊕ B) ⊛ C) ⊢ ((A ⊛ C) ⊕ (B ⊛ C))
⊛-distL A B C = ⊛-E' (A ⊕ B) C go
  where
  go : (u u₁ u₂ : Usage) → Use⊎ u₁ u₂ u → (A ⊕ B) u₁ → C u₂
     → ((A ⊛ C) ⊕ (B ⊛ C)) u
  go u u₁ u₂ s (inl x) z = inl (⊛-mk A C u u₁ u₂ s x z)
  go u u₁ u₂ s (inr y) z = inr (⊛-mk B C u u₁ u₂ s y z)

-- ==================================================================
-- §3  TERM PRIMITIVES.
--
-- Four of them, and the recursor.  Every pass below is built from
-- these plus `_∘g_`, `⊕-E`, `⊕-I₁/₂`, `⊛-map`, `⊛-dist*` and `under`.
-- ==================================================================

-- transport along an `Eq` equation of usages; reduces on `Eq.refl`,
-- which is why §1.1 produces `Eq.≡` and not a Path
coeTm : ∀ {u v} → u Eq.≡ v → Tm u → Tm v
coeTm Eq.refl t = t

-- PRIMITIVE (phase 1): SHIFTING -- an unused variable may be inserted
-- anywhere in the scope.  `⊢`-typed at `n = 0` as `TmG ⊢ BodyOf' TmG`
-- below; the general `n` is needed only to go under binders.
insT : ∀ {n u v} → Mark false n u v → Tm u → Tm v
insT m (tvar s)     = tvar (markF-Solo→ m s)
insT m (tapp s a b) =
  let (v₁ , v₂ , m₁ , m₂ , s') = insSplit m s
  in tapp s' (insT m₁ a) (insT m₂ b)
insT m (tlam b)     = tlam (insT (mthere true m) b)

-- PRIMITIVE (phase 1): STRENGTHENING -- an unused variable may be
-- removed.  This is what η-contraction pays for; in the untyped
-- development the same obligation is `scoped?` in `Passes/Eta.agda`,
-- a DECISION that may fail.  Here it cannot fail, because the usage
-- already says the variable is unused.
delT : ∀ {n u v} → Mark false n u v → Tm v → Tm u
delT m (tvar s)     = tvar (markF-Solo← m s)
delT m (tapp s a b) =
  let (u₁ , u₂ , m₁ , m₂ , s') = delSplit m s
  in tapp s' (delT m₁ a) (delT m₂ b)
delT m (tlam b)     = tlam (delT (mthere true m) b)

-- the two of them as terms of the calculus, at a reindexed motive --
-- the same shape as `lamT`
Unused : Ctx
Unused u = Tm (false ∷ u)

shiftT : TmG ⊢ Unused
shiftT u = insT mhere

strengthenT : Unused ⊢ TmG
strengthenT u = delT mhere

-- ------------------------------------------------------------------
-- 3.1  The shape functor and the recursor.
-- ------------------------------------------------------------------

StepG : Ctx → Ctx
StepG A = SoloG ⊕ ((A ⊛ A) ⊕ BodyOf A)

-- the three typing rules of `Syntax.agda`, as one algebra
roll : StepG TmG ⊢ TmG
roll = ⊕-E varT (⊕-E appT lamT)

-- PRIMITIVE (phase 1): ... and their joint inverse.  Downstream, no
-- pass ever matches on `Tm`; it uses `unroll` and `⊕-E`.
unroll : TmG ⊢ StepG TmG
unroll u (tvar s)               = inl s
unroll u (tapp {u₁} {u₂} s a b) = inr (inl (⊛-mk TmG TmG u u₁ u₂ s a b))
unroll u (tlam b)               = inr (inr b)

-- PRIMITIVE (phase 1): THE recursion.  `linGrading` cannot supply it
-- -- `deg = live` INCREASES under a binder -- so structural recursion
-- on `Tm` is genuinely primitive here, and it happens exactly once.
foldTm : (A : Ctx) → StepG A ⊢ A → TmG ⊢ A
foldTm A α u (tvar s) = α u (inl s)
foldTm A α u (tapp {u₁} {u₂} s a b) =
  α u (inr (inl (⊛-mk A A u u₁ u₂ s (foldTm A α u₁ a) (foldTm A α u₂ b))))
foldTm A α u (tlam b) = α u (inr (inr (foldTm A α (true ∷ u) b)))

-- `roll` and `unroll` are inverse -- definitionally in one direction
rollUnroll : (u : Usage) (t : Tm u) → roll u (unroll u t) ≡ t
rollUnroll u (tvar s)     = refl
rollUnroll u (tapp s a b) = refl
rollUnroll u (tlam b)     = refl

-- THEOREM.  The identity pass is the fold of the typing rules.  This
-- is what licenses "a pass is `roll` with one branch replaced"; the
-- untyped `Passes/Framework.agda` states the corresponding fact about
-- `idAlg` but never proves it.
foldRoll : (u : Usage) (t : Tm u) → foldTm TmG roll u t ≡ t
foldRoll u (tvar s)     = refl
foldRoll u (tapp s a b) = cong₂ (tapp s) (foldRoll _ a) (foldRoll _ b)
foldRoll u (tlam b)     = cong tlam (foldRoll _ b)

foldRollPass : foldTm TmG roll ≡ idPass
foldRollPass i u t = foldRoll u t i

-- ------------------------------------------------------------------
-- 3.2  The two structural facts about a binder.
-- ------------------------------------------------------------------

-- PRIMITIVE (phase 1): THE LINEARITY LEMMA.  Under a binder, an
-- application uses the fresh variable in EXACTLY ONE premise; the
-- other premise does not mention it, so it can be strengthened.
--
-- This map is the whole difference from a cartesian calculus.  There
-- the variable may occur in both branches (so the codomain would have
-- to be a `&`, not a `⊕`) or in neither (so a third summand would be
-- needed).  Here `Use⊎`'s missing (true,true) constructor rules out
-- the first and the body's `true` index rules out the second.
freshSplit : BodyOf (TmG ⊛ TmG)
           ⊢ ((BodyOf TmG ⊛ TmG) ⊕ (TmG ⊛ BodyOf TmG))
freshSplit u ((v₁ , v₂ , s) , k) = go v₁ v₂ s (k true) (k false)
  where
  Cod : Ctx
  Cod = (BodyOf TmG ⊛ TmG) ⊕ (TmG ⊛ BodyOf TmG)

  go : (v₁ v₂ : Usage) → Use⊎ v₁ v₂ (true ∷ u) → Tm v₁ → Tm v₂ → Cod u
  go _ _ (uleft {u = w₁} {v = w₂} s') a b =
    inl (⊛-mk (BodyOf TmG) TmG u w₁ w₂ s' a (delT mhere b))
  go _ _ (uright {u = w₁} {v = w₂} s') a b =
    inr (⊛-mk TmG (BodyOf TmG) u w₁ w₂ s' (delT mhere a) b)

-- ... and its two inverses, so a pass that decides NOT to fire can
-- put the node back.  `insT` undoes the `delT` that `freshSplit` did.
unfreshL : (BodyOf TmG ⊛ TmG) ⊢ BodyOf (TmG ⊛ TmG)
unfreshL = ⊛-E' (BodyOf TmG) TmG λ u w₁ w₂ s a b →
  ⊛-mk TmG TmG (true ∷ u) (true ∷ w₁) (false ∷ w₂) (uleft s) a (insT mhere b)

unfreshR : (TmG ⊛ BodyOf TmG) ⊢ BodyOf (TmG ⊛ TmG)
unfreshR = ⊛-E' TmG (BodyOf TmG) λ u w₁ w₂ s a b →
  ⊛-mk TmG TmG (true ∷ u) (false ∷ w₁) (true ∷ w₂) (uright s) (insT mhere a) b

-- PRIMITIVE (phase 1): THE UNIT LAW, which is where η happens.  An
-- application whose argument is exactly the fresh variable has an
-- `Empty` right slot, so the splitting is trivial and the function
-- part already lives at the whole usage.  No `subst`: `useEmptyR`
-- lands in `Eq`-world and `coeTm` matches `Eq.refl`.
soloUnit : (TmG ⊛ BodyOf SoloG) ⊢ TmG
soloUnit = ⊛-E' TmG (BodyOf SoloG) λ u u₁ u₂ s f so →
  coeTm (useEmptyR s so) f

-- ------------------------------------------------------------------
-- 3.3  Substitution -- the β step, and the file's headline type.
-- ------------------------------------------------------------------

-- PRIMITIVE (phase 1): linear substitution.  Recursion on the body;
-- the three cases are the three ways the marked variable can sit.
--
--   tvar   the body IS the variable, so the argument is the answer;
--          `markT-Solo` says the rest of the body's usage is empty
--          and `useEmptyL` turns that into `u₂ ≡ u`.
--   tapp   `atSplit` says the variable went to exactly one premise;
--          the argument follows it and `useExch`/`useAssoc`
--          reassociate the splitting.  NOTHING is duplicated, and
--          nothing could be: `Use⊎` cannot put `u₂` on both sides.
--   tlam   go under the binder, shifting the argument past it.
subT : ∀ {n u₁ v u₂ u} → Mark true n u₁ v → Use⊎ u₁ u₂ u
     → Tm v → Tm u₂ → Tm u
subT m sp (tvar so) arg = coeTm (useEmptyL sp (markT-Solo m so)) arg
subT m sp (tapp s a b) arg = go (atSplit m s)
  where
  go : _ → Tm _
  go (inl (p , q , mp , mq , sq)) =
    let (t , l , r) = useExch sq sp
    in tapp r (subT mp l a arg) (delT mq b)
  go (inr (p , q , mp , mq , sq)) =
    let (t , l , r) = useAssoc sq sp
    in tapp r (delT mp a) (subT mq l b arg)
subT m sp (tlam b) arg =
  tlam (subT (mthere true m) (uleft sp) b (insT mhere arg))

-- THE HEADLINE.  Substitution is a term of the calculus, at the
-- multiplicative connective.  Its type IS the substitution lemma of
-- the linear λ-calculus, side condition included, and it is the exact
-- statement that `Instances/Lambda/Passes/Inline.agda` REFUTES for
-- the untyped calculus (`¬subSplitPres` at `varOp`).
--
-- PRIMITIVE (phase 1)
substT : (BodyOf TmG ⊛ TmG) ⊢ TmG
substT = ⊛-E' (BodyOf TmG) TmG λ u u₁ u₂ s b a → subT mhere s b a

-- ------------------------------------------------------------------
-- 3.4  ... AND SUBSTITUTION IS THE INTERNAL HOM.
--
-- The type of `substT` is the substitution lemma; the CURRIED type is
-- the better statement, because it says substitution is a term of the
-- residual and β is its evaluation map:
--
--     substCurried : BodyOf TmG ⊢ (TmG ⊸ TmG)
--
-- `Fibered.agda`'s naive `⊸ˢ` carries a `parts o m sp i ≡ x`
-- component, so writing this against it would need a `subst` at a
-- family over a variable usage -- the wrong derivation, and every
-- `refl` test in §6 would stop reducing.  The right answer is the one
-- `Fibered.agda` anticipates: supply the FOCUSED splittings (the
-- zipper view -- a splitting seen from slot `true`, indexed by what
-- sits there) and the residual becomes a plain Π with both laws
-- `refl`.  For usages that view is immediate.
-- ------------------------------------------------------------------

-- PRIMITIVE (phase 1): the zipper view of a usage splitting.
linFocus : Focus linFib appop true
linFocus .SplitAt u₁   = Σ[ u₂ ∈ Usage ] Σ[ u ∈ Usage ] Use⊎ u₁ u₂ u
linFocus .whole  sa    = sa .snd .fst
linFocus .Rest         = Unit
linFocus .restOf _     = false
linFocus .restSlot sa _ = sa .fst

open FocusNotation linFocus

-- the arity family of a β-redex: body on the left, argument on the
-- right.  `⊸ᶠ` reads it only at `restOf tt = false`.
Redex : (a : Bool) → Ctx
Redex = boolΠ (BodyOf TmG) TmG

-- SUBSTITUTION, CURRIED.  No transport, no equation component.
substCurried : BodyOf TmG ⊢ ⊸ᶠ Redex TmG
substCurried u₁ b (u₂ , u , s) k = subT mhere s b (k tt)

-- PRIMITIVE (phase 1): the focused splittings ARE the splittings.
-- This is the bridge `Fibered.agda` leaves to the instance, and it is
-- the only thing standing between `⊸ᶠ` and `⊛`.
focusApp : {B : Ctx} → (BodyOf TmG ⊢ ⊸ᶠ Redex B) → (BodyOf TmG ⊛ TmG) ⊢ B
focusApp g = ⊛-E' (BodyOf TmG) TmG λ u u₁ u₂ s b a → g u₁ b (u₂ , u , s) (λ _ → a)

focusLam : {B : Ctx} → ((BodyOf TmG ⊛ TmG) ⊢ B) → BodyOf TmG ⊢ ⊸ᶠ Redex B
focusLam f u₁ b (u₂ , u , s) k = f u (⊛-mk (BodyOf TmG) TmG u u₁ u₂ s b (k tt))

-- THEOREM.  β IS EVALUATION AT THE RESIDUAL, definitionally.
substIsApp : substT ≡ focusApp substCurried
substIsApp = refl

-- ... and the currying is an isomorphism.  ONE direction is `refl`;
-- the other costs exactly one instance of the documented trap
-- "arities have no η" -- `boolΠ (k true) (k false)` is not `k`, so
-- rebuilding a payload from its two slots is only PROPOSITIONALLY the
-- identity.  That single `cong` is the whole price of the residual
-- here, and naming it is the point of stating the iso at all.
private
  boolΠ-η : ∀ {ℓ} {M : Bool → Type ℓ} (k : (b : Bool) → M b)
          → boolΠ {M = M} (k true) (k false) ≡ k
  boolΠ-η {M = M} k =
    funExt (boolΠ {M = λ b → boolΠ {M = M} (k true) (k false) b ≡ k b} refl refl)

focusRet : {B : Ctx} (g : BodyOf TmG ⊢ ⊸ᶠ Redex B) → focusLam (focusApp g) ≡ g
focusRet g = refl

focusSec : {B : Ctx} (f : (BodyOf TmG ⊛ TmG) ⊢ B) → focusApp (focusLam f) ≡ f
focusSec f = funExt λ u → funExt λ x → cong (λ z → f u (x .fst , z)) (boolΠ-η (x .snd))

substUP : {B : Ctx} → Iso ((BodyOf TmG ⊛ TmG) ⊢ B) (BodyOf TmG ⊢ ⊸ᶠ Redex B)
substUP .Iso.fun = focusLam
substUP .Iso.inv = focusApp
substUP .Iso.sec = focusRet
substUP .Iso.ret = focusSec

-- ==================================================================
-- §4  THE BUDGET, and DEAD-CODE ELIMINATION IS VACUOUS.
--
-- The motive of the fold is the statement being proved.
-- ==================================================================

-- occurrences = live variables + binders
Budget : Ctx
Budget u = Σ[ oc ∈ ℕ ] Σ[ lm ∈ ℕ ] (oc ≡ live u + lm)

private
  shuffle : (a b c d : ℕ) → (a + b) + (c + d) ≡ (a + c) + (b + d)
  shuffle a b c d =
      sym (+-assoc a b (c + d))
    ∙ cong (a +_) (+-assoc b c d)
    ∙ cong (λ z → a + (z + d)) (+-comm b c)
    ∙ cong (a +_) (sym (+-assoc c b d))
    ∙ +-assoc a c (b + d)

-- one variable, no binder: `soloLive` is the whole content
budgetVar : SoloG ⊢ Budget
budgetVar u s = 1 , 0 , sym (+-zero (live u) ∙ soloLive u s)

-- occurrences add, binders add, and the usages add by `liveSplit`
-- (a primitive of `Context.agda`, not a new proof)
budgetApp : (Budget ⊛ Budget) ⊢ Budget
budgetApp = ⊛-E' Budget Budget
  λ u u₁ u₂ s (o₁ , l₁ , e₁) (o₂ , l₂ , e₂) →
    (o₁ + o₂) , (l₁ + l₂) ,
      ( cong₂ _+_ e₁ e₂
      ∙ shuffle (live u₁) l₁ (live u₂) l₂
      ∙ cong (_+ (l₁ + l₂)) (liveSplit s))

-- a binder trades one live variable for one binder: the invariant is
-- literally `+-suc`
budgetLam : BodyOf Budget ⊢ Budget
budgetLam u (o , l , e) = o , suc l , (e ∙ sym (+-suc (live u) l))

budgetAlg : StepG Budget ⊢ Budget
budgetAlg = ⊕-E budgetVar (⊕-E budgetApp budgetLam)

-- THE INTRINSIC INVARIANT, as a term of the calculus.
budget : TmG ⊢ Budget
budget = foldTm Budget budgetAlg

occOf : ∀ {u} → Tm u → ℕ
occOf {u} t = budget u t .fst

lamOf : ∀ {u} → Tm u → ℕ
lamOf {u} t = budget u t .snd .fst

budgetEq : ∀ {u} (t : Tm u) → occOf t ≡ live u + lamOf t
budgetEq {u} t = budget u t .snd .snd

private
  noSucSelf : (n : ℕ) → suc n ≡ n → ⊥
  noSucSelf zero    p = snotz p
  noSucSelf (suc n) p = noSucSelf n (injSuc p)

-- ------------------------------------------------------------------
-- A DEAD BINDER, spelled out.  `b` is the body of a `λ`; `c` is what
-- a dead-code eliminator would return in its place, at the SMALLER
-- usage (the binder gone, the variable never mentioned).  For the
-- rewrite to be dead-code elimination rather than an arbitrary
-- rewrite, `c` must be the same term as `b` -- and we ask only that
-- their occurrence profiles agree, which is much weaker.
-- ------------------------------------------------------------------

DeadBinder : Ctx
DeadBinder u =
  Σ[ b ∈ BodyOf TmG u ] Σ[ c ∈ TmG u ]
    ((occOf b ≡ occOf c) × (lamOf b ≡ lamOf c))

-- THEOREM.  THE DEAD-BINDER GRAMMAR IS EMPTY.  Nothing is dead in a
-- linear calculus, and this is the internal statement of it.
deadBinder : DeadBinder ⊢ ⊥G
deadBinder u (b , c , eo , el) = E.rec (noSucSelf (live u + lamOf b) contradiction)
  where
  -- occ b = live (true ∷ u) + lam b = suc (live u + lam b)
  contradiction : suc (live u + lamOf b) ≡ live u + lamOf b
  contradiction =
      sym (budgetEq b)
    ∙ eo
    ∙ budgetEq c
    ∙ cong (live u +_) (sym el)

-- COROLLARY.  A dead-code eliminator's rewriting branch is `⊥-E`, so
-- there is nothing to choose: any two of them agree, and the pass is
-- the identity.  In the untyped development this branch is
-- `Passes/Dead.agda`'s `dropBinder`, an entire alternative of the
-- algebra guarded by a `scoped?` decision.
stripDead : DeadBinder ⊢ TmG
stripDead = ⊥-E ∘g deadBinder

dceUnique : (f g : DeadBinder ⊢ TmG) → f ≡ g
dceUnique f g = funExt λ u → funExt λ d → E.rec* (deadBinder u d)

-- ... hence the honest dead-code-elimination pass
dcePass : Pass
dcePass = idPass

-- ------------------------------------------------------------------
-- The other half of "no variable is dropped or duplicated": a usage
-- that owns a live variable does not split as itself twice.  This is
-- `noDupUse` propagated along a whole usage, and it is the statement
-- that a pass cannot make two copies of a subterm that uses anything.
-- ------------------------------------------------------------------

noSelfSplit : (u : Usage) → 0 < live u → Use⊎ u u u → ⊥
noSelfSplit []          p _         = ¬-<-zero p
noSelfSplit (true  ∷ u) p ()
noSelfSplit (false ∷ u) p (uskip s) = noSelfSplit u p s

-- ==================================================================
-- §5  THE PASSES.  From here on there is no pointful Agda at all.
-- ==================================================================

-- ------------------------------------------------------------------
-- 5.1  Two views, built from `unroll` alone.
-- ------------------------------------------------------------------

-- "is it a variable?"  The negative branch keeps the term, because
-- `roll` puts back what `unroll` took apart.
isVarView : TmG ⊢ (SoloG ⊕ TmG)
isVarView =
  ⊕-E {A = SoloG} {C = SoloG ⊕ TmG} {B = (TmG ⊛ TmG) ⊕ BodyOf TmG}
      ⊕-I₁ (⊕-I₂ ∘g (⊕-E appT lamT))
  ∘g unroll

-- "is it a λ?"  The positive branch hands back the BODY, which is
-- what β needs.
lamView : TmG ⊢ (BodyOf TmG ⊕ TmG)
lamView =
  ⊕-E {A = SoloG} {C = BodyOf TmG ⊕ TmG} {B = (TmG ⊛ TmG) ⊕ BodyOf TmG}
      (⊕-I₂ ∘g varT)
      (⊕-E (⊕-I₂ ∘g appT) ⊕-I₁)
  ∘g unroll

-- ------------------------------------------------------------------
-- 5.2  β-CONTRACTION.  One alternative of `roll` replaced.
--
--   look at the function part                 ⊛-map lamView idg
--   push the choice out of the tensor         ⊛-distL
--   it was a λ: substitute; else: rebuild     ⊕-E substT appT
--
-- Read the middle line: `⊛-distL` is exactly the step that a
-- cartesian calculus would need `&` for.  And read `substT`'s type
-- again -- the argument goes into the body ONCE, because the tensor
-- gave it its own half of the usage.
-- ------------------------------------------------------------------

betaApp : (TmG ⊛ TmG) ⊢ TmG
betaApp =
  ⊕-E substT appT
  ∘g ⊛-distL (BodyOf TmG) TmG TmG
  ∘g ⊛-map lamView idg

betaAlg : StepG TmG ⊢ TmG
betaAlg = ⊕-E varT (⊕-E betaApp lamT)

-- A single bottom-up sweep, NOT a normaliser: contracting a redex can
-- expose a new one at an ancestor, and this pass does not revisit it.
-- (A normaliser would be `löb`/`hyloC` over a decreasing measure, and
-- `linGrading` is not that measure -- see the header.)
betaPass : Pass
betaPass = foldTm TmG betaAlg

-- ------------------------------------------------------------------
-- 5.3  η-CONTRACTION.  `λx. f x  ↦  f`.
--
-- The `lam` alternative replaced, and every step is one of §3's
-- primitives:
--
--   unroll the body under the binder            under unroll
--   body is the variable                        no η
--   body is an application:
--     fresh variable in the function part       no η   (unfreshL)
--     fresh variable in the argument:           freshSplit
--       argument IS the variable                η !    (soloUnit)
--       argument is something else              no η   (unfreshR)
--   body is a λ                                 no η
--
-- The two obligations `Passes/Eta.agda` has to DECIDE -- "is the
-- argument the bound variable" and "does the function part survive at
-- the smaller scope" -- are here the two halves of `freshSplit`, and
-- neither can fail.  The second one, strengthening, is free because
-- `freshSplit` already produced the function part at the smaller
-- usage; in the untyped setting it is `scoped?`, a decision procedure
-- with a refutation branch.
-- ------------------------------------------------------------------

etaApp : BodyOf (TmG ⊛ TmG) ⊢ TmG
etaApp =
  ⊕-E (lamT ∘g under appT ∘g unfreshL)
      ( ⊕-E soloUnit (lamT ∘g under appT ∘g unfreshR)
        ∘g ⊛-distR TmG (BodyOf SoloG) (BodyOf TmG)
        ∘g ⊛-map idg (under isVarView))
  ∘g freshSplit

etaLam : BodyOf TmG ⊢ TmG
etaLam =
  ⊕-E (lamT ∘g under varT)
      (⊕-E etaApp (lamT ∘g under lamT))
  ∘g under unroll

etaAlg : StepG TmG ⊢ TmG
etaAlg = ⊕-E varT (⊕-E appT etaLam)

etaPass : Pass
etaPass = foldTm TmG etaAlg

-- ------------------------------------------------------------------
-- 5.4  A PIPELINE.  `_then_` is `Syntax.agda`'s; passes are the
-- endomorphisms of `TmG` in the category of the calculus, so
-- composing them is `_∘g_` and nothing has to be checked.
-- ------------------------------------------------------------------

optimise : Pass
optimise = betaPass then etaPass then dcePass

-- ==================================================================
-- §6  IT COMPUTES.
-- ==================================================================

-- `λx. x` at the empty usage, with the binder's variable live
idLin0 : Tm (false ∷ [])
idLin0 = tlam (tvar tt)

-- `(λx.x) (λx.x)`, at the usage `false ∷ []`
selfApp0 : Tm (false ∷ [])
selfApp0 = tapp (uskip unil) idLin0 idLin0

-- an η-redex whose function part is NOT a λ, so only η can fire
etaRedex : Tm []
etaRedex = tlam (tapp (uright unil) selfApp0 (tvar tt))

-- ... and one whose function part is a λ, so β fires first
betaEtaRedex : Tm []
betaEtaRedex = tlam (tapp (uright unil) idLin0 (tvar tt))

_ : idPass [] idLin ≡ idLin
_ = refl

_ : betaPass [] selfApp ≡ idLin
_ = refl

_ : etaPass [] etaRedex ≡ selfApp
_ = refl

_ : etaPass [] betaEtaRedex ≡ idLin
_ = refl

-- β then η: `(λx. (λy.y) x)` ↦ `λx. x` by β, and the η-redex is gone
_ : optimise [] betaEtaRedex ≡ idLin
_ = refl

-- the identity pass really is the fold of the typing rules, at a point
_ : foldTm TmG roll [] selfApp ≡ selfApp
_ = refl

{-
  ==================================================================
  WHAT THE INDEX BOUGHT -- and where it bought nothing.
  ==================================================================

  BOUGHT.

  * The substitution lemma.  `substT : (BodyOf TmG ⊛ TmG) ⊢ TmG` is
    the whole statement, and its proof never mentions a context
    invariant -- the `Use⊎` reassociations in `subT` ARE the context
    reasoning, and they are forced by the type.  Written as
    `Tm → Tm → Tm` this would need a separate "substitution preserves
    typing" theorem; here there is nothing left to prove.  §3.4 goes
    one better: `substUP` says substitution IS the internal hom and β
    IS evaluation, with `substIsApp` holding by `refl`.

  * No duplication, no discarding, for free.  Every pass has type
    `TmG ⊢ TmG`, so its output owns exactly the variables its input
    owned.  `noSelfSplit` is the sharp form: a live usage does not
    split as itself twice, so no pass can copy a subterm that uses
    anything.  This is the fact `Passes/Inline.agda` cannot have.

  * Strengthening for free.  η-contraction in the untyped setting has
    to DECIDE that the function part survives at the smaller scope
    (`scoped?`, with a refutation branch).  Here `freshSplit` hands it
    over already strengthened, because the splitting said the fresh
    variable went elsewhere.

  * The dead-code theorem.  `deadBinder : DeadBinder ⊢ ⊥G` is a
    statement one cannot even phrase without the index.

  BOUGHT NOTHING.

  * Semantic correctness.  `TmG ⊢ TmG` says nothing about the pass
    preserving MEANING.  `etaPass` could return `λx. x` for every
    input and would still typecheck.  The index is a resource
    discipline, not a semantics, and every claim of the form "this
    really is η" in §5 is a claim about the code, not a theorem.
    Fixing that needs an evaluation relation and a motive that
    carries it -- the Quicksort `Spec` move -- and this file does not
    do it.

  * Termination of a normaliser.  `foldTm` is one bottom-up sweep.
    Iterating to a normal form needs a decreasing measure, and the
    grading the framework supplies (`live`) is the WRONG one -- it
    increases under a binder.  So `hyloC`/`löb` are unavailable here
    and the passes are single-sweep by necessity, not by choice.

  * Confluence, or any relation between the passes.  `optimise` is a
    composite because `_∘g_` composes; that `betaPass then etaPass`
    is better than either alone is an empirical remark about the
    `refl` tests in §6.

  * The index algebra itself.  §1 is 150 lines of `Use⊎` combinatorics
    -- associativity, exchange, markers -- that an unindexed
    development simply does not have.  It is paid once and reused by
    every pass, but it is a real cost and it is not "free" in any
    sense.  What the framework gave was the SHAPE (`⊗ˢ` is the
    splitting) rather than the proofs.

  ==================================================================
  WHAT IS NOT HERE.
  ==================================================================

  * A normaliser.  See "bought nothing", second bullet: the grading is
    the wrong measure, so `hyloC`/`löb` do not apply and the passes
    are single-sweep.

  * Any semantic statement about the passes.  §5's comments name what
    each branch is FOR; nothing checks it.

  * `⊸ᶠ` in `Context.agda`.  §3.4 builds `Focus linFib appop true`
    locally because this file may not touch `Context.agda`.  It
    belongs there -- it is a fact about the usage promodel, not about
    optimisation, and `Refinement`/`CanonicalFocus` would both want
    it.  Moving it is a one-line change to `Context.agda` and a
    deletion here.
-}
