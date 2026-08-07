{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  A PROGRAM LOGIC OVER AN ARBITRARY PROMODEL.

  `Instances/Heap/Hoare.agda` builds weakest preconditions, Hoare triples
  and the frame rule for heaps.  Not one line of that argument is about
  heaps, and this file is the proof: everything there is reproduced here
  over an arbitrary `Fibered σ ℓX ℓP`, with `∗` replaced by `⊗ˢ o` at an
  arbitrary operation and `Heap` replaced by the abstract carrier.

  ------------------------------------------------------------------
  1.  THE ASSERTION LOGIC IS ALREADY THERE, SO THE PROGRAM LOGIC IS FREE
  ------------------------------------------------------------------

  `TheoryTy ℓ s = carrier s → Type ℓ` is a DISPLAYED presentation: a type
  of the calculus is a family over the carrier, and `_⊢_` is a map of
  families over the identity.  A COMMAND is a relation between carriers,

      Cmd ℓC s t  =  F .carrier s → G .carrier t → Type ℓC,

  i.e. a profunctor between two DISCRETE categories -- ordinary
  metalanguage data, nothing internal.  Its two images

      wp c Q m   =  (m' : G .carrier t) → c m m' → Q m'
      sp c P m'  =  Σ[ m ∈ F .carrier s ] (P m × c m m')

  are again families, hence again types of the calculus, and therefore a
  HOARE TRIPLE IS AN ENTAILMENT OF THE LOGIC WE ALREADY HAVE:

      ⟪ P ⟫ c ⟪ Q ⟫   =   P ⊢ wp c Q.

  No new category, no new judgement, and no meta-level soundness theorem:
  the frame rule below is a term of the calculus.

  ------------------------------------------------------------------
  2.  `wp` IS REINDEXING, AND AT A FUNCTION IT IS THE CARTESIAN LIFT
  ------------------------------------------------------------------

  In the family fibration over the carrier, reindexing along a map is
  substitution and the Cartesian lift is composition.  `CarrierMap.Along`
  calls it `pull`:

      pull B m  =  B (h .hom s m).

  `wp` is the same operation along a RELATION rather than a function --
  it is the right adjoint to the direct image, and the adjunction

      sp c  ⊣  wp c                                       (`sp⊣wp`)

  is currying and swapping, with both round trips `refl` because Σ and Π
  both have definitional η.  Specialised to (the graph of) a function it
  is `Σ_f ⊣ f*`, the usual pair.

  The degeneration is exact, and this file makes it DEFINITIONAL rather
  than merely isomorphic, by spelling the graph of `f` in the direction
  the representable already uses:

      fn f m m'  =  m' Eq.≡ f m                (note the ORIENTATION),

  because with that orientation

      wp (fn f) Q m   =   (m' : _) → m' Eq.≡ f m → Q m'
                      =   ⌈ f m ⌉ ⊢ Q          -- ON THE NOSE

  (`wp-fn-repr`, proved by `refl`).  So `wp` at a function is the hom-set
  out of a representable, and `wp-fn` -- "the weakest precondition of a
  deterministic command is its postcondition, reindexed" -- is LITERALLY
  the Yoneda lemma `⌈⌉-UP`, not merely "in disguise" as the heap file put
  it.  The heap file's orientation (`f h Eq.≡ h'`) costs an `Eq.sym` at
  every use; this one costs none, and it makes `homParts` fit `Local`
  without a symmetry step (see 4).

  ONE THING DOES NOT SURVIVE, and the reason is a level, not a
  mathematical obstruction: `wp (fn f) Q ≡ pull Q` cannot even be STATED.
  `wp` quantifies over the carrier, so `wp (fn f) Q : TheoryTy (ℓ-max ℓX
  ℓA) s` whereas `pull Q : TheoryTy ℓA s`, and a `Path` needs one type.
  The Iso `wp-pull` is the honest statement, and its two directions
  `wp→pull` / `pull→wp` are the terms one actually composes with.  (Even
  at equal levels a path would be the wrong object: `subst` along it does
  not reduce, and CLAUDE.md's third trap says what that costs.)

  ------------------------------------------------------------------
  3.  THE FRAME RULE, SLOTWISE
  ------------------------------------------------------------------

  The heap statement is binary and reads

      (wp c Q) ∗ R  ⊢  wp c (Q ∗ R),

  with `R` untouched by `c`.  Generically the arity is an abstract type,
  there is no `boolΠ` to case on it, and "the slots other than i" is not
  computable without `Discrete (arities o)`.  The way out is to stop
  distinguishing the frame: give EVERY slot a command,

      d : (a : arities o) → Cmd (sortOf o a) (sortOf o a),

  and read the classical rule as the instance where `d i` is the real
  command and `d a` is `skip` at the frame slots -- `wp skip R ≅ R` by
  `wp-fn` at the identity, so nothing is lost.  Then the frame rule is

      frame-cmd :  ((a : arities o) → ⟪ A a ⟫ d a ⟪ B a ⟫)
                →  ⟪ ⊗ˢ o A ⟫ c ⟪ ⊗ˢ o B ⟫,

  A FAMILY OF TRIPLES COMPOSES TO A TRIPLE ON THE COMPOSITE, which is
  what the frame rule always was.  It is uniform in the arity, needs no
  eliminator for it, and specialises to the binary statement by
  instantiating `d` and `A` with the instance's own `boolΠ`.

  ------------------------------------------------------------------
  4.  `Local` IS `SplitPresAt`, AND ITS CONVERSE IS `ReflectsSplitAt`
  ------------------------------------------------------------------

      Local c d = (m) (sl : F .Split o m) (m') → c m m'
                → Σ[ sl' ∈ G .Split o m' ]
                    ((a) → d a (F .parts o m sl a) (G .parts o m' sl' a))

  It takes a splitting of the INPUT and hands back a splitting of the
  OUTPUT together with the slotwise action -- so no component of a
  splitting is ever projected, which is what makes it statable at an
  abstract `Split`/`parts` (the heap version needed `mkSplit`,
  `split-Ilv` and `split-#` precisely because it named `u`, `v` and their
  disjointness).  Compare `CarrierMap.SplitPresAt`:

      homSplit : Split o m → Split' o (hom m)
      homParts : parts' o (hom m) (homSplit m sl) a Eq.≡ hom (parts o m sl a)

  `Local` IS `SplitPresAt` with the function replaced by a relation and
  the equation `parts' = hom parts` replaced by `d a (parts) (parts')`.
  `Local-of-SplitPres` proves this: at the deterministic command `fn
  (hom)`, `homSplit` is the splitting and `homParts` is the slotwise
  datum, with no coercion and no `Eq.sym` (this is what the orientation
  of `fn` bought).

  The heap header called `Local` "`ReflectsSplit` transposed", and the
  transposition is literal: `ReflectsSplitAt` is `Local` OF THE CONVERSE
  COMMAND, read in `Hoare G F` rather than `Hoare F G`.
  `Local-of-Reflects` and `Reflects-of-Local` are inverse to each other
  and are pure currying -- the Σ-types are the same type.

  DID `frame-wp` FALL OUT OF `push⊗`?  No -- it is the other way round,
  and that is the better outcome.  `push⊗` is the SPECIAL CASE of
  `frame-wp` at a deterministic command: `push⊗-from-frame` derives
  `Along.push⊗` from `frame-wp` + `Local-of-SplitPres` + `wp-fn`, with no
  new content.  `pull⊗` does NOT arise the same way, and the reason is
  worth recording: `wp` along the converse of `hom` is the PUSHFORWARD
  (right Kan extension) `∀ m, hom m = m' → Q m`, not `pull`, so the
  converse frame rule is a statement about `Π_hom`, not about `pull`.
  `pull⊗` is instead an immediate corollary of `Reflects-of-Local`
  (`pull⊗-from-Local`).

  ------------------------------------------------------------------
  PHASE.  Phase 1 here is the language construction: `wp`, `sp`, their
  functorial actions, `fn`, and the two Iso packages -- each a definition
  of the calculus, all pointful by nature and none of them matching on a
  carrier.  `frame-wp`, `frame-cmd` and `consequence` are phase 2: `⊗ˢ-E`,
  `⊗ˢ-I`, `⊗ˢ-map`, `_∘g_`, `⌈⌉-UP` and `Local` handed to them.  NO
  extended lambda over an arity appears anywhere (they are nominal, so
  two copies would not reduce against each other); every function over
  `σ .arities o` is either a plain λ binding the slot uniformly or an
  argument.
-}
module TheoryGrammar.Hoare where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Rules
open import TheoryGrammar.RulesFib
open import TheoryGrammar.CarrierMap

private variable ℓS ℓ ℓ' ℓX ℓP ℓA ℓB ℓC ℓD ℓE : Level

-- ==================================================================
-- COMMANDS FROM ONE PROMODEL TO ANOTHER.
--
-- Both promodels are over the same signature and at the same levels,
-- which is what lets `Reindex` (and hence `pull`) be compared with `wp`
-- below.  The endo case `Hoare Fib Fib` -- packaged as `Endo` -- is the
-- one an instance normally wants; the heterogeneous case is what makes
-- "a command is a change of theory that need not be a function" precise.
-- ==================================================================

module Hoare {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
             (F G : Fibered σ ℓX ℓP) where

  -- the source's combinators, unqualified; the target's, qualified.
  -- Neither is re-exported, so an instance's own `open RulesF Fib` is
  -- undisturbed.
  open RulesF F
  module Tgt = RulesF G

  private variable s t : S

  -- ================================================================
  -- Commands, and the two images.
  -- ================================================================

  Cmd : (ℓC : Level) → S → S → Type (ℓ-max ℓX (ℓ-suc ℓC))
  Cmd ℓC s t = F .carrier s → G .carrier t → Type ℓC

  -- WEAKEST PRECONDITION -- reindexing along the relation.
  wp : Cmd ℓC s t → Tgt.TheoryTy ℓA t → TheoryTy (ℓ-max ℓX (ℓ-max ℓC ℓA)) s
  wp {t = t} c Q m = (m' : G .carrier t) → c m m' → Q m'

  -- STRONGEST POSTCONDITION -- the direct image.
  sp : Cmd ℓC s t → TheoryTy ℓA s → Tgt.TheoryTy (ℓ-max ℓX (ℓ-max ℓC ℓA)) t
  sp {s = s} c P m' = Σ[ m ∈ F .carrier s ] (P m × c m m')

  -- Functorial in the assertion: this is all `consequence` needs, and
  -- keeping it separate is what makes the rule of consequence a
  -- composite of `_∘g_` rather than a pointful proof.
  wp-map : (c : Cmd ℓC s t) {Q : Tgt.TheoryTy ℓA t} {Q' : Tgt.TheoryTy ℓB t}
         → Q Tgt.⊢ Q' → wp c Q ⊢ wp c Q'
  wp-map c f m w m' r = f m' (w m' r)

  sp-map : (c : Cmd ℓC s t) {P : TheoryTy ℓA s} {P' : TheoryTy ℓB s}
         → P ⊢ P' → sp c P Tgt.⊢ sp c P'
  sp-map c f m' (m , p , r) = m , f m p , r

  -- ================================================================
  -- THE ADJUNCTION `sp c ⊣ wp c`.  Currying and swapping; both round
  -- trips are `refl`, because Σ and Π both have η.
  -- ================================================================

  sp⊣wp : (c : Cmd ℓC s t) (P : TheoryTy ℓA s) (Q : Tgt.TheoryTy ℓB t)
        → Iso (sp c P Tgt.⊢ Q) (P ⊢ wp c Q)
  sp⊣wp c P Q .Iso.fun f m p m' r = f m' (m , p , r)
  sp⊣wp c P Q .Iso.inv g m' (m , p , r) = g m p m' r
  sp⊣wp c P Q .Iso.sec _ = refl
  sp⊣wp c P Q .Iso.ret _ = refl

  -- ================================================================
  -- HOARE TRIPLES are entailments.  Nothing new is introduced.
  -- ================================================================

  ⟪_⟫_⟪_⟫ : TheoryTy ℓA s → Cmd ℓC s t → Tgt.TheoryTy ℓB t
          → Type (ℓ-max ℓX (ℓ-max ℓA (ℓ-max ℓC ℓB)))
  ⟪ P ⟫ c ⟪ Q ⟫ = P ⊢ wp c Q

  -- the rule of consequence, from `∘g` and `wp-map` alone
  consequence : (c : Cmd ℓC s t)
                {P : TheoryTy ℓA s} {P' : TheoryTy ℓB s}
                {Q : Tgt.TheoryTy ℓD t} {Q' : Tgt.TheoryTy ℓE t}
              → P' ⊢ P → Q Tgt.⊢ Q' → ⟪ P ⟫ c ⟪ Q ⟫ → ⟪ P' ⟫ c ⟪ Q' ⟫
  consequence c pre post tr = wp-map c post ∘g tr ∘g pre

  -- ================================================================
  -- A DETERMINISTIC COMMAND IS A FUNCTION, AND `wp` AT ONE IS THE
  -- CARTESIAN LIFT.  With the graph oriented as `m' Eq.≡ f m`, `wp (fn
  -- f) Q m` is the hom out of the representable at `f m` DEFINITIONALLY,
  -- so `wp-fn` is not "the Yoneda lemma in disguise" -- it is `⌈⌉-UP`.
  -- ================================================================

  fn : (F .carrier s → G .carrier t) → Cmd ℓX s t
  fn f m m' = m' Eq.≡ f m

  wp-fn-repr : (f : F .carrier s → G .carrier t) (Q : Tgt.TheoryTy ℓA t)
               (m : F .carrier s)
             → wp (fn f) Q m ≡ (Tgt.⌈ f m ⌉ Tgt.⊢ Q)
  wp-fn-repr f Q m = refl

  wp-fn : (f : F .carrier s → G .carrier t) (Q : Tgt.TheoryTy ℓA t)
          (m : F .carrier s)
        → Iso (wp (fn f) Q m) (Q (f m))
  wp-fn f Q m = Tgt.⌈⌉-UP {a = f m} {B = Q}

  -- ================================================================
  -- LOCALITY AND THE FRAME RULE, at one operation.
  -- ================================================================

  module Frame (o : σ .ops) where

    -- one command per slot.  The classical rule is the instance where
    -- all but one of them is `skip`; see `Endo` and the header (3).
    SlotCmd : (ℓD : Level) → Type (ℓ-max ℓ' (ℓ-max ℓX (ℓ-suc ℓD)))
    SlotCmd ℓD = (a : σ .arities o) → Cmd ℓD (σ .sortOf o a) (σ .sortOf o a)

    -- ==============================================================
    -- LOCALITY.  A splitting of the INPUT yields a splitting of the
    -- OUTPUT, slotwise related by the slot commands.
    --
    -- Phrased entirely in `Split` and `parts`: the output splitting is
    -- HANDED BACK, never assembled, so nothing here projects a component
    -- of a splitting and no `mkSplit`-style primitive is needed.  This
    -- is `CarrierMap.SplitPresAt` with the function made a relation --
    -- see `Local-of-SplitPres` -- and its converse is
    -- `Along.ReflectsSplitAt`, see `Local-of-Reflects`.
    -- ==============================================================

    Local : Cmd ℓC (σ .resultSort o) (σ .resultSort o) → SlotCmd ℓD
          → Type (ℓ-max ℓX (ℓ-max ℓP (ℓ-max ℓ' (ℓ-max ℓC ℓD))))
    Local c d =
      (m : F .carrier (σ .resultSort o)) (sl : F .Split o m)
      (m' : G .carrier (σ .resultSort o)) → c m m'
      → Σ[ sl' ∈ G .Split o m' ]
          ((a : σ .arities o) → d a (F .parts o m sl a) (G .parts o m' sl' a))

    -- ==============================================================
    -- THE FRAME RULE.  `⊗ˢ-E` consumes the tensor, locality moves the
    -- splitting across the command, `⊗ˢ-I` rebuilds it at the output.
    --
    -- Compare `⊗ˢ-map`, the ASSERTION frame rule, which needs no
    -- hypothesis at all because functoriality is free.  This is the
    -- COMMAND frame rule and the whole difference is `Local`.
    -- ==============================================================

    frame-wp : (c : Cmd ℓC (σ .resultSort o) (σ .resultSort o)) (d : SlotCmd ℓD)
             → Local c d
             → (B : (a : σ .arities o) → Tgt.TheoryTy ℓA (σ .sortOf o a))
             → ⊗ˢ o (λ a → wp (d a) (B a)) ⊢ wp c (Tgt.⊗ˢ o B)
    frame-wp c d loc B =
      ⊗ˢ-E o {A = λ a → wp (d a) (B a)} {B = wp c (Tgt.⊗ˢ o B)}
        (λ m sl k m' r →
          Tgt.⊗ˢ-I o {A = B} m' (loc m sl m' r .fst)
            (λ a → k a (G .parts o m' (loc m sl m' r .fst) a)
                       (loc m sl m' r .snd a)))

    -- ... and its packaging as the composition of a FAMILY OF TRIPLES,
    -- which is the form an instance uses: `⊗ˢ-map` feeds the slotwise
    -- triples in, `frame-wp` does the rest.
    --
    -- NOT called `frame`: an instance's `frame` is conventionally the
    -- ASSERTION frame rule (`⊗ˢ-map`, hypothesis-free -- see
    -- `Heap/Connectives`), and the two must be openable together.
    frame-cmd : (c : Cmd ℓC (σ .resultSort o) (σ .resultSort o)) (d : SlotCmd ℓD)
          → Local c d
          → {A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a)}
            {B : (a : σ .arities o) → Tgt.TheoryTy ℓB (σ .sortOf o a)}
          → ((a : σ .arities o) → ⟪ A a ⟫ d a ⟪ B a ⟫)
          → ⟪ ⊗ˢ o A ⟫ c ⟪ Tgt.⊗ˢ o B ⟫
    frame-cmd c d loc {A = A} {B = B} k =
      frame-wp c d loc B ∘g ⊗ˢ-map o {A = A} {B = λ a → wp (d a) (B a)} k

-- ==================================================================
-- THE ENDO CASE -- a command on one promodel -- with `skip`.
--
-- `skip` is what makes the slotwise frame rule specialise to the
-- classical one: at a frame slot the command is `skip`, and `wp skip R`
-- is `R` by `wp-fn` at the identity.  An instance's binary rule
--
--     (wp c Q) ∗ R  ⊢  wp c (Q ∗ R)
--
-- is `Frame.frame-cmd` at `d = boolΠ c skip`, `A = boolΠ (wp c Q) R` and
-- `k = boolΠ idg (skip-I R)`; `boolΠ` is the instance's own arity
-- eliminator and cannot appear here, which is exactly why the generic
-- rule is stated slotwise.
--
-- Checked at `heapFib`: `Endo heapFib`'s `wp`, `sp` and `⟪_⟫_⟪_⟫` are
-- `refl`-equal to `Instances/Heap/Hoare`'s, and the four lines above
-- inhabit that file's `frame-wp` type verbatim.  The one step that is
-- genuinely instance-work is turning the heap's `Local` (stated with
-- `Ilv` and `_#_`) into this one -- it needs `split-Ilv`, `split-#` and
-- `mkSplit`, which is right: those primitives exist because the HEAP's
-- phrasing projects a splitting, and the generic phrasing is what
-- removes the need for them downstream.
-- ==================================================================

module Endo {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (Fib : Fibered σ ℓX ℓP) where

  open Hoare Fib Fib public
  open RulesF Fib

  private variable s : S

  skip : Cmd ℓX s s
  skip = fn (λ m → m)

  wp-skip : (Q : TheoryTy ℓA s) (m : Fib .carrier s) → Iso (wp skip Q m) (Q m)
  wp-skip Q = wp-fn (λ m → m) Q

  -- the two directions as terms of the calculus.  `skip-I` is `⌈⌉-E`:
  -- `wp skip Q m` IS `⌈ m ⌉ ⊢ Q`.
  skip-I : (Q : TheoryTy ℓA s) → Q ⊢ wp skip Q
  skip-I Q m q = ⌈⌉-E q

  skip-E : (Q : TheoryTy ℓA s) → wp skip Q ⊢ Q
  skip-E Q m w = w m Eq.refl

  -- `skip` is local at every operation, and the splitting it hands back
  -- is the one it was given.
  module _ (o : σ .ops) where

    open Frame o

    skipLocal : Local (skip {σ .resultSort o}) (λ a → skip)
    skipLocal m sl .m Eq.refl = sl , λ a → Eq.refl

-- ==================================================================
-- `wp` VERSUS `pull`: the Cartesian lift, and `push⊗` as an instance of
-- the frame rule.
-- ==================================================================

module ReindexHoare {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
                    {F G : Fibered σ ℓX ℓP} (h : Reindex F G) where

  open Hoare F G
  open RulesF F
  module A = Along h
  module Bwd = Hoare G F          -- commands the other way, for `Reflects`

  -- the deterministic command induced by `h`, at each sort
  cmd : (s : S) → Cmd ℓX s s
  cmd s = fn (h .hom s)

  -- ================================================================
  -- THE SHARPEST STATEMENT: `wp` along a function IS `pull`.
  --
  -- `A.pull B m` is `B (h .hom s m)` by definition and `wp (cmd s) B m`
  -- is `⌈ h .hom s m ⌉ ⊢ B` by definition, so this Iso is `⌈⌉-UP` with
  -- nothing added.  It is NOT a path, and cannot be: `wp` quantifies
  -- over the carrier, so the two sides sit at different levels.
  -- ================================================================

  wp-pull : (s : S) (B : Tgt.TheoryTy ℓA s) (m : F .carrier s)
          → Iso (wp (cmd s) B m) (A.pull B m)
  wp-pull s B m = wp-fn (h .hom s) B m

  wp→pull : (s : S) (B : Tgt.TheoryTy ℓA s) → wp (cmd s) B ⊢ A.pull B
  wp→pull s B m w = Iso.fun (wp-pull s B m) w

  pull→wp : (s : S) (B : Tgt.TheoryTy ℓA s) → A.pull B ⊢ wp (cmd s) B
  pull→wp s B m q = Iso.inv (wp-pull s B m) q

  module _ (o : σ .ops) where

    open Frame o
    module BwdFr = Bwd.Frame o

    -- ==============================================================
    -- `SplitPresAt` IS `Local`, for the deterministic command.  Note
    -- there is no coercion and no `Eq.sym`: `homParts` has exactly the
    -- orientation `fn` asks for.
    -- ==============================================================

    Local-of-SplitPres : SplitPresAt h o
                       → Local (cmd (σ .resultSort o)) (λ a → cmd (σ .sortOf o a))
    Local-of-SplitPres P m sl .(h .hom _ m) Eq.refl =
      P .homSplit m sl , λ a → P .homParts m sl a

    -- ==============================================================
    -- ... hence `push⊗` is the frame rule at a deterministic command.
    -- Nothing is proved again: `pull→wp`, `frame-wp`, `wp→pull`.
    --
    -- It is not merely a term of `push⊗`'s type but pointwise THE SAME
    -- MAP: unfolded, both are `homSplit m sl` paired with an
    -- `Eq`-elimination of `homParts m sl a` in the same direction (ours
    -- through `⌈⌉-E`, `Along`'s through its coercion).  That equation
    -- cannot be STATED here, however: `Along`'s coercion is `private`,
    -- and the two eliminators are nominally distinct, so neither side
    -- reduces at a stuck proof and no `with` can abstract the shared
    -- subterm.  Making it provable means exporting that coercion from
    -- `CarrierMap`, which is not this file's business.
    -- ==============================================================

    push⊗-from-frame : (P : SplitPresAt h o)
                       (B : (a : σ .arities o) → Tgt.TheoryTy ℓA (σ .sortOf o a))
                     → ⊗ˢ o (λ a → A.pull (B a)) ⊢ A.pull (Tgt.⊗ˢ o B)
    push⊗-from-frame P B =
        wp→pull (σ .resultSort o) (Tgt.⊗ˢ o B)
      ∘g frame-wp (cmd (σ .resultSort o)) (λ a → cmd (σ .sortOf o a))
                  (Local-of-SplitPres P) B
      ∘g ⊗ˢ-map o {A = λ a → A.pull (B a)}
                  {B = λ a → wp (cmd (σ .sortOf o a)) (B a)}
                  (λ a → pull→wp (σ .sortOf o a) (B a))

    -- ==============================================================
    -- THE TRANSPOSITION.  `ReflectsSplitAt` is `Local` of the CONVERSE
    -- command, read in `Hoare G F`.  The two Σ-types are the same type,
    -- so both directions are pure currying.
    -- ==============================================================

    revCmd : (s : S) → Bwd.Cmd ℓX s s
    revCmd s m' m = m' Eq.≡ h .hom s m

    Local-of-Reflects : A.ReflectsSplitAt o
                      → BwdFr.Local (revCmd (σ .resultSort o))
                                    (λ a → revCmd (σ .sortOf o a))
    Local-of-Reflects R .(h .hom _ m) sl' m Eq.refl = R m sl'

    Reflects-of-Local : BwdFr.Local (revCmd (σ .resultSort o))
                                    (λ a → revCmd (σ .sortOf o a))
                      → A.ReflectsSplitAt o
    Reflects-of-Local L m sl' = L (h .hom _ m) sl' m Eq.refl

    -- `pull⊗` is then immediate.  It is NOT an instance of `frame-wp`:
    -- `wp` along the converse of `h` is the pushforward `Π_h`, not
    -- `pull`, so the converse frame rule is a different statement.
    pull⊗-from-Local : BwdFr.Local (revCmd (σ .resultSort o))
                                   (λ a → revCmd (σ .sortOf o a))
                     → (B : (a : σ .arities o) → Tgt.TheoryTy ℓA (σ .sortOf o a))
                     → A.pull (Tgt.⊗ˢ o B) ⊢ ⊗ˢ o (λ a → A.pull (B a))
    pull⊗-from-Local L B = A.pull⊗ o (Reflects-of-Local L) {B = B}
