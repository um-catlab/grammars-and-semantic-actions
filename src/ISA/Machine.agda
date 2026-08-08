{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  AN ISA HAS TWO MONOIDS, AND A HOMOMORPHISM BETWEEN THEM.

  This file is the second of the two, in the abstract.

  ------------------------------------------------------------------
  THE TWO STRUCTURES
  ------------------------------------------------------------------

  Read an instruction-set architecture off the two things it is made of,
  and both of them are promodels this development already has:

    * PROGRAM TEXT is a FREE MONOID on the instruction set.  A splitting
      `Split appop p` is a way of writing `p = p₁ ++ p₂`, so `⊗ˢ appop`
      at that promodel IS sequential composition of program text.  That
      is `TheoryGrammar.Instances.Strings` at an alphabet of
      instructions, and nothing about it is new.

    * MACHINE RESOURCE is a PARTIAL COMMUTATIVE MONOID -- registers and
      memory, splitting disjointly.  That is
      `TheoryGrammar.Instances.Heap`, and again nothing about it is new.

  This file fixes the SECOND one abstractly: it takes an arbitrary
  promodel `Fib` over the monoid signature and builds, over it, the whole
  command/weakest-precondition layer.  It never mentions heaps, cells,
  locations, instructions or lists.  `ISA.Interp` fixes the first one
  abstractly; `ISA.Program` supplies the free monoid; `ISA.Toy`
  instantiates both.

  ------------------------------------------------------------------
  COMMANDS FORM A MONOID, AND `wp` IS AN ANTIHOMOMORPHISM
  ------------------------------------------------------------------

  A command is a relation `c : Res → Res → Type`.  Relations under
  composition are a monoid (up to iso):

      skip  h h'  = h Eq.≡ h'
      (c ⨟ d) h h'' = Σ h', c h h' × d h' h''

  The weakest precondition is the right adjoint to the direct image,

      wp c Q h = (h' : Res) → c h h' → Q h'          (`sp c ⊣ wp c`)

  and it is CONTRAVARIANT in the command (`wp-⊑`) and COVARIANT in the
  postcondition (`wp-map`).  The one computation that matters is that it
  turns `⨟` into function composition:

      wp (c ⨟ d) Q  ≅  wp c (wp d Q)                 (`wp-⨟`)

  and BOTH round trips are `refl` -- it is currying and swapping two Π's
  past a Σ, and Σ and Π both have definitional η.  So

      (Cmd, ⨟, skip)  --wp-->  (Gr → Gr, ∘, id)      is a monoid
                                                     ANTIhomomorphism.

  THAT IS THE WHOLE OF THE HOARE SEQUENCING RULE.  `seqCmd` below is

      wp-⨟← ∘g wp-map c t₂ ∘g t₁

  three combinators, no induction, no case analysis, no program.  It is
  worth being precise about what has been bought: the Hoare rule

      {P} c {R}   {R} d {Q}
      ---------------------
         {P} c ⨟ d {Q}

  is not a fact about programs at all.  It is the statement that `wp` is
  a lax monoidal functor out of the command monoid, and once `wp-⨟` is
  `refl` the rule is a composite of identities.

  ------------------------------------------------------------------
  COMMANDS ARE THEMSELVES A PROMODEL
  ------------------------------------------------------------------

  `cmdFib` below makes that structure first class: `Split appop c` is a
  FACTORISATION of `c`, i.e. a pair `(c₁ , c₂)` with `c ⊑ c₁ ⨟ c₂`.  Note
  the inequality -- the splitting is LAX, exactly as `Bags`' `Ilv` is
  lax, and for the same reason: a promodel is allowed to be strictly
  larger than the graph of its point.  With `cmdFib` in hand, "`⟦_⟧` is
  a monoid homomorphism" becomes "`⟦_⟧` is a map of promodels preserving
  splittings" -- `TheoryGrammar.CarrierMap`'s `SplitPresAt`, which is
  precisely what `ISA.Interp` asks for.

  (`SplitPresAt` is not literally reusable here only because `Reindex`
  forces the two promodels to the SAME universe levels, and `Cmd` lives
  one level up from `Res`.  The shape is copied field for field.)

  ------------------------------------------------------------------
  SEPARATION AND THE FRAME RULE
  ------------------------------------------------------------------

  Since `Fib` is a promodel over the monoid signature, `∗` and `emp` are
  just `⊗ˢ appop` and `⊗ˢ nilop` -- nothing local to heaps was used, so
  the ASSERTION-level frame rule is `⊗ˢ-map` and is free.  The
  COMMAND-level frame rule needs a hypothesis, and the hypothesis is
  `Local`: a decomposition of the OUTPUT must come from one of the INPUT
  with the frame untouched.  That is `ChangeOfTheory`'s "reflects
  splittings" transposed from a function to a relation, and it is stated
  here purely in terms of `Split` and `parts` -- no `Ilv`, no `#`, no
  heap.  `TheoryGrammar.Instances.Heap.Hoare`'s `Local` is this one read
  at `heapFib`.

  CAVEAT, stated plainly because it is inherited rather than invented:
  this `Local` has no safety side condition, so it holds only of commands
  that are defined everywhere and leave the frame alone.  A
  small-footprint store fails it (see `ISA.Toy`).  Nondeterministic
  ALLOCATION satisfies it, and that is the frame example the toy uses.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1 here: `boolΠ` (the arity eliminator -- never an extended
  lambda, which Agda identifies nominally), `coeG`, `eqTrans`, `wp`,
  `sp`, `skip`, `_⨟_`, `cmdFib`.  Everything else -- `seqCmd`,
  `skipRule`, `consequence`, `frame-wp`, `local-⨟` -- is a composite.
-}
open import Cubical.Foundations.Prelude

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Theories.Monoid

module ISA.Machine (Fib : Fibered monoidSig ℓ-zero ℓ-zero) where

open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit
open import Cubical.Data.Empty as E using (⊥; ⊥*)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.RulesFib

-- the connectives and the additive combinators over the resource
-- promodel, inherited wholesale
open RulesF Fib public

-- ==================================================================
-- Resources and assertions.
-- ==================================================================

Res : Type₀
Res = Fib .carrier tt

Gr : Type₁
Gr = TheoryTy ℓ-zero tt

-- The dependent eliminator for the arity of a binary operation.
-- PRIMITIVE (phase 1), and the ONE place `true`/`false` are matched.
-- An extended lambda here would be nominally distinct from every other
-- extended lambda over `Bool`, which is why this is a named function.
-- `boolΠ` now comes from `TheoryGrammar.Base`, opened above.

-- Coercion of an assertion along `Eq`.  PRIMITIVE (phase 1): the one
-- match on `Eq.refl` in the file, kept out of every theorem below.
coeG : (A : Gr) {x y : Res} → x Eq.≡ y → A x → A y
coeG A Eq.refl a = a

eqTrans : {x y z : Res} → x Eq.≡ y → y Eq.≡ z → x Eq.≡ z
eqTrans Eq.refl q = q

-- ==================================================================
-- SEPARATION.  `∗` is `⊗ˢ appop`, `emp` is `⊗ˢ nilop`.  Nothing about
-- heaps; the whole content is in `Fib .Split`.
-- ==================================================================

emp : Gr
emp = ⊗ˢ nilop (λ ())

_∗_ : Gr → Gr → Gr
A ∗ B = ⊗ˢ appop (boolΠ {M = λ _ → Gr} A B)

infixr 20 _∗_

-- the ASSERTION frame rule: functoriality, and therefore free
∗-map : {A B : Gr} (C : Gr) → A ⊢ B → (A ∗ C) ⊢ (B ∗ C)
∗-map {A} {B} C f =
  ⊗ˢ-map appop {A = boolΠ {M = λ _ → Gr} A C} {B = boolΠ {M = λ _ → Gr} B C}
         (boolΠ {M = λ a → boolΠ {M = λ _ → Gr} A C a
                         ⊢ boolΠ {M = λ _ → Gr} B C a} f idg)

-- ==================================================================
-- COMMANDS.
-- ==================================================================

Cmd : Type₁
Cmd = Res → Res → Type₀

-- refinement / containment of commands
_⊑_ : Cmd → Cmd → Type₀
c ⊑ d = (h h' : Res) → c h h' → d h h'

infix 4 _⊑_

⊑-refl : (c : Cmd) → c ⊑ c
⊑-refl c h h' r = r

⊑-trans : {c d e : Cmd} → c ⊑ d → d ⊑ e → c ⊑ e
⊑-trans p q h h' r = q h h' (p h h' r)

-- the unit and the multiplication of the command monoid
skip : Cmd
skip h h' = h Eq.≡ h'

_⨟_ : Cmd → Cmd → Cmd
(c ⨟ d) h h'' = Σ[ h' ∈ Res ] (c h h' × d h' h'')

infixr 25 _⨟_

-- a deterministic command is a function; `wp` at one is reindexing
fn : (Res → Res) → Cmd
fn f h h' = f h Eq.≡ h'

-- ==================================================================
-- THE TWO IMAGES, AND THE ADJUNCTION `sp c ⊣ wp c`.
-- ==================================================================

wp : Cmd → Gr → Gr
wp c Q h = (h' : Res) → c h h' → Q h'

sp : Cmd → Gr → Gr
sp c P h' = Σ[ h ∈ Res ] (P h × c h h')

sp⊣wp : (c : Cmd) (P Q : Gr) → Iso (sp c P ⊢ Q) (P ⊢ wp c Q)
sp⊣wp c P Q .Iso.fun f h p h' r = f h' (h , p , r)
sp⊣wp c P Q .Iso.inv g h' (h , p , r) = g h p h' r
sp⊣wp c P Q .Iso.sec _ = refl
sp⊣wp c P Q .Iso.ret _ = refl

-- ==================================================================
-- FUNCTORIALITY OF `wp`.  Covariant in the postcondition, CONTRAVARIANT
-- in the command.  These two and `wp-⨟` are the entire toolkit.
-- ==================================================================

wp-map : (c : Cmd) {Q Q' : Gr} → Q ⊢ Q' → wp c Q ⊢ wp c Q'
wp-map c f h w h' r = f h' (w h' r)

wp-⊑ : {c d : Cmd} → c ⊑ d → (Q : Gr) → wp d Q ⊢ wp c Q
wp-⊑ le Q h w h' r = w h' (le h h' r)

-- ==================================================================
-- `wp` TURNS `⨟` INTO COMPOSITION -- and both round trips are `refl`.
-- This is the monoid antihomomorphism, and it is the sequencing rule.
-- ==================================================================

wp-⨟ : (c d : Cmd) (Q : Gr) (h : Res)
     → Iso (wp (c ⨟ d) Q h) (wp c (wp d Q) h)
wp-⨟ c d Q h .Iso.fun w h' r h'' r' = w h'' (h' , r , r')
wp-⨟ c d Q h .Iso.inv v h'' (h' , r , r') = v h' r h'' r'
wp-⨟ c d Q h .Iso.sec _ = refl
wp-⨟ c d Q h .Iso.ret _ = refl

wp-⨟→ : (c d : Cmd) (Q : Gr) → wp (c ⨟ d) Q ⊢ wp c (wp d Q)
wp-⨟→ c d Q h = wp-⨟ c d Q h .Iso.fun

wp-⨟← : (c d : Cmd) (Q : Gr) → wp c (wp d Q) ⊢ wp (c ⨟ d) Q
wp-⨟← c d Q h = wp-⨟ c d Q h .Iso.inv

-- ... and `skip` to the identity: this is the Yoneda lemma (`⌈⌉-UP`),
-- since `skip h = ⌈ h ⌉`.
wp-skip : (Q : Gr) (h : Res) → Iso (wp skip Q h) (Q h)
wp-skip Q h .Iso.fun w = w h Eq.refl
wp-skip Q h .Iso.inv q .h Eq.refl = q
wp-skip Q h .Iso.sec _ = refl
wp-skip Q h .Iso.ret w = funExt λ _ → funExt λ { Eq.refl → refl }

-- the same for an arbitrary deterministic command: `wp (fn f) Q ≅ Q ∘ f`
wp-fn : (f : Res → Res) (Q : Gr) (h : Res) → Iso (wp (fn f) Q h) (Q (f h))
wp-fn f Q h .Iso.fun w = w (f h) Eq.refl
wp-fn f Q h .Iso.inv q .(f h) Eq.refl = q
wp-fn f Q h .Iso.sec _ = refl
wp-fn f Q h .Iso.ret w = funExt λ _ → funExt λ { Eq.refl → refl }

-- ==================================================================
-- HOARE TRIPLES ARE ENTAILMENTS.  Nothing new is introduced.
-- ==================================================================

⟪_⟫_⟪_⟫ : Gr → Cmd → Gr → Type₀
⟪ P ⟫ c ⟪ Q ⟫ = P ⊢ wp c Q

-- the rule of consequence: `∘g` and `wp-map`
consequence : {P P' Q Q' : Gr} (c : Cmd)
            → P' ⊢ P → Q ⊢ Q' → ⟪ P ⟫ c ⟪ Q ⟫ → ⟪ P' ⟫ c ⟪ Q' ⟫
consequence c pre post tr = wp-map c post ∘g tr ∘g pre

-- the rule of refinement: shrinking the command WEAKENS nothing
refine : {P Q : Gr} {c d : Cmd} → c ⊑ d → ⟪ P ⟫ d ⟪ Q ⟫ → ⟪ P ⟫ c ⟪ Q ⟫
refine {Q = Q} le tr = wp-⊑ le Q ∘g tr

-- ==================================================================
-- THE SEQUENCING RULE AT THE LEVEL OF COMMANDS.
--
-- Three combinators.  No induction, no program, no case analysis: it is
-- exactly `wp` being an antihomomorphism, read as a rule.
-- ==================================================================

seqCmd : {P R Q : Gr} (c d : Cmd)
       → ⟪ P ⟫ c ⟪ R ⟫ → ⟪ R ⟫ d ⟪ Q ⟫ → ⟪ P ⟫ c ⨟ d ⟪ Q ⟫
seqCmd {Q = Q} c d t₁ t₂ = wp-⨟← c d Q ∘g wp-map c t₂ ∘g t₁

skipRule : (Q : Gr) → ⟪ Q ⟫ skip ⟪ Q ⟫
skipRule Q h q = wp-skip Q h .Iso.inv q

-- ==================================================================
-- COMMANDS AS A PROMODEL.
--
-- `Split appop c` is a lax FACTORISATION of `c`; `Split nilop c` says
-- `c` is at most `skip`.  With this, "⟦_⟧ is a monoid homomorphism" is
-- literally "⟦_⟧ preserves splittings" -- `CarrierMap.SplitPresAt`.
-- ==================================================================

CmdSplit : (o : MonOp) → Cmd → Type₁
CmdSplit nilop c = Lift (ℓ-suc ℓ-zero) (c ⊑ skip)
CmdSplit appop c = Σ[ c₁ ∈ Cmd ] Σ[ c₂ ∈ Cmd ] (c ⊑ c₁ ⨟ c₂)

CmdParts : (o : MonOp) (c : Cmd) → CmdSplit o c → MonAr o → Cmd
CmdParts nilop c sp ()
CmdParts appop c (c₁ , c₂ , _) = boolΠ {M = λ _ → Cmd} c₁ c₂

cmdFib : Fibered monoidSig (ℓ-suc ℓ-zero) (ℓ-suc ℓ-zero)
cmdFib .carrier _ = Cmd
cmdFib .Split     = CmdSplit
cmdFib .parts     = CmdParts

-- The command monoid really is one: `⨟` splits itself, `skip` is nil.
-- (This is `LaxPoint cmdFib` minus the level bookkeeping.)
⨟-split : (c d : Cmd) → CmdSplit appop (c ⨟ d)
⨟-split c d = c , d , ⊑-refl (c ⨟ d)

skip-split : CmdSplit nilop skip
skip-split = lift (⊑-refl skip)

-- ==================================================================
-- LOCALITY AND THE COMMAND FRAME RULE.
--
-- `Local c` is `ReflectsSplit` transposed to a relation: every splitting
-- of the input is carried to one of the output with the frame slot
-- unchanged.  Stated with `Split`/`parts` only -- generic in the
-- resource promodel.
-- ==================================================================

Local : Cmd → Type₀
Local c =
  (h : Res) (sp : Fib .Split appop h) (h' : Res) → c h h'
  → Σ[ sp' ∈ Fib .Split appop h' ]
      ( c (Fib .parts appop h sp true) (Fib .parts appop h' sp' true)
      × (Fib .parts appop h' sp' false Eq.≡ Fib .parts appop h sp false) )

local-skip : Local skip
local-skip h sp .h Eq.refl = sp , Eq.refl , Eq.refl

local-⨟ : (c d : Cmd) → Local c → Local d → Local (c ⨟ d)
local-⨟ c d lc ld h sp h'' r =
  ld' .fst
  , (Fib .parts appop (r .fst) (lc' .fst) true , lc' .snd .fst , ld' .snd .fst)
  , eqTrans (ld' .snd .snd) (lc' .snd .snd)
  where
  lc' = lc h sp (r .fst) (r .snd .fst)
  ld' = ld (r .fst) (lc' .fst) h'' (r .snd .snd)

-- THE COMMAND FRAME RULE.  `⊗ˢ-E` consumes the `∗`, locality moves the
-- splitting across the command, `⊗ˢ-I` rebuilds it.  Generic: the only
-- heap-specific thing about the version in `Heap.Hoare` was the names.
frame-wp : (c : Cmd) → Local c → (Q R : Gr) → ((wp c Q) ∗ R) ⊢ wp c (Q ∗ R)
frame-wp c loc Q R =
  ⊗ˢ-E appop {A = boolΠ {M = λ _ → Gr} (wp c Q) R}
    (λ h sp k h' ch →
      let l   = loc h sp h' ch
          sp' = l .fst
      in ⊗ˢ-I appop {A = boolΠ {M = λ _ → Gr} Q R} h' sp'
           (boolΠ {M = λ a → boolΠ {M = λ _ → Gr} Q R a
                               (Fib .parts appop h' sp' a)}
                  (k true (Fib .parts appop h' sp' true) (l .snd .fst))
                  (coeG R (Eq.sym (l .snd .snd)) (k false))))

-- and the frame rule as a rule about TRIPLES
frameRuleCmd : {P Q : Gr} (R : Gr) (c : Cmd) → Local c
             → ⟪ P ⟫ c ⟪ Q ⟫ → ⟪ P ∗ R ⟫ c ⟪ Q ∗ R ⟫
frameRuleCmd {P} {Q} R c loc t = frame-wp c loc Q R ∘g ∗-map R t
