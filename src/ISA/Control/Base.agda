{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  CONTROL FLOW.  WHICH STRUCTURE GIVES `if`, AND WHICH GIVES `while`.

  `ISA.Program` makes program text the FREE MONOID on the instruction
  set, so `⊗ˢ appop` IS sequential composition and `ISA.Interp.seq` is
  its Hoare rule.  A monoid has no branching and no looping.  This file
  says exactly what has to be added, and the answer is not one thing but
  two, sitting on opposite sides of the development:

      `if`     is the ADDITIVE structure of the COMMAND promodel.
      `while`  is LÖB, and it is NOT free -- it costs a variant.

  Neither of them touches the program-text promodel.  That is the first
  result: control flow is a fact about `ISA.Machine.cmdFib`, not about
  `Strings`.

  ------------------------------------------------------------------
  1.  `if` IS `⊕` ON COMMANDS, AND `wp` TAKES IT TO `&ᴰ`
  ------------------------------------------------------------------

  A command is a relation, and relations are closed under UNION:

      sumC f h h'  =  Σ[ y ∈ Y ] f y h h'

  This is `⊕ᴰ` read at the two-variable family `Cmd = Res → Res → Type`,
  and it is the coproduct of the poset `(Cmd , ⊑)`.  `wp` is a RIGHT
  adjoint in its command argument (it is `Π` over the relation), so it
  takes that coproduct to a product:

      wp (sumC f) Q  ≅  &ᴰ Y (λ y → wp (f y) Q)                (`wp-sum`)

  and BOTH round trips are `refl` -- it is currying a Σ out of a Π,
  exactly as `wp-⨟` is currying two Π's past a Σ.  So `wp` is not merely
  a monoid antihomomorphism (`ISA.Machine`); it is a LAX MONOIDAL
  FUNCTOR OUT OF THE WHOLE ADDITIVE-AND-MULTIPLICATIVE COMMAND
  STRUCTURE, and every rule below is a reading of that.

  Read at `Y = Bool` this is already the rule for DEMONIC CHOICE
  (`choiceRule`), which is the conditional with the test erased.  To put
  the test back, note the other half of a conditional is `assume`:

      assume t b h h'  =  (t h Eq.≡ b) × (h Eq.≡ h')

  a SUBIDENTITY command, and `wp` sends it to the additive implication

      wp (assume t b) Q  ≅  Tst t b ⇒ Q                     (`wp-assume`)

  -- an assumption in the command becomes a HYPOTHESIS in the assertion,
  which is what a Hoare conditional rule is.  Put the three together,

      ifC t c d  =  (assume t true ⨟ c)  ⊔  (assume t false ⨟ d)

  and `condRule` is the composite

      wp-sum←  ∘  &ᴰ-I ∘ boolΠ  ∘  wp-⨟←  ∘  wp-assume←  ∘  ⇒-I,

  no induction, no case analysis, no program.  The answer to "is `if`
  simply the additive on commands, with the rule falling out of the
  elimination?" is YES, verbatim, with `⊕ᴰ`/`&ᴰ` in place of `⊕`/`&`
  because the choice is over the arity `Bool` rather than over two
  grammars.

  Two things are worth flagging.

  * The conditional is TOTAL where its branches are: `testFires` is
    `⊤G ⊢ ⊕ᴰ Bool (Tst t)`, one line, and it is the internal statement
    that the guard always decides.  Contrast `ISA.Toy`'s `store`, which
    is not `Local` precisely because it is partial.

  * `Tst t b` is the guard as an ASSERTION, and `Tst t true & Tst t false`
    is empty, so the two branches of `condRule` are genuinely exclusive.
    That is `TheoryGrammar.Decidable`'s shape -- a decision is an
    internal `⊤ ⊢ A ⊕ A'` -- at `A = Tst t true`, `A' = Tst t false`.

  ------------------------------------------------------------------
  2.  `while` IS NOT ADDITIVE.  IT IS A FIXED POINT.
  ------------------------------------------------------------------

  `sumC` is a FINITE union; a loop is an infinite one, and no amount of
  `⊕ᴰ` produces it, because the index of the union (how many times round)
  is not available in advance.  A loop is the fixed point of

      Φ(w)  =  ifC t (c ⨟ w) skip

  and there are exactly two ways to get one in this framework.  Both are
  below, and the difference between them is the whole content of the
  termination question.

  ROUTE A -- MAKE THE LOOP INDUCTIVE.  `While t c` is declared as a data
  type whose two constructors are the two branches of Φ.  Then the
  invariant rule

      {I & t}  c  {I}      ⟹      {I}  while t c  {I & ¬t}

  is `whileRuleInd`: TWO CLAUSES, by induction on the derivation, and it
  is the exact analogue of `ISA.Program.homSplit3` -- the development's
  other "one induction".  No variant, no rank, no well-foundedness.

  The catch is not in the proof, it is in the STATEMENT.  An inductive
  `While` relates `h` to `h'` only when the loop TERMINATES from `h`;
  divergence contributes no pair at all, because there is no final state
  to pair with.  So route A does not prove partial correctness of a
  possibly-diverging loop -- it defines divergence away.  That is a
  legitimate semantics (it is the standard operational one), but it is
  not available if the loop arrives as a JUMP, i.e. as a command someone
  hands you together with its unfolding equation and nothing else.  A
  real ISA's loop arrives exactly that way.

  ROUTE B -- LÖB.  Take `w : Cmd` ARBITRARY, knowing only

      w ⊑ ifC t ((c ↓) ⨟ w) skip.

  Then `loopRule` derives the invariant rule with no induction on
  anything: it is `löb` at the well-founded order `h ≺ h' = rank h <
  rank h'` on the RESOURCE, and the step is a term

      ▷ (I ⇒ wp w Inv)  ⊢  (I ⇒ wp w Inv)

  built from `condRule`, `refine`, `seqCmd` and `⇒-app`.  The loop's own
  rule is `condRule` again -- the body of a `while` IS an `if` -- and the
  recursive occurrence is discharged by `⇒-app` against the `▷`.

  The `↓` is where the cost sits.  `(c ↓) h h' = c h h' × (h' ≺ h)` is
  the strictly-decreasing part of the body, and

      ▷-wp : (▷ X & wp (c ↓) Y)  ⊢  wp (c ↓) (Y & X)

  is the ONE primitive route B needs.  It is this substrate's
  `Grammar/Later/Properties.agda`'s `▷-app-NE` -- "a `▷` may be consumed
  under a connective provided the connective moves strictly down the
  order" -- with `¬Nullable` replaced by `↓`, and it is two projections.

  ------------------------------------------------------------------
  3.  WHY THE VARIANT IS NOT AN ARTEFACT
  ------------------------------------------------------------------

  It is tempting to think `↓` is an accident of using `löb`, and that the
  unfolding equation alone ought to suffice.  It does not, and
  `noDescent` below is the proof: the rule

      w ⊑ ifC t (c ⨟ w) skip   →   {I & t} c {I}   →   {I} w {I & ¬t}

  with the descent dropped is INCONSISTENT.  Take `t` constantly true,
  `c = skip`, and `w` the TOTAL relation.  The unfolding holds (every
  step is available), the body triple is `skipRule`, and the conclusion
  hands back `true Eq.≡ false`.

  So the unfolding of a loop is a POST-fixed point and pins `w` only
  below the GREATEST fixed point, which contains the diverging runs.
  Selecting the least one -- which is what a Hoare rule needs -- is
  exactly a well-foundedness assumption.  Route A gets it from the data
  declaration; route B gets it from `rank`; nothing gets it for free.

  THAT is what unbounded `while` costs in a framework where everything
  descends by `deg<`: not expressiveness -- `While` is perfectly
  definable, and `loopRule` applies to any `w` at all -- but the ability
  to REASON about a loop you did not construct.  For that you must
  produce a descent, and a descent is a variant.  The framework's
  well-foundedness discipline is therefore not an obstacle to `while`; it
  is a correct diagnosis that `while` needs the same thing every other
  recursion in this development needs, and the reason `while` feels
  different is only that the order lives on the RESOURCE rather than on
  the program text.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1, all marked: `wp-sum→`/`wp-sum←`, `wp-assume→`/`wp-assume←`
  (the `wp`-computations, exactly as `wp-⨟`/`wp-skip` are in
  `ISA.Machine`), `testFires`, `decideT`, `▷-wp`, `↓⊑`, the `While` data
  declaration with `while-unfold`/`while-fold`, and `whileRuleInd`.
  Everything else -- `choiceRule`, `condRule`, `loopRule`, `whileRule` --
  is a composite of `⊢`-combinators.
-}
open import Cubical.Foundations.Prelude

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Theories.Monoid

module ISA.Control.Base (Fib : Fibered monoidSig ℓ-zero ℓ-zero) where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order using (_<_; <-wellfounded)
open import Cubical.Data.Unit
open import Cubical.Data.Empty as E using (⊥)
open import Cubical.Induction.WellFounded
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Later

open import ISA.Machine Fib public

-- ==================================================================
-- CHOICE.  The additive structure of the command promodel.
-- ==================================================================

-- A guard is a decidable predicate on the resource -- concretely, a
-- flag register.  Nothing below needs it to be anything else.
Test : Type₀
Test = Res → Bool

-- `⊕ᴰ` at the two-variable family: the union of a `Y`-indexed family of
-- commands.  This is the coproduct in `(Cmd , ⊑)`.
sumC : {Y : Type₀} → (Y → Cmd) → Cmd
sumC {Y} f h h' = Σ[ y ∈ Y ] f y h h'

-- binary nondeterministic choice, `sumC` at the arity `Bool`
_⊔c_ : Cmd → Cmd → Cmd
c ⊔c d = sumC (boolΠ {M = λ _ → Cmd} c d)

infixr 22 _⊔c_

-- ==================================================================
-- `wp` TAKES A UNION OF COMMANDS TO A `&ᴰ` OF PRECONDITIONS.
--
-- PRIMITIVE (phase 1), and the exact analogue of `wp-⨟`: currying a Σ
-- out of a Π.  Both round trips are `refl`, so this is an iso.
-- ==================================================================

wp-sum→ : {Y : Type₀} (f : Y → Cmd) (Q : Gr)
        → wp (sumC f) Q ⊢ &ᴰ Y (λ y → wp (f y) Q)
wp-sum→ f Q h w y h' r = w h' (y , r)

wp-sum← : {Y : Type₀} (f : Y → Cmd) (Q : Gr)
        → &ᴰ Y (λ y → wp (f y) Q) ⊢ wp (sumC f) Q
wp-sum← f Q h k h' (y , r) = k y h' r

-- both round trips, for the record
wp-sum-β : {Y : Type₀} (f : Y → Cmd) (Q : Gr) (h : Res)
           (w : &ᴰ Y (λ y → wp (f y) Q) h)
         → wp-sum→ f Q h (wp-sum← f Q h w) ≡ w
wp-sum-β f Q h w = refl

-- ==================================================================
-- DEMONIC CHOICE.  The conditional with the test erased -- already a
-- complete rule, and already a composite.
-- ==================================================================

choiceRule : {P Q : Gr} (c d : Cmd)
           → ⟪ P ⟫ c ⟪ Q ⟫ → ⟪ P ⟫ d ⟪ Q ⟫ → ⟪ P ⟫ c ⊔c d ⟪ Q ⟫
choiceRule {P} {Q} c d tc td =
  wp-sum← (boolΠ {M = λ _ → Cmd} c d) Q
  ∘g &ᴰ-I {Y = Bool} {A = P}
          {B = λ b → wp (boolΠ {M = λ _ → Cmd} c d b) Q}
       (boolΠ {M = λ b → P ⊢ wp (boolΠ {M = λ _ → Cmd} c d b) Q} tc td)

-- ==================================================================
-- GUARDS.  `Tst t b` is the guard as an ASSERTION; `assume t b` is the
-- guard as a SUBIDENTITY COMMAND.
-- ==================================================================

Tst : Test → Bool → Gr
Tst t b h = t h Eq.≡ b

assume : Test → Bool → Cmd
assume t b h h' = Tst t b h × (h Eq.≡ h')

-- PRIMITIVE (phase 1): THE GUARD ALWAYS DECIDES.  This is the internal
-- statement that a conditional is total -- `TheoryGrammar.Decidable`'s
-- `⊤ ⊢ A ⊕ A'` at `A = Tst t true`, `A' = Tst t false`.
testFires : (t : Test) → ⊤G ⊢ ⊕ᴰ Bool (Tst t)
testFires t h _ = t h , Eq.refl

-- ... and its useful form: any precondition splits along the guard.
decideT : (t : Test) {P : Gr} → P ⊢ ⊕ᴰ Bool (λ b → P & Tst t b)
decideT t h p = t h , p , Eq.refl

-- ==================================================================
-- `wp` TAKES AN ASSUMPTION TO AN IMPLICATION.
--
-- PRIMITIVE (phase 1).  `wp-assume←` is the only `Eq.refl` match in the
-- file's conditional half, and it is `wp-skip`'s inverse with a
-- hypothesis attached.
-- ==================================================================

wp-assume→ : (t : Test) (b : Bool) (Q : Gr) → wp (assume t b) Q ⊢ (Tst t b ⇒ Q)
wp-assume→ t b Q h w e = w h (e , Eq.refl)

wp-assume← : (t : Test) (b : Bool) (Q : Gr) → (Tst t b ⇒ Q) ⊢ wp (assume t b) Q
wp-assume← t b Q h k .h (e , Eq.refl) = k e

-- ==================================================================
-- THE CONDITIONAL, AND ITS HOARE RULE.
--
-- `ifC` is spelled through `ifBody` rather than inline, because the
-- arity `Bool` has no η and `boolΠ` must be a NAMED function for the two
-- branches to be seen as instances of one family.
-- ==================================================================

ifBody : Test → Cmd → Cmd → Bool → Cmd
ifBody t c d = boolΠ {M = λ _ → Cmd} (assume t true ⨟ c) (assume t false ⨟ d)

ifC : Test → Cmd → Cmd → Cmd
ifC t c d = sumC (ifBody t c d)

-- THE CONDITIONAL RULE.  A composite; nothing is matched.
condRule : {P Q : Gr} (t : Test) (c d : Cmd)
         → ⟪ P & Tst t true  ⟫ c ⟪ Q ⟫
         → ⟪ P & Tst t false ⟫ d ⟪ Q ⟫
         → ⟪ P ⟫ ifC t c d ⟪ Q ⟫
condRule {P} {Q} t c d tc td =
  wp-sum← (ifBody t c d) Q
  ∘g &ᴰ-I {Y = Bool} {A = P} {B = λ b → wp (ifBody t c d b) Q}
       (boolΠ {M = λ b → P ⊢ wp (ifBody t c d b) Q}
              (branch true c tc) (branch false d td))
  where
  branch : (b : Bool) (e : Cmd) → ⟪ P & Tst t b ⟫ e ⟪ Q ⟫
         → P ⊢ wp (assume t b ⨟ e) Q
  branch b e tr = wp-⨟← (assume t b) e Q
                ∘g wp-assume← t b (wp e Q)
                ∘g ⇒-I tr

-- the degenerate conditional: both branches the same command
ifC-triv : (t : Test) (c : Cmd) {P Q : Gr}
         → ⟪ P & Tst t true ⟫ c ⟪ Q ⟫ → ⟪ P & Tst t false ⟫ c ⟪ Q ⟫
         → ⟪ P ⟫ ifC t c c ⟪ Q ⟫
ifC-triv t c = condRule t c c

-- ==================================================================
-- THE LOOP, ROUTE A: DECLARE IT INDUCTIVE.
--
-- PRIMITIVE (phase 1): the two constructors are the two branches of the
-- unfolding `Φ(w) = ifC t (c ⨟ w) skip`, written as data.
-- ==================================================================

data While (t : Test) (c : Cmd) : Res → Res → Type₀ where
  wh-stop : {h h' : Res} → Tst t false h → h Eq.≡ h' → While t c h h'
  wh-step : {h h₁ h' : Res} → Tst t true h → c h h₁ → While t c h₁ h'
          → While t c h h'

-- ... and it really is a fixed point of Φ.  Both directions, both
-- PRIMITIVE (phase 1), and both are pure repackaging of the two
-- constructors against `sumC`/`assume`/`⨟`.
while-fold : (t : Test) (c : Cmd) → ifC t (c ⨟ While t c) skip ⊑ While t c
while-fold t c h h' (true  , _ , (e , Eq.refl) , _ , r , rest) = wh-step e r rest
while-fold t c h h' (false , _ , (e , Eq.refl) , p)            = wh-stop e p

while-unfold : (t : Test) (c : Cmd) → While t c ⊑ ifC t (c ⨟ While t c) skip
while-unfold t c h h' (wh-stop e p)                = false , h , (e , Eq.refl) , p
while-unfold t c h h' (wh-step {h₁ = h₁} e r rest) =
  true , h , (e , Eq.refl) , h₁ , r , rest

-- THE INVARIANT RULE, ROUTE A.  Two clauses, by induction on the
-- derivation -- the analogue of `ISA.Program.homSplit3`.  No variant
-- appears because an inductive `While` has already excluded divergence.
-- PRIMITIVE (phase 1).
whileRuleInd : (t : Test) (c : Cmd) (I : Gr)
             → ⟪ I & Tst t true ⟫ c ⟪ I ⟫
             → ⟪ I ⟫ While t c ⟪ I & Tst t false ⟫
whileRuleInd t c I body h i .h (wh-stop e Eq.refl) = i , e
whileRuleInd t c I body h i h' (wh-step {h₁ = h₁} e r rest) =
  whileRuleInd t c I body h₁ (body h (i , e) h₁ r) h' rest

-- ==================================================================
-- WHY THE UNFOLDING ALONE IS NOT ENOUGH.
--
-- The invariant rule stated for an ARBITRARY `w` satisfying only the
-- unfolding is INCONSISTENT.  `w` is pinned only below the GREATEST
-- fixed point of `Φ`, and that contains the diverging runs.
-- ==================================================================

noDescent : (h₀ : Res)
          → ((t : Test) (c w : Cmd) (I : Gr)
             → w ⊑ ifC t (c ⨟ w) skip
             → ⟪ I & Tst t true ⟫ c ⟪ I ⟫
             → ⟪ I ⟫ w ⟪ I & Tst t false ⟫)
          → ⊥
noDescent h₀ bad = tf (bad alwaysT skip total ⊤G unfold bodyTr h₀ tt h₀ tt .snd)
  where
  alwaysT : Test
  alwaysT _ = true

  total : Cmd
  total _ _ = Unit

  unfold : total ⊑ ifC alwaysT (skip ⨟ total) skip
  unfold h h' _ = true , h , (Eq.refl , Eq.refl) , h , Eq.refl , tt

  bodyTr : ⟪ ⊤G & Tst alwaysT true ⟫ skip ⟪ ⊤G ⟫
  bodyTr = skipRule ⊤G ∘g ⊤-I

  tf : true Eq.≡ false → ⊥
  tf ()

-- ==================================================================
-- THE LOOP, ROUTE B: LÖB AT A VARIANT.
--
-- Everything from here on is parameterised by a RANK on the resource.
-- `WFLater` is generic in a well-founded order and asks for nothing
-- else, so `▷` here is literally the same modality `TheoryGrammar.
-- Grading` builds -- only the order lives on the RESOURCE rather than on
-- the carrier of the promodel.
-- ==================================================================

module Variant (rank : Res → ℕ) where

  _≺_ : Res → Res → Type₀
  h ≺ h' = rank h < rank h'

  infix 4 _≺_

  private
    ≺-wf : WellFounded _≺_
    ≺-wf i = go (rank i) (<-wellfounded (rank i)) i refl
      where
      go : (n : ℕ) → Acc _<_ n → (j : Res) → rank j ≡ n → Acc _≺_ j
      go n (acc hh) j p =
        acc λ k q → go (rank k) (hh (rank k) (subst (rank k <_) p q)) k refl

  open WFLater _≺_ ≺-wf public using (▷; next; löb; löb-unfold; löb-unique)

  -- löb as a `⊢`, which is what a use site wants.  `▷ A ⊢ A` IS löb's
  -- step, definitionally.
  löbG : {A : Gr} → (▷ A ⊢ A) → ⊤G ⊢ A
  löbG {A} step h _ = löb {A = A} step h

  -- ================================================================
  -- THE STRICTLY-DECREASING PART OF A COMMAND.
  -- ================================================================

  _↓ : Cmd → Cmd
  (c ↓) h h' = c h h' × (h' ≺ h)

  -- PRIMITIVE (phase 1)
  ↓⊑ : (c : Cmd) → (c ↓) ⊑ c
  ↓⊑ c h h' = fst

  -- ================================================================
  -- THE ONE PRIMITIVE ROUTE B NEEDS.
  --
  -- `▷` passes into the postcondition of a strictly-decreasing command.
  -- This is `Grammar/Later/Properties.agda`'s `▷-app-NE` for this
  -- substrate: a `▷` may be consumed under a connective exactly when
  -- the connective moves strictly down the order.  Two projections.
  -- PRIMITIVE (phase 1).
  -- ================================================================

  ▷-wp : (c : Cmd) (X Y : Gr) → (▷ X & wp (c ↓) Y) ⊢ wp (c ↓) (Y & X)
  ▷-wp c X Y h (lat , k) h' r = k h' r , lat h' (r .snd)

  -- ================================================================
  -- THE LOOP RULE.  `w` is ARBITRARY: all that is known of it is its
  -- unfolding, with the body's descent folded in.  No induction on
  -- anything -- `löb`, `condRule`, `refine`, `seqCmd`, `⇒-app`.
  -- ================================================================

  loopRule : (t : Test) (c w : Cmd) (I : Gr)
           → w ⊑ ifC t ((c ↓) ⨟ w) skip
           → ⟪ I & Tst t true ⟫ c ↓ ⟪ I ⟫
           → ⟪ I ⟫ w ⟪ I & Tst t false ⟫
  loopRule t c w I unfold body = ⇒-E (löbG step ∘g ⊤-I) idg
    where
    Inv : Gr
    Inv = I & Tst t false

    A : Gr
    A = I ⇒ wp w Inv

    P : Gr
    P = ▷ A & I

    -- the recursive occurrence, discharged against the `▷`
    trueB : (P & Tst t true) ⊢ wp ((c ↓) ⨟ w) Inv
    trueB = wp-⨟← (c ↓) w Inv
          ∘g wp-map (c ↓) (⇒-app ∘g &-I &-E₂ &-E₁)
          ∘g ▷-wp c A I
          ∘g &-I (&-E₁ ∘g &-E₁) (body ∘g &-I (&-E₂ ∘g &-E₁) &-E₂)

    falseB : (P & Tst t false) ⊢ wp skip Inv
    falseB = skipRule Inv ∘g &-I (&-E₂ ∘g &-E₁) &-E₂

    inner : P ⊢ wp w Inv
    inner = refine unfold (condRule t ((c ↓) ⨟ w) skip trueB falseB)

    step : ▷ A ⊢ A
    step = ⇒-I inner

  -- ================================================================
  -- ... and the same rule at the INDUCTIVE loop, where the descent
  -- hypothesis is supplied once, per iteration, as the variant.
  -- ================================================================

  Decreasing : Test → Cmd → Type₀
  Decreasing t c = (h h₁ : Res) → Tst t true h → c h h₁ → h₁ ≺ h

  -- PRIMITIVE (phase 1): the unfolding, with the descent inserted.
  while-unfold↓ : (t : Test) (c : Cmd) → Decreasing t c
                → While t c ⊑ ifC t ((c ↓) ⨟ While t c) skip
  while-unfold↓ t c dec h h' (wh-stop e p) = false , h , (e , Eq.refl) , p
  while-unfold↓ t c dec h h' (wh-step {h₁ = h₁} e r rest) =
    true , h , (e , Eq.refl) , h₁ , (r , dec h h₁ e r) , rest

  -- THE INVARIANT RULE, ROUTE B.  A composite of `loopRule` and
  -- `refine`; the ONLY thing this asks over route A is `Decreasing`.
  whileRule : (t : Test) (c : Cmd) (I : Gr) → Decreasing t c
            → ⟪ I & Tst t true ⟫ c ⟪ I ⟫
            → ⟪ I ⟫ While t c ⟪ I & Tst t false ⟫
  whileRule t c I dec body =
    loopRule t c (While t c) I (while-unfold↓ t c dec) (refine (↓⊑ c) body)
