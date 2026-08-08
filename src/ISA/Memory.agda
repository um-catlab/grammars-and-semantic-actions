{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  ASSEMBLY WITH A MEMORY MODEL, AND THE SEMANTICS IS STILL A PASS.

  ------------------------------------------------------------------
  WHY THIS EXISTS
  ------------------------------------------------------------------

  `Compile.LinToISA.NoTextPres` proves that code generation is NOT a
  pass into the free-monoid theory of program text, and the reason is
  not a defect of the compiler:

      A HEAP SPLITTING IS UNORDERED.  CONCATENATION IS ORDERED.

  `compileU u` stores address 0 then 1; the two halves of a splitting
  that takes the second variable LEFT emit them in the other order.
  Same instructions, same heap, different lists.

  The repair is to give assembly the theory it actually has.  The
  memory model is one sentence,

      INSTRUCTIONS WITH DISJOINT FOOTPRINTS COMMUTE,

  and this file is what that sentence costs.

  ------------------------------------------------------------------
  IT IS A SPLITTING, NOT A QUOTIENT
  ------------------------------------------------------------------

  The obvious move -- quotient `List Instr` by disjoint transposition --
  is the wrong one twice over.  A set-quotient does not compute, so
  every `refl` test downstream dies; and it would make the CARRIER
  bigger-typed for a fact that belongs to the SPLITTING.

  The right move is already in this repository, twice.
  `TheoryGrammar.Instances.Heap.Base` and `Bags` both take

      Split appop m  =  Σ m₁ , Σ m₂ , Ilv m₁ m₂ m  ×  (m₁ # m₂)

  -- an INTERLEAVING with an apartness side condition -- and that is
  exactly the memory model.  Two programs interleave into one, and any
  interleaving is as good as any other PROVIDED their footprints are
  disjoint.  `asmFib` below is `Strings.Base.strFib` with `Split3`
  (concatenation) replaced by `Ilv` (interleaving) and `Disj` added,
  and nothing else changes.

  So the memory model is not new machinery.  It is the observation that
  program text splits like a HEAP rather than like a STRING, once you
  are allowed to say which instructions commute.

  ------------------------------------------------------------------
  WHAT IT COSTS: ONE HYPOTHESIS, AND IT IS THE HONEST ONE
  ------------------------------------------------------------------

  Relaxing the splitting cannot be free -- `ISA.Pass.semPass` used
  `Split3`, and a lax interleaving is strictly more splittings to
  preserve.  The extra obligation is `Commutes`:

      ⌣-comm : i ⌣ j → (step i ⨟ step j) ⊑ (step j ⨟ step i)

  which is the memory model stated where it can be USED, at the level
  of commands rather than of syntax.  `⌣` is data supplied by the
  instantiation -- for `Compile.LinToISA` it is "`putI l _` and
  `putI k _` with `Diff l k`" -- and `⌣-comm` is the one thing an ISA
  must prove to claim its memory model.

  `memPass` then says: with that hypothesis, the semantics is STILL a
  pass, now out of the relaxed theory.  So nothing that was proved for
  the rigid theory is lost, and the extra splittings are covered.

  ------------------------------------------------------------------
  THE SHAPE OF THE PROOF
  ------------------------------------------------------------------

  `ilv-sem` is an induction on `Ilv` with three clauses.  `ileft` is
  the easy one -- the head is already at the front of the left part, so
  it is an associativity.  `iright` is where the memory model is spent:
  the head belongs to the RIGHT part but sits at the front of the
  whole, so it must be moved PAST the entire left part, which is
  `commPast`, an induction using `⌣-comm` once per instruction.

  That asymmetry is the content.  Interleaving is exactly
  concatenation plus the right to commute, and `commPast` is the only
  place the right is exercised.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1: promodel construction and its metatheory.  `Ilv` is data,
  `Disj`/`All⌣` are `Unit`/`×`-valued recursive predicates in
  `Syntax.Same`'s style so their proofs compute, and the `⨟` laws are
  Σ-rebracketings -- the same two clauses `ISA.Program.homSplit3` is.
-}
open import Cubical.Foundations.Prelude

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Theories.Monoid
import ISA.Machine

module ISA.Memory (Fib   : Fibered monoidSig ℓ-zero ℓ-zero)
                  (Instr : Type₀)
                  (step  : Instr → ISA.Machine.Cmd Fib) where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit
open import Cubical.Data.List using (List; []; _∷_; _++_)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Reindex.Base
open import TheoryGrammar.Reindex.Pass

-- `Cmd`, `⊑`, `skip`, `_⨟_`, `cmdFib`, `Program`, `sem`, `Interp`, and
-- the rigid theory's `semPass` are all inherited
open import ISA.Pass Fib Instr step public

-- ==================================================================
-- §1  THE LAWS OF `⨟`.
--
-- Relational composition is associative and unital, and `⊑` is a
-- congruence for it.  Every proof is a Σ-rebracketing; none of them
-- mentions an instruction.
-- ==================================================================

⨟-mono : {c c' d d' : Cmd} → c ⊑ c' → d ⊑ d' → (c ⨟ d) ⊑ (c' ⨟ d')
⨟-mono p q h h'' (k , ch , dh) = k , p h k ch , q k h'' dh

⨟-assoc→ : (c d e : Cmd) → ((c ⨟ d) ⨟ e) ⊑ (c ⨟ (d ⨟ e))
⨟-assoc→ c d e h h'' (k₂ , (k₁ , ch , dh) , eh) = k₁ , ch , (k₂ , dh , eh)

⨟-assoc← : (c d e : Cmd) → (c ⨟ (d ⨟ e)) ⊑ ((c ⨟ d) ⨟ e)
⨟-assoc← c d e h h'' (k₁ , ch , (k₂ , dh , eh)) = k₂ , (k₁ , ch , dh) , eh

⨟-unitL← : (c : Cmd) → c ⊑ (skip ⨟ c)
⨟-unitL← c h h' ch = h , Eq.refl , ch

⨟-unitR← : (c : Cmd) → c ⊑ (c ⨟ skip)
⨟-unitR← c h h' ch = h' , ch , Eq.refl

-- PRIMITIVE (phase 1): the two clauses that match on `Eq.refl`.
⨟-unitR→ : (c : Cmd) → (c ⨟ skip) ⊑ c
⨟-unitR→ c h h' (k , ch , Eq.refl) = ch

-- ==================================================================
-- §2  THE MEMORY MODEL, AS DATA AND AS A LAW.
-- ==================================================================

-- `i ⌣ j` -- "these two instructions have disjoint footprints".  DATA,
-- supplied by the instantiation; this module never inspects it.
Apart : Type₁
Apart = Instr → Instr → Type₀

module _ (_⌣_ : Apart) where

  -- THE LAW.  Stated at commands, which is where it is used.
  Commutes : Type₀
  Commutes = (i j : Instr) → i ⌣ j → (step i ⨟ step j) ⊑ (step j ⨟ step i)

  Symmetric : Type₀
  Symmetric = (i j : Instr) → i ⌣ j → j ⌣ i

  -- ================================================================
  -- §3  INTERLEAVING, AND POINTWISE DISJOINTNESS.
  -- ================================================================

  data Ilv : Program → Program → Program → Type₀ where
    inil   : Ilv [] [] []
    ileft  : ∀ {i p q r} → Ilv p q r → Ilv (i ∷ p) q (i ∷ r)
    iright : ∀ {i p q r} → Ilv p q r → Ilv p (i ∷ q) (i ∷ r)

  -- a CONCATENATION is an interleaving, so `asmFib` has at least the
  -- splittings `strFib` had
  ilv-app : (p q : Program) → Ilv p q (p ++ q)
  ilv-app []      []      = inil
  ilv-app []      (j ∷ q) = iright (ilv-app [] q)
  ilv-app (i ∷ p) q       = ileft (ilv-app p q)

  -- PRIMITIVE (phase 1): `Unit`/`×`-valued, so proofs are `tt`-shaped
  -- and never block a reduction.
  All⌣ : Instr → Program → Type₀
  All⌣ i []      = Unit
  All⌣ i (j ∷ q) = (j ⌣ i) × All⌣ i q

  Disj : Program → Program → Type₀
  Disj p []      = Unit
  Disj p (j ∷ q) = All⌣ j p × Disj p q

  disj-tl : {i : Instr} {p q : Program} → Disj (i ∷ p) q → Disj p q
  disj-tl {q = []}    dj = tt
  disj-tl {q = j ∷ q} dj = dj .fst .snd , disj-tl {q = q} (dj .snd)

  -- ================================================================
  -- §4  THE PROMODEL.
  --
  -- `strFib` with `Split3` replaced by `Ilv` and `Disj` added.  `nilop`
  -- is untouched: the empty program is still the empty program.
  -- ================================================================

  IsNil : Program → Type₀
  IsNil []      = Unit
  IsNil (_ ∷ _) = ⊥

  AsmSplit : (o : MonOp) → Program → Type₀
  AsmSplit nilop r = IsNil r
  AsmSplit appop r = Σ[ p ∈ Program ] Σ[ q ∈ Program ] (Ilv p q r × Disj p q)

  AsmParts : (o : MonOp) (r : Program) → AsmSplit o r → MonAr o → Program
  AsmParts nilop r sp ()
  AsmParts appop r (p , q , _) = boolΠ {M = λ _ → Program} p q

  asmFib : Fibered monoidSig ℓ-zero ℓ-zero
  asmFib .carrier _ = Program
  asmFib .Split     = AsmSplit
  asmFib .parts     = AsmParts

  asmTheoryM : Theory ℓ-zero ℓ-zero ℓ-zero ℓ-zero ℓ-zero
  asmTheoryM = theory monoidSig asmFib

  -- ================================================================
  -- §5  THE HOMOMORPHISM, UNDER THE MEMORY MODEL.
  -- ================================================================

  module _ (⌣-sym : Symmetric) (⌣-comm : Commutes) where

    -- MOVING AN INSTRUCTION PAST A BLOCK.  The one place the memory
    -- model is spent, and it is spent once per instruction of `p`.
    commPast : (i : Instr) (p : Program) → All⌣ i p
             → (step i ⨟ sem p) ⊑ (sem p ⨟ step i)
    commPast i []      _  = ⊑-trans (⨟-unitR→ (step i)) (⨟-unitL← (step i))
    commPast i (j ∷ p) al =
      ⊑-trans (⨟-assoc← (step i) (step j) (sem p))
      (⊑-trans (⨟-mono (⌣-comm i j (⌣-sym j i (al .fst))) (⊑-refl (sem p)))
      (⊑-trans (⨟-assoc→ (step j) (step i) (sem p))
      (⊑-trans (⨟-mono (⊑-refl (step j)) (commPast i p (al .snd)))
               (⨟-assoc← (step j) (sem p) (step i)))))

    -- THE MONOID HOMOMORPHISM, at the RELAXED splitting.  Compare
    -- `ISA.Program.homSplit3`: same statement, `Ilv` for `Split3`, and
    -- one extra clause where the head crosses the left block.
    ilv-sem : {p q r : Program} → Ilv p q r → Disj p q
            → sem r ⊑ (sem p ⨟ sem q)
    ilv-sem inil _ = ⨟-unitL← skip
    ilv-sem (ileft {i} {p} {q} {r} d) dj =
      ⊑-trans (⨟-mono (⊑-refl (step i)) (ilv-sem d (disj-tl {i = i} dj)))
              (⨟-assoc← (step i) (sem p) (sem q))
    ilv-sem (iright {i} {p} {q} {r} d) dj =
      ⊑-trans (⨟-mono (⊑-refl (step i)) (ilv-sem d (dj .snd)))
      (⊑-trans (⨟-assoc← (step i) (sem p) (sem q))
      (⊑-trans (⨟-mono (commPast i p (dj .fst)) (⊑-refl (sem q)))
               (⨟-assoc→ (sem p) (step i) (sem q))))

    -- ... and the unit, which the relaxation did not touch
    ilv-nil : (r : Program) → IsNil r → sem r ⊑ skip
    ilv-nil []      _  = ⊑-refl skip
    ilv-nil (i ∷ p) ()

    -- ================================================================
    -- §6  THE PASS.
    --
    -- `ISA.Pass.semPass` with `asmFib` in place of `PT.strFib`.  The
    -- fields are `ilv-sem` and `ilv-nil` verbatim, exactly as the rigid
    -- version's were `homSplit3` and `semNil`.
    -- ================================================================

    memOver : ReindexOver (idSigMor monoidSig) asmFib cmdFib
    memOver .homO _ p = sem p

    memPresO : (o : MonOp) → SplitPresAtOver memOver o
    memPresO appop .homSplitO r (p , q , d , dj) =
      sem p , sem q , ilv-sem d dj
    memPresO appop .homPartsO r (p , q , d , dj) =
      boolΠ {M = λ a → cmdFib .parts appop (sem r)
                         (sem p , sem q , ilv-sem d dj) a
                       Eq.≡ sem (AsmParts appop r (p , q , d , dj) a)}
            Eq.refl Eq.refl
    memPresO nilop .homSplitO r sp = lift (ilv-nil r sp)
    memPresO nilop .homPartsO r sp ()

    -- THE THEOREM.  The memory model costs `⌣-comm` and buys back every
    -- splitting a heap has.
    memPass : Pass asmTheoryM cmdTheory
    memPass .sigOf  = idSigMor monoidSig
    memPass .mapOf  = memOver
    memPass .presOf = memPresO
