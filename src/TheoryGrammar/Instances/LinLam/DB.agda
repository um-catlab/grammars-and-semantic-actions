{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  DE BRUIJN TERMS AS A PROMODEL -- the theory the elaborator lands IN.

  `Lambda/DeBruijn.agda` folds a well-scoped named term into `DB n`, a
  bare metalanguage family.  After that fold you are OUTSIDE the
  calculus: `DB n` carries no `Split`, so nothing downstream may use
  `⊗ˢ`, `⌈⌉`, `μ`, `hyloC` or `⊸ᶠ` on it, and every later pass degenerates
  into an Agda function with its own hand-written correctness proof.
  That is the leak this file closes.  The cure is not to change the fold
  but to give its CODOMAIN a promodel structure OVER THE SAME SIGNATURE
  `λSig`, so that elaboration becomes a `Reindex λFib dbFib`
  (`Scope.agda`) instead of an exit.

  --------------------------------------------------------------------
  WHY THE CARRIER IS SCOPE-INDEXED, and not raw de Bruijn trees.

  Two carriers present themselves:

      untyped   carrier tm = DB           (dvar : ℕ    → DB)
      scoped    carrier tm = Σ[n] DBTm n  (dvar : Fin n → DBTm n)

  Take the second.  The reason is exactly the thing this exercise is
  meant to measure.  Over `λFib`, well-scopedness is a GRAMMAR:
  `Wellscoped` builds `In Γ : NmG` as a ⊕-chain of representables, and
  `Scoped Γ` as a `μ` with ONE NONTERMINAL PER SCOPE (`X = Scope`).
  Over the scoped de Bruijn carrier

      In  ≡  ⊤G                                          (definitionally)

  because a point of `carrier nm = Σ[n] Fin n` carries the scope it lives
  in, so "this variable is in scope" has no content left; and the
  nonterminal index collapses from `Scope` to `Unit`.  THAT is the honest
  sense in which `Scoped` becomes trivial: not that its proof got
  shorter, but that the whole FAMILY of nonterminals disappears, because
  the scope moved into the index of the carrier.  `dbAll : ⊤G ⊢ DBAll`
  below states it as a theorem, and it is the generic `scanμ` -- no
  induction is written here at all, only the decomposition axiom
  `dbCase`.

  With the untyped carrier neither happens: `In` would be `i < n`, a
  perfectly nontrivial grammar, and one nonterminal per scope size would
  still be wanted.  Untyped de Bruijn buys α-equivalence and nothing
  else; scoped de Bruijn buys α-equivalence AND scoping.

  --------------------------------------------------------------------
  THE SECOND THING THAT BECOMES FREE: α-EQUIVALENCE, as an absence.

  Over `λFib`,

      parts lamOp (lam n t) (mkLam n t) true  =  n

  -- the binder's NAME is a genuine degree of freedom in the splitting,
  which is why `Wellscoped`'s description has to GUESS it (`⊕e Name λ n →
  …`) and then pin the guess with the representable `⌜ ⌈ n ⌉ ⌝`.  Over
  `dbFib`,

      parts lamOp (n , dlam b) (mkDLam b) true  =  (suc n , fzero)

  is FORCED: there is exactly one thing a de Bruijn binder can put in its
  name slot, namely index 0 of the extended scope.  So the `⊕e Name`
  disappears from the description (`DBAlt tL` below has no guess), and
  α-equivalence is not a quotient anybody imposes -- it is the absence of
  a choice in `parts`.  This is the promodel-level reading of "de Bruijn
  terms are α-equivalence classes", and it is visible in the SIGNATURE of
  `DBParts`, not in a theorem.

  --------------------------------------------------------------------
  WHAT DOES NOT BECOME FREE.  Reported here because the honest answer
  matters more than the positive one; the details are in `Scope.agda`.

  The question asked was whether any operation NEWLY satisfies
  `SplitPresAt` over this theory.  The answer is NO, and the reason is
  worth stating precisely rather than apologised for: `SplitPresAt` is a
  property of a MAP, not of a theory, so a new promodel cannot make it
  hold -- it can only change which map one is asking about.  For the
  elaboration `λFib → dbFib` the tally is

      varOp   PRESERVED and REFLECTED
      appOp   PRESERVED and REFLECTED
      lamOp   NEITHER  (`¬presLam`, `¬reflLam` in `Scope.agda`)

  and `lamOp` fails twice over -- the name slot moves from `n` to
  `fzero`, and the scope moves from `n` to `suc n`.  Compare
  `Lambda/Passes/Inline`, where substitution preserves `appOp`/`lamOp`
  and fails at `varOp`, and where REFLECTION additionally fails at
  `appOp`.  So the two passes fail in different places, and in each case
  the obstruction is exactly the operation the pass rewrites.  That
  per-operation localisation is the whole content of `CarrierMap`'s
  design, and it is what this instance confirms rather than what it
  improves on.

  What DOES improve is the ADDITIVE side, and it improves because of the
  carrier, not because of any preservation property: see
  `Scope.elabScoped`, where a theorem about de Bruijn terms becomes a
  theorem about the elaboration of an arbitrary raw term by `pullTerm`
  alone.

  --------------------------------------------------------------------
  PRIMITIVE (phase 1), i.e. everything below that matches the carrier:
  `IsDVar`, `IsDApp`, `IsDLam`, `DBSplit`, `DBParts`, `boolΠ`, `dbSize`,
  the grading's four fields, the six intro/elim rules, `⟦DB⟧`/`⟦DB⟧⁻`,
  and `dbCase`.  Everything after `dbCase` is composition.
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.LinLam.DB where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as E using (⊥)
open import Cubical.Data.FinData.Base using (Fin)
  renaming (zero to fzero; suc to fsuc)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded
open import TheoryGrammar.Decidable

open import TheoryGrammar.Instances.Lambda.Signature public

-- ==================================================================
-- The dependent eliminator for a `Bool` arity.  ONE place where
-- `true`/`false` are matched over a slot family, exactly as in
-- `Heap/Base` and `LinLam/Context`; extended lambdas over an arity are
-- identified NOMINALLY in Agda, so two written in different files never
-- reduce against each other.
-- ==================================================================

-- PRIMITIVE (phase 1)
boolΠ : ∀ {ℓ} {M : Bool → Type ℓ} → M true → M false → (b : Bool) → M b
boolΠ t f true  = t
boolΠ t f false = f

-- ==================================================================
-- THE CARRIER.  Two sorts, as in `λSig`: a NAME is a de Bruijn index
-- together with the scope it indexes, a TERM is a de Bruijn tree
-- together with its scope.  Both are Σ-types over ℕ, so the sort
-- structure of `λSig` survives unchanged and a `Reindex` is available.
-- ==================================================================

data DBTm : ℕ → Type₀ where
  dvar : ∀ {n} → Fin n → DBTm n
  dapp : ∀ {n} → DBTm n → DBTm n → DBTm n
  dlam : ∀ {n} → DBTm (suc n) → DBTm n

Scope• : Type₀
Scope• = Σ[ n ∈ ℕ ] Fin n

Term• : Type₀
Term• = Σ[ n ∈ ℕ ] DBTm n

DBCar : LSort → Type₀
DBCar nm = Scope•
DBCar tm = Term•

-- ==================================================================
-- SPLITTINGS.  As in `Lambda/Fibered`, each family has exactly ONE
-- constructor -- unique readability of the de Bruijn AST -- which is
-- what makes `parts` a projection rather than an inversion lemma.
-- ==================================================================

data IsDVar {n : ℕ} : DBTm n → Type₀ where      -- PRIMITIVE
  mkDVar : (i : Fin n) → IsDVar (dvar i)

data IsDApp {n : ℕ} : DBTm n → Type₀ where      -- PRIMITIVE
  mkDApp : (u v : DBTm n) → IsDApp (dapp u v)

data IsDLam {n : ℕ} : DBTm n → Type₀ where      -- PRIMITIVE
  mkDLam : (b : DBTm (suc n)) → IsDLam (dlam b)

DBSplit : (o : LOp) → Term• → Type₀             -- PRIMITIVE
DBSplit varOp (n , t) = IsDVar t
DBSplit appOp (n , t) = IsDApp t
DBSplit lamOp (n , t) = IsDLam t

-- THE ONE LINE THIS FILE EXISTS FOR is the `lamOp`/`true` clause: the
-- name slot is `(suc n , fzero)`, with nothing to choose.
DBParts : (o : LOp) (m : Term•) → DBSplit o m
        → (a : LAr o) → DBCar (LSortOf o a)     -- PRIMITIVE
DBParts varOp (n , _) (mkDVar i)   _ = n , i
DBParts appOp (n , _) (mkDApp u v)   =
  boolΠ {M = λ _ → Term•} (n , u) (n , v)
DBParts lamOp (n , _) (mkDLam b)     =
  boolΠ {M = λ a → DBCar (LSortOf lamOp a)} (suc n , fzero) (suc n , b)

dbFib : Fibered λSig ℓ-zero ℓ-zero
dbFib .carrier = DBCar
dbFib .Split   = DBSplit
dbFib .parts   = DBParts

-- the connectives, the additive rules, the semantic actions and the
-- generic internal theory of decisions, in one `open`
open DecFib dbFib public

NmG : Type₁
NmG = TheoryTy ℓ-zero nm

TmG : Type₁
TmG = TheoryTy ℓ-zero tm

-- ==================================================================
-- `In` COLLAPSES.  Over `λFib` this is `Wellscoped.In`, a ⊕-chain of
-- representables built from the scope; here it is the terminal grammar,
-- ON THE NOSE, because the scope is already in the index.
-- ==================================================================

InDB : NmG
InDB = ⊤G

in-trivial : InDB ≡ ⊤G
in-trivial = refl

-- ==================================================================
-- THE THREE TENSORS, and their intro/elim.  Compare `Lambda/Base`: the
-- ONLY difference is that `LamG`'s name argument has nothing to say.
-- ==================================================================

VarG : NmG → TmG
VarG P = ⊗ˢ varOp (λ _ → P)

AppG : TmG → TmG → TmG
AppG A B = ⊗ˢ appOp (boolΠ {M = λ _ → TmG} A B)

LamG : NmG → TmG → TmG
LamG P A = ⊗ˢ lamOp (boolΠ {M = λ a → TheoryTy ℓ-zero (LSortOf lamOp a)} P A)

-- PRIMITIVES: intro and elim of the three tensors.
dvar-mk : {P : NmG} {n : ℕ} {i : Fin n} → P (n , i) → VarG P (n , dvar i)
dvar-mk {n = n} {i} p = mkDVar i , λ _ → p

dapp-mk : {A B : TmG} {n : ℕ} {u v : DBTm n}
        → A (n , u) → B (n , v) → AppG A B (n , dapp u v)
dapp-mk {A = A} {B} {n} {u} {v} a b =
  mkDApp u v
  , boolΠ {M = λ c → boolΠ {M = λ _ → TmG} A B c
                       (DBParts appOp (n , dapp u v) (mkDApp u v) c)} a b

dlam-mk : {P : NmG} {A : TmG} {n : ℕ} {b : DBTm (suc n)}
        → P (suc n , fzero) → A (suc n , b) → LamG P A (n , dlam b)
dlam-mk {P = P} {A} {n} {b} p t =
  mkDLam b
  , boolΠ {M = λ c → boolΠ {M = λ a → TheoryTy ℓ-zero (LSortOf lamOp a)} P A c
                       (DBParts lamOp (n , dlam b) (mkDLam b) c)} p t

dvar-elim : {P : NmG} {C : TmG}
          → (∀ n (i : Fin n) → P (n , i) → C (n , dvar i)) → VarG P ⊢ C
dvar-elim f (n , _) (mkDVar i , h) = f n i (h tt)

dapp-elim : {A B C : TmG}
          → (∀ n (u v : DBTm n) → A (n , u) → B (n , v) → C (n , dapp u v))
          → AppG A B ⊢ C
dapp-elim f (n , _) (mkDApp u v , h) = f n u v (h true) (h false)

dlam-elim : {P : NmG} {A : TmG} {C : TmG}
          → (∀ n (b : DBTm (suc n)) → P (suc n , fzero) → A (suc n , b)
             → C (n , dlam b))
          → LamG P A ⊢ C
dlam-elim f (n , _) (mkDLam b , h) = f n b (h true) (h false)

-- ==================================================================
-- THE GRADING.  `deg` is the size of the tree; a name has degree 0.
-- EVERY slot is proper -- `Proper = Unit` -- and that is itself a
-- finding: over `linFib` properness had to be "the sibling owns a
-- variable", because a usage can split with an empty part, whereas a de
-- Bruijn subtree is ALWAYS strictly smaller than its parent.  Syntax is
-- the well-founded case; resources are not.
-- ==================================================================

dbSize : {n : ℕ} → DBTm n → ℕ                   -- PRIMITIVE
dbSize (dvar i)   = 1
dbSize (dapp u v) = suc (dbSize u + dbSize v)
dbSize (dlam b)   = suc (dbSize b)

dbDeg : (s : LSort) → DBCar s → ℕ
dbDeg nm _       = 0
dbDeg tm (n , t) = dbSize t

private
  leL : (a b : ℕ) → a ≤ a + b
  leL a b = b , +-comm b a

  leR : (a b : ℕ) → b ≤ a + b
  leR a b = a , refl

dbGrading : Grading dbFib
dbGrading .deg           = dbDeg
dbGrading .Proper o m sp a = Unit

dbGrading .deg≤ varOp (n , _) (mkDVar i)   _     = zero-≤
dbGrading .deg≤ appOp (n , _) (mkDApp u v) true  = ≤-suc (leL _ _)
dbGrading .deg≤ appOp (n , _) (mkDApp u v) false = ≤-suc (leR _ _)
dbGrading .deg≤ lamOp (n , _) (mkDLam b)   true  = zero-≤
dbGrading .deg≤ lamOp (n , _) (mkDLam b)   false = ≤-suc ≤-refl

dbGrading .deg< varOp (n , _) (mkDVar i)   _     _ = suc-≤-suc zero-≤
dbGrading .deg< appOp (n , _) (mkDApp u v) true  _ = suc-≤-suc (leL _ _)
dbGrading .deg< appOp (n , _) (mkDApp u v) false _ = suc-≤-suc (leR _ _)
dbGrading .deg< lamOp (n , _) (mkDLam b)   true  _ = suc-≤-suc zero-≤
dbGrading .deg< lamOp (n , _) (mkDLam b)   false _ = ≤-refl

dbGraded : GradedFib λSig ℓ-zero ℓ-zero
dbGraded = graded dbFib dbGrading

-- descriptions, guardedness, ▷/löb, the hylomorphism, and the
-- programs-out-of-⊤ interface
open Guard dbGraded ℓ-zero Unit (λ _ → tm) public

-- ==================================================================
-- THE DESCRIPTION.  Three alternatives, one per operation, and NO
-- `⊕e Name` -- compare `Wellscoped.ScopedF`, whose `tLam` branch must
-- guess the bound name and pin it with a representable.  The
-- nonterminal index is `Unit`, not `Scope`.
-- ==================================================================

data DBTag : Type₀ where
  tV tA tL : DBTag

-- the slot families, NAMED (an arity family is never an anonymous
-- lambda here, for the reason `boolΠ` exists)
DBVar : (a : LAr varOp) → Functor (LSortOf varOp a)
DBVar _ = ⌜ ⊤G {s = nm} ⌝

DBApp : (a : LAr appOp) → Functor (LSortOf appOp a)
DBApp _ = Var tt

DBLam : (a : LAr lamOp) → Functor (LSortOf lamOp a)
DBLam = boolΠ {M = λ a → Functor (LSortOf lamOp a)} ⌜ ⊤G {s = nm} ⌝ (Var tt)

DBAlt : DBTag → Functor tm
DBAlt tV = ⊗e varOp DBVar
DBAlt tA = ⊗e appOp DBApp
DBAlt tL = ⊗e lamOp DBLam

DBF : Unit → Functor tm
DBF _ = ⊕e DBTag DBAlt

-- Guardedness.  Every slot is proper, so every recursive position is
-- discharged by `slotProper` with `tt`; there is no case analysis on
-- which sibling is nonempty, which is the resource-theory complication
-- that syntax simply does not have.
private
  gV : Guarded (DBAlt tV)
  gV = ⊗-guard varOp DBVar λ m sp sh a ()

  gA : Guarded (DBAlt tA)
  gA = ⊗-guard appOp DBApp
         λ m sp sh a p → slotProper appOp m sp a (≤Var tt) tt (sh a) p

  gLstep : (m : Term•) (sp : DBSplit lamOp m)
           (sh : (a : LAr lamOp) → Sh (DBLam a) (DBParts lamOp m sp a))
           (a : LAr lamOp) (p : Pos (DBLam a) _ (sh a))
         → degIx (nx (DBLam a) _ (sh a) p) < dbDeg tm m
  gLstep m sp sh true  ()
  gLstep m sp sh false p =
    slotProper lamOp m sp false (≤Var tt) tt (sh false) p

  gL : Guarded (DBAlt tL)
  gL = ⊗-guard lamOp DBLam gLstep

dbGuarded : (x : Unit) → Guarded (DBF x)
dbGuarded tt = <⊕e DBTag DBAlt alt
  where
  alt : (t : DBTag) → Guarded (DBAlt t)
  alt tV = gV
  alt tA = gA
  alt tL = gL

-- ==================================================================
-- THE CONTAINER ENCODING, RESPELLED IN THE CONNECTIVES.  Exactly
-- `Wellscoped.⟦Sc⟧`'s job: a change of notation, never a proof.  No
-- splitting is opened -- `sp` passes through abstractly.
-- ==================================================================

DBStep : TmG → TmG
DBStep M = VarG ⊤G ⊕ (AppG M M ⊕ LamG ⊤G M)

module _ {M : Ix → Type₀} where

  private
    M' : TmG
    M' m = M (tt , m)

  -- PRIMITIVE (phase 1)
  ⟦DB⟧ : ⟦ DBF tt ⟧c M ⊢ DBStep M'
  ⟦DB⟧ m (tV , sp , sh) = inl (sp , λ a → lower (sh a))
  ⟦DB⟧ m (tA , sp , h)  =
    inr (inl (sp , boolΠ {M = λ c → boolΠ {M = λ _ → TmG} M' M' c
                                      (DBParts appOp m sp c)}
                         (h true) (h false)))
  ⟦DB⟧ m (tL , sp , h)  =
    inr (inr (sp , boolΠ {M = λ c → boolΠ {M = λ a → TheoryTy ℓ-zero
                                                       (LSortOf lamOp a)}
                                      (⊤G {s = nm}) M' c
                                      (DBParts lamOp m sp c)}
                         (lower (h true)) (h false)))

  -- PRIMITIVE (phase 1)
  ⟦DB⟧⁻ : DBStep M' ⊢ ⟦ DBF tt ⟧c M
  ⟦DB⟧⁻ m (inl (sp , h)) =
    tV , sp , λ a → lift {ℓ' = ℓ-zero} (h a)
  ⟦DB⟧⁻ m (inr (inl (sp , h))) =
    tA , sp , boolΠ {M = λ c → M (tt , DBParts appOp m sp c)} (h true) (h false)
  ⟦DB⟧⁻ m (inr (inr (sp , h))) =
    tL , sp , boolΠ {M = λ c → ⟦ DBLam c ⟧c M (DBParts lamOp m sp c)}
                    (lift (h true)) (h false)

-- ==================================================================
-- THE DECOMPOSITION AXIOM: `⊤` carries a coalgebra for `DBF`.  This is
-- `bagCase` / `charCase` for de Bruijn terms, and it is the LAST place
-- in the file that matches the carrier.
-- ==================================================================

TopFam : Fam
TopFam _ = ⊤ᴳ

private
  varSlots : (n : ℕ) (i : Fin n) (a : LAr varOp)
           → ⟦ DBVar a ⟧c ⌞ TopFam ⌟
               (DBParts varOp (n , dvar i) (mkDVar i) a)
  varSlots n i _ = lift tt

  appSlots : (n : ℕ) (u v : DBTm n) (a : LAr appOp)
           → ⟦ DBApp a ⟧c ⌞ TopFam ⌟
               (DBParts appOp (n , dapp u v) (mkDApp u v) a)
  appSlots n u v true  = tt*
  appSlots n u v false = tt*

  lamSlots : (n : ℕ) (b : DBTm (suc n)) (a : LAr lamOp)
           → ⟦ DBLam a ⟧c ⌞ TopFam ⌟
               (DBParts lamOp (n , dlam b) (mkDLam b) a)
  lamSlots n b true  = lift tt
  lamSlots n b false = tt*

-- PRIMITIVE (phase 1)
dbCase : Scanner DBF
dbCase tt (n , dvar i)   _ = tV , mkDVar i   , varSlots n i
dbCase tt (n , dapp u v) _ = tA , mkDApp u v , appSlots n u v
dbCase tt (n , dlam b)   _ = tL , mkDLam b   , lamSlots n b

-- ==================================================================
-- `Scoped` IS TRIVIAL, as a theorem.
--
-- `DBAll` is the de Bruijn analogue of `Wellscoped.Scoped`: the μ of the
-- description.  Over `λFib` it is a genuine subgrammar of `Raw` and
-- `scoped?` (Lambda/Passes/Decide) has to DECIDE it.  Here it is
-- inhabited at every point of the carrier, and the proof is the generic
-- `scanμ` applied to the decomposition axiom -- no recursion is written,
-- the termination certificate is `dbGuarded`.
--
-- Read the other way round: `⊤G ⊢ DBAll` says the scope discipline is
-- no longer a property to check but a fact about the carrier, which is
-- what "it is in the index now" means.
-- ==================================================================

DBAll : TmG
DBAll = μᴳ DBF tt

dbAll : ⊤G ⊢ DBAll
dbAll = scanμ dbGuarded dbCase tt

-- ... and the unrolling rules, so downstream never touches `sup`.
db-unroll : DBAll ⊢ DBStep DBAll
db-unroll = ⟦DB⟧ {M = μ DBF} ∘g toCg
  where
  toCg : DBAll ⊢ ⟦ DBF tt ⟧c (μ DBF)
  toCg m t = toC (DBF tt) m (μ-coalg DBF tt m t)

db-roll : DBStep DBAll ⊢ DBAll
db-roll m s = μ-alg DBF tt m (fromC (DBF tt) m (⟦DB⟧⁻ {M = μ DBF} m s))
