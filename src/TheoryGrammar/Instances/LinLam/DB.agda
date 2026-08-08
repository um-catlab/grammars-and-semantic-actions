{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- DE BRUIJN TERMS AS A `Fibered` -- the theory the elaborator lands IN. -}
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

-- The dependent eliminator for a `Bool` arity.

-- PRIMITIVE (phase 1)
-- `boolΠ` (Bool's dependent eliminator, = the binary arity's) now
-- comes from `TheoryGrammar.Theories.Monoid`, where the arity is.

-- THE CARRIER. Two sorts, as in `λSig`: a NAME is a de Bruijn index
-- together with the scope it indexes, a TERM is a de Bruijn tree together
-- with its scope.

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

-- SPLITTINGS.  As in `Lambda/Fibered`, each family has exactly ONE
-- constructor -- unique readability of the de Bruijn AST -- which is
-- what makes `parts` a projection rather than an inversion lemma.

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

-- `In` COLLAPSES.  Over `λFib` this is `Wellscoped.In`, a ⊕-chain of
-- representables built from the scope; here it is the terminal grammar,
-- ON THE NOSE, because the scope is already in the index.

InDB : NmG
InDB = ⊤G

in-trivial : InDB ≡ ⊤G
in-trivial = refl

-- THE THREE TENSORS, and their intro/elim.  Compare `Lambda/Base`: the
-- ONLY difference is that `LamG`'s name argument has nothing to say.

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

-- THE GRADING. `deg` is the size of the tree; a name has degree 0.

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

-- THE DESCRIPTION. Three alternatives, one per operation, and NO `⊕e Name`
-- -- compare `Wellscoped.ScopedF`, whose `tLam` branch must guess the
-- bound name and pin it with a representable.

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

-- Guardedness. Every slot is proper, so every recursive position is
-- discharged by `slotProper` with `tt`; there is no case analysis on which
-- sibling is nonempty, which is the resource-theory complication that
-- syntax simply does not have.
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

-- THE CONTAINER ENCODING, RESPELLED IN THE CONNECTIVES.  Exactly
-- `Wellscoped.⟦Sc⟧`'s job: a change of notation, never a proof.  No
-- splitting is opened -- `sp` passes through abstractly.

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

-- THE DECOMPOSITION AXIOM: `⊤` carries a coalgebra for `DBF`.  This is
-- `bagCase` / `charCase` for de Bruijn terms, and it is the LAST place
-- in the file that matches the carrier.

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

-- `Scoped` IS TRIVIAL, as a theorem. `DBAll` is the de Bruijn analogue of
-- `Wellscoped.Scoped`: the μ of the description.

DBAll : TmG
DBAll = μᴳ DBF tt

dbAll : ⊤G ⊢ DBAll
dbAll = scanμ dbGuarded dbCase tt

-- ... and the unrolling rules, so downstream never touches `sup`.
db-unroll : DBAll ⊢ DBStep DBAll
db-unroll = ⟦DB⟧ {M = μ DBF} ∘g unrollg DBF tt

db-roll : DBStep DBAll ⊢ DBAll
db-roll = rollg DBF tt ∘g ⟦DB⟧⁻ {M = μ DBF}
