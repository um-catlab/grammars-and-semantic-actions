{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE BINARY RELATION BETWEEN SOURCE TERMS AND TARGET EXPRESSIONS.

  `Compile.Relational.Refutation` proves that

      Simulates = (t v : Tm []) → t ⇓ₛ v → compileRust t ⇓ compileRust v

  is FALSE, and that the only thing wrong with it is the `≡` in its
  conclusion: the target's answer and the compilation of the source's
  answer are the same term up to a renaming of binders.  This file
  supplies the relation that replaces that `≡`.

  ------------------------------------------------------------------
  WHAT IT RELATES
  ------------------------------------------------------------------

  A source term `t : Tm u` has one free variable per `true` in `u`, and
  the ONLY thing `compileE` decides is what to call them.  So a target
  expression realises `t` RELATIVE TO A CHOICE OF NAMES, a
  `NameF = ℕ → Ident` sending a source position to the identifier
  standing for it:

      Rel ν t e     "e realises t, calling position p by the name ν p"

  `rlam` takes the binder's level as an ARBITRARY natural, which is
  exactly the freedom `compileRust`'s `≡` did not have: two expressions
  differing only in their binder levels are both related to the same
  source term.  `compileE` is then one SECTION,

      relCompile : (d : ℕ) (t : Tm u) → Rel (nameOf d) t (compileE d t)

  and its proof is three clauses with no equations, because
  `Codegen.nameOf` is written point-free in the depth: `nameOf (suc d)`
  reduces to `ext d (nameOf d)` with no argument supplied.  Pointfully
  this step needs `funExt` and then a `subst` at a family over a
  variable name assignment -- the documented trap.

  ------------------------------------------------------------------
  THE NON-SHADOWING PREMISE ON `rlam`, AND WHY IT IS THIS ONE
  ------------------------------------------------------------------

  `Eval.substE` resolves a variable BY NAME, so a binder can shadow an
  outer one carrying the same level.  A first attempt at this relation
  had no side condition on `rlam` at all, and was unsound: it would
  relate a source variable at an outer position to an occurrence that
  the target resolves to an INNER binder of the same name.

  The obvious repair -- demand the new level be fresh for the whole
  assignment -- is too strong, and MEASURABLY so.  `appLin appLin`
  evaluates to

      rClos 1 (rCall (rClos 0 (rClos 1 …)) (rVar (bnd 1)))

  in which level `1` occurs twice on one path.  Binder levels are
  simply not distinct after evaluation, and any relation that demands
  they be cannot describe the target's own answers.

  The premise carried here is the weakest one that is sound:

      (p : ℕ) → LiveAt p u → DifI (ν p) (bnd n)

  -- the new level differs from the name of every LIVE outer position.
  A shadowed level is fine as long as nothing still refers to it, which
  is precisely the situation above: the outer `rClos 1` is re-shadowed
  only inside a closed subexpression.  Restricting to live positions is
  not a convenience; `LiveAt` is what makes the premise satisfiable.

  It also pays for itself downstream.  `Relational.Subst.relSubst`
  needs "no binder of the body carries the substituted name", and the
  substituted position is LIVE by `Mark true`, so that hypothesis is
  now DERIVED from the relation rather than assumed alongside it.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1 throughout.  `Dif`, `DifI`, `Lt`, `Below`, `LiveAt`, `dlift`
  and `del` are PRIMITIVE and marked; all are `Unit`/`⊥`-valued in the
  style of `Syntax.Same`, so their proofs never block a `refl`.
-}
open import Cubical.Foundations.Prelude

module Compile.Relational.Base where

open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import Compile.LinToRust.Codegen
import Compile.Semantics.CBV as S
import TheoryGrammar.Instances.LinLam.Syntax as L

-- ==================================================================
-- §1  DISTINCTNESS OF NAMES, AS DATA THAT COMPUTES.
-- ==================================================================

-- PRIMITIVE (phase 1): the complement of `Syntax.Same`
Dif : ℕ → ℕ → Type₀
Dif zero    zero    = ⊥
Dif zero    (suc _) = Unit
Dif (suc _) zero    = Unit
Dif (suc m) (suc n) = Dif m n

-- PRIMITIVE (phase 1)
DifI : Ident → Ident → Type₀
DifI (bnd m) (bnd n) = Dif m n
DifI (fre m) (fre n) = Dif m n
DifI (bnd _) (fre _) = Unit
DifI (fre _) (bnd _) = Unit

-- PRIMITIVE (phase 1): and its positive counterpart, for the branch of
-- `substE` that STOPS
SameI : Ident → Ident → Type₀
SameI (bnd m) (bnd n) = m Eq.≡ n
SameI (fre m) (fre n) = m Eq.≡ n
SameI (bnd _) (fre _) = ⊥
SameI (fre _) (bnd _) = ⊥

dif-sym : (m n : ℕ) → Dif m n → Dif n m
dif-sym zero    zero    d = d
dif-sym zero    (suc n) d = tt
dif-sym (suc m) zero    d = tt
dif-sym (suc m) (suc n) d = dif-sym m n d

difI-sym : (x y : Ident) → DifI x y → DifI y x
difI-sym (bnd m) (bnd n) d = dif-sym m n d
difI-sym (fre m) (fre n) d = dif-sym m n d
difI-sym (bnd _) (fre _) d = tt
difI-sym (fre _) (bnd _) d = tt

dif-suc : (n : ℕ) → Dif n (suc n)
dif-suc zero    = tt
dif-suc (suc n) = dif-suc n

-- ------------------------------------------------------------------
-- the boolean decision, and its reflection in both directions.  This
-- is what lets a proof CASE on whether `substE` stops at a binder.
-- ------------------------------------------------------------------

eqℕ-dif : (m n : ℕ) → Dif m n → eqℕ m n Eq.≡ false
eqℕ-dif zero    zero    d = E.rec d
eqℕ-dif zero    (suc n) d = Eq.refl
eqℕ-dif (suc m) zero    d = Eq.refl
eqℕ-dif (suc m) (suc n) d = eqℕ-dif m n d

eqIdent-dif : (x y : Ident) → DifI x y → eqIdent x y Eq.≡ false
eqIdent-dif (bnd m) (bnd n) d = eqℕ-dif m n d
eqIdent-dif (fre m) (fre n) d = eqℕ-dif m n d
eqIdent-dif (bnd _) (fre _) d = Eq.refl
eqIdent-dif (fre _) (bnd _) d = Eq.refl

eqℕ-refl : (n : ℕ) → eqℕ n n Eq.≡ true
eqℕ-refl zero    = Eq.refl
eqℕ-refl (suc n) = eqℕ-refl n

eqIdent-refl : (x : Ident) → eqIdent x x Eq.≡ true
eqIdent-refl (bnd n) = eqℕ-refl n
eqIdent-refl (fre n) = eqℕ-refl n

-- reflection: a `false` decision IS a distinctness, and a `true` one
-- IS an equality
eqℕ-false : (m n : ℕ) → eqℕ m n Eq.≡ false → Dif m n
eqℕ-false zero    zero    e = Eq.transport (λ z → BF z) e tt
  where BF : Bool → Type₀
        BF true  = Unit
        BF false = ⊥
eqℕ-false zero    (suc n) e = tt
eqℕ-false (suc m) zero    e = tt
eqℕ-false (suc m) (suc n) e = eqℕ-false m n e

eqIdent-false : (x y : Ident) → eqIdent x y Eq.≡ false → DifI x y
eqIdent-false (bnd m) (bnd n) e = eqℕ-false m n e
eqIdent-false (fre m) (fre n) e = eqℕ-false m n e
eqIdent-false (bnd _) (fre _) e = tt
eqIdent-false (fre _) (bnd _) e = tt

eqℕ-true : (m n : ℕ) → eqℕ m n Eq.≡ true → m Eq.≡ n
eqℕ-true zero    zero    e = Eq.refl
eqℕ-true zero    (suc n) e = E.rec (Eq.transport BT e tt)
  where BT : Bool → Type₀
        BT true  = ⊥
        BT false = Unit
eqℕ-true (suc m) zero    e = E.rec (Eq.transport BT e tt)
  where BT : Bool → Type₀
        BT true  = ⊥
        BT false = Unit
eqℕ-true (suc m) (suc n) e = Eq.ap suc (eqℕ-true m n e)

eqIdent-true : (x y : Ident) → eqIdent x y Eq.≡ true → SameI x y
eqIdent-true (bnd m) (bnd n) e = eqℕ-true m n e
eqIdent-true (fre m) (fre n) e = eqℕ-true m n e
eqIdent-true (bnd _) (fre _) e = E.rec (Eq.transport BT e tt)
  where BT : Bool → Type₀
        BT true  = ⊥
        BT false = Unit
eqIdent-true (fre _) (bnd _) e = E.rec (Eq.transport BT e tt)
  where BT : Bool → Type₀
        BT true  = ⊥
        BT false = Unit

-- ==================================================================
-- §2  LIVENESS OF A POSITION.
--
-- PRIMITIVE (phase 1).  `LiveAt p u` is "slot `p` of `u` is `true`" --
-- the positions a term at usage `u` may actually mention.
-- ==================================================================

LiveAt : ℕ → L.Usage → Type₀
LiveAt _       []          = ⊥
LiveAt zero    (true  ∷ _) = Unit
LiveAt zero    (false ∷ _) = ⊥
LiveAt (suc p) (_ ∷ u)     = LiveAt p u

-- ==================================================================
-- §3  THE RELATION.
--
-- `rapp` gives the two premises the SAME assignment.  That is not a
-- simplification: `Use⊎ u₁ u₂ u` preserves the length of the usage, so
-- position `p` of a premise IS position `p` of the conclusion, and
-- `soloAt` counts every slot, live or dead.  It is the same reason
-- `Codegen.names` threads one offset through both sides of a split.
-- ==================================================================

data Rel : {u : L.Usage} → NameF → L.Tm u → RExpr → Type₀ where

  rvar : ∀ {u} {ν : NameF} (s : L.Solo u)
       → Rel {u} ν (L.tvar s) (rVar (ν (soloAt 0 u s)))

  rapp : ∀ {u₁ u₂ u} {ν : NameF} {sp : L.Use⊎ u₁ u₂ u}
         {f : L.Tm u₁} {a : L.Tm u₂} {f' a' : RExpr}
       → Rel ν f f' → Rel ν a a'
       → Rel ν (L.tapp sp f a) (rCall f' a')

  rlam : ∀ {u} {ν : NameF} {b : L.Tm (true ∷ u)} {b' : RExpr} (n : ℕ)
       → ((p : ℕ) → LiveAt p u → DifI (ν p) (bnd n))   -- NON-SHADOWING
       → Rel (ext n ν) b b'
       → Rel ν (L.tlam b) (rClos n b')

-- ==================================================================
-- §4  `nameOf` MEETS THE PREMISE, VIA A BOUND ON THE LEVELS IT EMITS.
--
-- `Below d x` is "`x` is a binder at a level `< d`, or a free
-- variable".  It makes the freshness of the NEXT binder an induction:
-- the level about to be introduced is `d`, and every level already in
-- play is `< d`.
-- ==================================================================

-- PRIMITIVE (phase 1)
Lt : ℕ → ℕ → Type₀
Lt _       zero    = ⊥
Lt zero    (suc _) = Unit
Lt (suc m) (suc n) = Lt m n

lt-dif : (m n : ℕ) → Lt m n → Dif m n
lt-dif m       zero    l = E.rec l
lt-dif zero    (suc n) l = tt
lt-dif (suc m) (suc n) l = lt-dif m n l

lt-suc : (m n : ℕ) → Lt m n → Lt m (suc n)
lt-suc m       zero    l = E.rec l
lt-suc zero    (suc n) l = tt
lt-suc (suc m) (suc n) l = lt-suc m n l

lt-self : (n : ℕ) → Lt n (suc n)
lt-self zero    = tt
lt-self (suc n) = lt-self n

Below : ℕ → Ident → Type₀
Below d (bnd j) = Lt j d
Below d (fre _) = Unit

below-suc : (d : ℕ) (x : Ident) → Below d x → Below (suc d) x
below-suc d (bnd j) b = lt-suc j d b
below-suc d (fre _) b = tt

nameOf-below : (d p : ℕ) → Below d (nameOf d p)
nameOf-below zero    p       = tt
nameOf-below (suc d) zero    = lt-self d
nameOf-below (suc d) (suc p) = below-suc d _ (nameOf-below d p)

-- the premise `rlam` wants, at `compileE`'s own assignment
freshB-nameOf : (d p : ℕ) → DifI (nameOf d p) (bnd d)
freshB-nameOf d p with nameOf d p | nameOf-below d p
... | bnd j | b = lt-dif j d b
... | fre _ | b = tt

-- ==================================================================
-- §5  `compileE` IS A SECTION.
-- ==================================================================

relCompile : ∀ {u} (d : ℕ) (t : L.Tm u) → Rel (nameOf d) t (compileE d t)
relCompile d (L.tvar s)      = rvar s
relCompile d (L.tapp sp f a) = rapp (relCompile d f) (relCompile d a)
relCompile d (L.tlam b)      =
  rlam d (λ p _ → freshB-nameOf d p) (relCompile (suc d) b)

relCompileRust : ∀ {u} (t : L.Tm u) → Rel (nameOf 0) t (compileRust t)
relCompileRust = relCompile 0

-- ==================================================================
-- §6  DELETION OF A POSITION, AND ITS LAWS.
--
-- `Opt.subS` CONTRACTS the usage: the substituted variable's slot
-- disappears.  `del k` is that contraction on assignments; it
-- reindexes along `dlift k`, which is injective and MISSES `k`.
-- PRIMITIVE (phase 1).
-- ==================================================================

del : ℕ → NameF → NameF
del zero    ν = tl ν
del (suc k) ν = extI (ν zero) (del k (tl ν))

-- crossing a binder commutes with deleting a position further out ...
del-ext : (k n : ℕ) (ν : NameF) → del (suc k) (ext n ν) ≡ ext n (del k ν)
del-ext k n ν = refl

-- ... and deleting the position a binder just introduced undoes it
del-ext₀ : (n : ℕ) (ν : NameF) → del zero (ext n ν) ≡ ν
del-ext₀ n ν = refl

del-nameOf : (d : ℕ) → del zero (nameOf (suc d)) ≡ nameOf d
del-nameOf d = refl

-- PRIMITIVE (phase 1)
dlift : ℕ → ℕ → ℕ
dlift zero    p       = suc p
dlift (suc k) zero    = zero
dlift (suc k) (suc p) = suc (dlift k p)

del-as : (k : ℕ) (ν : NameF) (p : ℕ) → del k ν p Eq.≡ ν (dlift k p)
del-as zero    ν p       = Eq.refl
del-as (suc k) ν zero    = Eq.refl
del-as (suc k) ν (suc p) = del-as k (tl ν) p

-- THE KEY FACT.  `k` is not in the image of `dlift k`.
dlift-miss : (k p : ℕ) → Dif (dlift k p) k
dlift-miss zero    p       = tt
dlift-miss (suc k) zero    = tt
dlift-miss (suc k) (suc p) = dlift-miss k p

-- ==================================================================
-- §7  OBSERVATION.  THE COUNTEREXAMPLE IS NOT ONE ANY MORE.
--
-- `Refutation`'s witness `(λf. λx. f x) (λy. y)` has a source value
-- whose compilation and a target answer that are DISTINCT expressions.
-- Both are `Rel (nameOf 0)`-related to that one source value, which is
-- precisely what it means for the repair to be a repair.
-- ==================================================================

bigT : L.Tm []
bigT = L.tapp L.unil appLin L.idLin

bigV : L.Tm []
bigV = S.evalV bigT

_ : compileRust bigV
  ≡ rClos 0 (rCall (rClos 1 (rVar (bnd 1))) (rVar (bnd 0)))
_ = refl

relSrc : Rel (nameOf 0) bigV (compileRust bigV)
relSrc = relCompileRust bigV

tgtV : RExpr
tgtV = rClos 1 (rCall (rClos 0 (rVar (bnd 0))) (rVar (bnd 1)))

_ : valOf (evalRust 20 (compileRust bigT)) ≡ just tgtV
_ = refl

-- ... and it is related to `bigV` too.  This is the theorem the `≡`
-- could not state: `rlam` chose the level `1` where `compileRust` was
-- forced to choose `0`, and the relation does not care.  Both
-- non-shadowing premises are discharged by `λ p ()` -- there are no
-- live outer positions to shadow, the terms being closed.
relTgt : Rel (nameOf 0) bigV tgtV
relTgt = rlam 1 (λ { zero () ; (suc p) () })
           (rapp (rlam 0 (λ { zero () ; (suc p) () }) (rvar _)) (rvar _))
