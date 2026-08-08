{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE FIRST-ORDER LINEAR IR, WITH NUMBERS.

  `Compile/ClosureConv/IR.agda` with two constructors added and one
  constructor added to `Val`.  Everything that does NOT mention a value
  is imported from there rather than repeated:

      Cap, cnil/cdead/clive, capWkD, idCap    the capture discipline
      slotOf, zeros, zerosEmpty, zsplitL      the slot arithmetic
      nothing≢just, just-inj                  the two `Maybe` facts

  so the only forked definitions are the ones whose type contains `Val`
  or `IR`.  That is the honest measure of what a base type costs: the
  linearity machinery is untouched, because a literal consumes nothing
  and a primitive splits, and neither is a new kind of scoping.

  ------------------------------------------------------------------
  A VALUE IS NO LONGER "A CLOSURE AND NOTHING ELSE"
  ------------------------------------------------------------------

  That sentence is `ClosureConv/IR.agda` §4, and it is what made
  `Correct.valuesCollapse` true.  Here

      data Val = clos ℕ (List Val) | num ℕ

  and the observation separates values again: `obsN incApp` is
  `just (num 42)` and `obsN inc` is `just (clos 0 [])`.

  WHAT THE MACHINE DOES WITH A MISMATCH.  `iapp` on a `num`, or `iadd`
  on a `clos`, is a term this IR admits and no type rules out -- the
  source is untyped.  Both answer `nothing`, uniformly with running out
  of fuel.  That is a deliberate choice and it is the one place the ARM
  backend does NOT follow the model: on the machine a value is a heap
  record with no tag, so `iadd` on a closure adds its code address.
  `Compile/LinNum/ARM.agda` §9 says so explicitly and pins the fragment
  where the two do agree.

  PHASE.  Phase 1: the definition of a machine.
-}
open import Cubical.Foundations.Prelude

module Compile.LinNum.IR where

open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.List using (List; []; _∷_; _++_; length)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

import TheoryGrammar.Instances.LinLam.Syntax as L

-- everything that does not mention a value
open import Compile.ClosureConv.IR
  using ( Cap; cnil; cdead; clive; capWkD; idCap
        ; slotOf; slotOf-shift; zeros; zerosEmpty; zsplitL
        ; nothing≢just; just-inj )
  public

-- ==================================================================
-- §1  THE IR.  FIVE constructors, still none of them a binder.
-- ==================================================================

data IR : L.Usage → Type₀ where
  ivar  : ∀ {u} → L.Solo u → IR u
  iapp  : ∀ {u₁ u₂ u} → L.Use⊎ u₁ u₂ u → IR u₁ → IR u₂ → IR u
  iclos : ∀ {sh u} → ℕ → Cap sh u → IR u
  ilit  : ∀ {u} → L.Empty u → ℕ → IR u
  iadd  : ∀ {u₁ u₂ u} → L.Use⊎ u₁ u₂ u → IR u₁ → IR u₂ → IR u

Blk : Type₀
Blk = Σ[ sh ∈ L.Usage ] IR (true ∷ sh)

Table : Type₀
Table = List Blk

Prog : Type₀
Prog = Table × IR []

-- ==================================================================
-- §2  RUNTIME VALUES.  Two shapes now.
-- ==================================================================

data Val : Type₀ where
  clos : ℕ → List Val → Val
  num  : ℕ → Val

junk : Val
junk = clos 0 []

-- THE OBSERVABLE THIS FILE EXISTS FOR: the number a program computed,
-- or `nothing` if it did not compute one.
numOf : Maybe Val → Maybe ℕ
numOf nothing            = nothing
numOf (just (clos _ _))  = nothing
numOf (just (num n))     = just n

Frame : Type₀
Frame = ℕ → Val

emptyF : Frame
emptyF _ = junk

extF : Val → Frame → Frame
extF v σ zero    = v
extF v σ (suc p) = σ p

capVals : ∀ {sh u} → Frame → Cap sh u → List Val
capVals σ (cnil _)                  = []
capVals σ (cdead c)                 = capVals σ c
capVals σ (clive {u₁ = u₁} sp so c) = σ (slotOf 0 u₁ so) ∷ capVals σ c

spread : L.Usage → List Val → Frame
spread []           vs       p       = junk
spread (false ∷ sh) vs       zero    = junk
spread (false ∷ sh) vs       (suc p) = spread sh vs p
spread (true  ∷ sh) []       p       = junk
spread (true  ∷ sh) (v ∷ vs) zero    = v
spread (true  ∷ sh) (v ∷ vs) (suc p) = spread sh vs p

callFrame : L.Usage → List Val → Val → Frame
callFrame sh vs va = extF va (spread sh vs)

-- ==================================================================
-- §3  THE CODE TABLE.
-- ==================================================================

data At : Table → ℕ → (sh : L.Usage) → IR (true ∷ sh) → Type₀ where
  ahere  : ∀ {T sh b} → At ((sh , b) ∷ T) 0 sh b
  athere : ∀ {T B i sh b} → At T i sh b → At (B ∷ T) (suc i) sh b

blkAt : Table → ℕ → Maybe Blk
blkAt []      _       = nothing
blkAt (B ∷ T) zero    = just B
blkAt (B ∷ T) (suc i) = blkAt T i

atFrom : (T : Table) (i : ℕ) {sh : L.Usage} {b : IR (true ∷ sh)}
       → blkAt T i Eq.≡ just (sh , b) → At T i sh b
atFrom []      i       e       = E.rec (nothing≢just e)
atFrom (B ∷ T) zero    Eq.refl = ahere
atFrom (B ∷ T) (suc i) e       = athere (atFrom T i e)

-- ==================================================================
-- §4  THE BIG-STEP SEMANTICS.  Five rules; `⇓lit` is immediate and
-- `⇓add` is the only new recursion.
-- ==================================================================

data Ev (T : Table) : {u : L.Usage} → Frame → IR u → Val → Type₀ where

  ⇓var  : ∀ {u} {σ : Frame} (s : L.Solo u)
        → Ev T σ (ivar s) (σ (slotOf 0 u s))

  ⇓clos : ∀ {sh u} {σ : Frame} (i : ℕ) (cap : Cap sh u)
        → Ev T σ (iclos i cap) (clos i (capVals σ cap))

  ⇓call : ∀ {u₁ u₂ u} {σ : Frame} {sp : L.Use⊎ u₁ u₂ u}
            {f : IR u₁} {a : IR u₂} {i sh vs} {body : IR (true ∷ sh)} {va w}
        → Ev T σ f (clos i vs)
        → At T i sh body
        → Ev T σ a va
        → Ev T (callFrame sh vs va) body w
        → Ev T σ (iapp sp f a) w

  ⇓lit  : ∀ {u} {σ : Frame} (e : L.Empty u) (n : ℕ)
        → Ev T σ (ilit e n) (num n)

  ⇓add  : ∀ {u₁ u₂ u} {σ : Frame} {sp : L.Use⊎ u₁ u₂ u}
            {a : IR u₁} {b : IR u₂} {m n : ℕ}
        → Ev T σ a (num m)
        → Ev T σ b (num n)
        → Ev T σ (iadd sp a b) (num (m + n))

-- ==================================================================
-- §5  THE EXECUTABLE EVALUATOR.  Written WITHOUT `with`, for the
-- reason `Compile/Semantics/Size.agda`'s header gives.
-- ==================================================================

evalI : ℕ → (T : Table) → ∀ {u} → Frame → IR u → Maybe Val
callI : ℕ → (T : Table) → Maybe Val → Maybe Val → Maybe Val
callB : ℕ → (T : Table) → Maybe Blk → List Val → Val → Maybe Val
addV  : Maybe Val → Maybe Val → Maybe Val

-- PRIMITIVE (phase 1)
evalI zero    T σ e             = nothing
evalI (suc k) T σ (ivar {u} s)  = just (σ (slotOf 0 u s))
evalI (suc k) T σ (iclos i cap) = just (clos i (capVals σ cap))
evalI (suc k) T σ (iapp sp f a) = callI k T (evalI k T σ f) (evalI k T σ a)
evalI (suc k) T σ (ilit e n)    = just (num n)
evalI (suc k) T σ (iadd sp a b) = addV (evalI k T σ a) (evalI k T σ b)

callI k T (just (clos i vs)) (just va) = callB k T (blkAt T i) vs va
callI k T _                  _         = nothing

callB k T nothing            vs va = nothing
callB k T (just (sh , body)) vs va = evalI k T (callFrame sh vs va) body

-- ADDING A CLOSURE IS `nothing`, not junk.  See the header: the ARM
-- backend cannot make this distinction and says so.
addV (just (num m)) (just (num n)) = just (num (m + n))
addV _              _              = nothing

runI : ℕ → Table → IR [] → Maybe Val
runI k T e = evalI k T emptyF e

runP : ℕ → Prog → Maybe Val
runP k P = runI k (P .fst) (P .snd)

-- ==================================================================
-- §6  THE EVALUATOR IS SOUND FOR THE RELATION.
--
-- `ClosureConv/IR.agda` §8, with one more inversion.  `addV-inv` is
-- `callI-inv`'s shape: a successful add names its two summands.
-- ==================================================================

private
  CallInv : Table → Maybe Val → Maybe Val → Val → ℕ → Type₀
  CallInv T mf ma v k =
    Σ[ i ∈ ℕ ] Σ[ vs ∈ List Val ] Σ[ va ∈ Val ]
    Σ[ sh ∈ L.Usage ] Σ[ body ∈ IR (true ∷ sh) ]
      ( (mf Eq.≡ just (clos i vs)) × (ma Eq.≡ just va)
      × At T i sh body
      × (evalI k T (callFrame sh vs va) body Eq.≡ just v) )

  callI-inv : (k : ℕ) (T : Table) (mf ma : Maybe Val) (v : Val)
            → callI k T mf ma Eq.≡ just v → CallInv T mf ma v k
  callI-inv k T nothing            ma        v p = E.rec (nothing≢just p)
  callI-inv k T (just (num _))     ma        v p = E.rec (nothing≢just p)
  callI-inv k T (just (clos i vs)) nothing   v p = E.rec (nothing≢just p)
  callI-inv k T (just (clos i vs)) (just va) v p = go (blkAt T i) Eq.refl
    where
    go : (mb : Maybe Blk) → blkAt T i Eq.≡ mb
       → CallInv T (just (clos i vs)) (just va) v k
    go nothing e =
      E.rec (nothing≢just (Eq.transport (λ z → callB k T z vs va Eq.≡ just v) e p))
    go (just (sh , body)) e =
      i , vs , va , sh , body , Eq.refl , Eq.refl , atFrom T i e
      , Eq.transport (λ z → callB k T z vs va Eq.≡ just v) e p

  AddInv : Maybe Val → Maybe Val → Val → Type₀
  AddInv ma mb v =
    Σ[ m ∈ ℕ ] Σ[ n ∈ ℕ ]
      ((ma Eq.≡ just (num m)) × (mb Eq.≡ just (num n)) × (v Eq.≡ num (m + n)))

  addV-inv : (ma mb : Maybe Val) (v : Val) → addV ma mb Eq.≡ just v
           → AddInv ma mb v
  addV-inv nothing            mb                v p = E.rec (nothing≢just p)
  addV-inv (just (clos _ _))  mb                v p = E.rec (nothing≢just p)
  addV-inv (just (num m))     nothing           v p = E.rec (nothing≢just p)
  addV-inv (just (num m))     (just (clos _ _)) v p = E.rec (nothing≢just p)
  addV-inv (just (num m))     (just (num n))    v p =
    m , n , Eq.refl , Eq.refl , Eq.sym (just-inj p)

evalSound : (k : ℕ) (T : Table) {u : L.Usage} (σ : Frame) (e : IR u) (v : Val)
          → evalI k T σ e Eq.≡ just v → Ev T σ e v
evalSound zero    T σ e             v p = E.rec (nothing≢just p)
evalSound (suc k) T σ (ivar {u} s)  v p =
  Eq.transport (λ z → Ev T σ (ivar s) z) (just-inj p) (⇓var s)
evalSound (suc k) T σ (iclos i cap) v p =
  Eq.transport (λ z → Ev T σ (iclos i cap) z) (just-inj p) (⇓clos i cap)
evalSound (suc k) T σ (iapp sp f a) v p =
  let (i , vs , va , sh , body , ef , ea , at , eb) =
        callI-inv k T (evalI k T σ f) (evalI k T σ a) v p
  in ⇓call (evalSound k T σ f (clos i vs) ef)
           at
           (evalSound k T σ a va ea)
           (evalSound k T (callFrame sh vs va) body v eb)
evalSound (suc k) T σ (ilit e n)    v p =
  Eq.transport (λ z → Ev T σ (ilit e n) z) (just-inj p) (⇓lit e n)
evalSound (suc k) T σ (iadd sp a b) v p =
  let (m , n , ea , eb , ev) = addV-inv (evalI k T σ a) (evalI k T σ b) v p
  in Eq.transport (λ z → Ev T σ (iadd sp a b) z) (Eq.sym ev)
       (⇓add (evalSound k T σ a (num m) ea) (evalSound k T σ b (num n) eb))

-- ==================================================================
-- §7  IT COMPUTES.  Nothing here goes through a compiler, so these
-- measure the MACHINE.
-- ==================================================================

private
  -- block 0 : `λ_. slot0 + 1`
  incBlk : Blk
  incBlk = [] , iadd (L.uleft L.unil) (ivar tt) (ilit tt 1)

  Tinc : Table
  Tinc = incBlk ∷ []

  -- `(λx. x + 1) 41`, by hand
  incApp : IR []
  incApp = iapp L.unil (iclos 0 (cnil tt)) (ilit tt 41)

  _ : runI 10 Tinc incApp Eq.≡ just (num 42)
  _ = Eq.refl

  _ : numOf (runI 10 Tinc incApp) Eq.≡ just 42
  _ = Eq.refl

  -- ... and the DERIVATION, extracted from that computation
  incDeriv : Ev Tinc emptyF incApp (num 42)
  incDeriv = evalSound 10 Tinc emptyF incApp (num 42) Eq.refl

  -- adding a closure gets `nothing`, not junk
  _ : runI 10 Tinc (iadd L.unil (iclos 0 (cnil tt)) (ilit tt 1)) Eq.≡ nothing
  _ = Eq.refl
