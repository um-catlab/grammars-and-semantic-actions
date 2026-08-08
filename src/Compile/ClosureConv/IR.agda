{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  A FIRST-ORDER, LINEAR INTERMEDIATE REPRESENTATION.

  ------------------------------------------------------------------
  WHY THIS FILE EXISTS
  ------------------------------------------------------------------

  `Compile/ArithToARM/AArch64Codegen.agda` proves a full correctness
  theorem against real AArch64, and the reason it can is that its
  source `Exp` has NO BINDERS: every leaf is a slot of a flat frame, so
  "compile" is a fold and "correct" is a four-field postcondition about
  registers and memory.  The linear λ-calculus cannot be handed to that
  proof, because `tlam` moves the index (`Syntax.agda`: abstraction is
  reindexing along weakening) and a machine has no reindexing.

  CLOSURE CONVERSION is the pass that removes the obstruction.  After
  it, a program is

      a TABLE of code blocks, each taking (environment, argument)
      an EXPRESSION built from `ivar`, `iapp` and `iclos i cap`

  and `IR` below has exactly three constructors, none of which binds.
  The λ is gone; what is left of it is a NUMBER (the block's index) and
  a CAPTURE (which of the enclosing frame's slots the block will read).

  ------------------------------------------------------------------
  LINEARITY SURVIVES THE PASS, AND IT SURVIVES STRUCTURALLY
  ------------------------------------------------------------------

  `IR` is indexed by `Usage`, and `iapp` carries the SAME `Use⊎ u₁ u₂ u`
  that `L.tapp` carries.  So the missing `(true,true)` constructor is
  still what rules out double use, and a map `IR u → IR u` still cannot
  invent or drop a variable.  That is not an accident of the encoding:
  the conversion in `Convert.agda` has the type

      convT : TmG ⊢ ConvG

  -- a term of the calculus, hence index-preserving by construction.

  The capture is the second place linearity is structural.  `Cap sh u`
  says: fill the live slots of the block's shape `sh`, consuming the
  usage `u`, EXACTLY.  Its three constructors are

      cnil   nothing left to capture -- and the residue must be `Empty`
      cdead  a dead slot of the shape captures nothing
      clive  a live slot captures ONE variable, splitting off its usage

  so a capture that read a variable twice, or forgot one, is not a
  `Cap`.  Compare `Compile/ArithToARM/Base.agda`'s `readsDisjoint`: the
  aliasing fact about the emitted code is the source's `Use⊎` again.

  Note what the capture does NOT contain: general expressions.  Its
  entries are `L.Solo` -- VARIABLE REFERENCES -- which is what a real
  closure builder emits (copy k slots of the current frame) and what
  makes `capVals` a total function rather than a recursive evaluator.

  ------------------------------------------------------------------
  THE SEMANTICS IS A MACHINE, NOT A REWRITER
  ------------------------------------------------------------------

  `Compile/LinToRust/Eval.agda` evaluates by SUBSTITUTION, and
  `Compile/Relational/Refutation.agda` then has to repair the square
  because level-based naming is not stable under substitution.  This
  target does not substitute at all.  `Ev T σ e v` reads a FRAME -- a
  total function `ℕ → Val` -- and a call

      Ev T σ f (clos i vs)   At T i sh body   Ev T σ a va
      Ev T (extF va (spread sh vs)) body w
      ------------------------------------------------------ ⇓call
      Ev T σ (iapp sp f a) w

  builds the callee's frame from its captured values and the argument.
  Nothing in the IR is ever rewritten; the only runtime data are `Val`s
  and frames.  That is the interface `AArch64Codegen`'s `Post` wants:
  a state, a step, and a postcondition about the state.

  It does NOT make the square true on the nose.  `Correct.agda` refutes
  it, with the SAME shape of counterexample and a different cause: the
  block INDEX a value carries depends on the whole program's table, and
  the table of `t` is not the table of `t`'s value.  Naming moved from
  binder levels to code pointers; it is still naming.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1 throughout: this is the definition of a machine, in the style
  of `ArithToARM/Base.agda`.  `slotOf`, `spread`, `capVals`, `blkAt`,
  `evalI` are PRIMITIVE and marked.  `LiveAt`-style predicates are
  `Unit`/`⊥`-valued so nothing they carry blocks a `refl`.
-}
open import Cubical.Foundations.Prelude

module Compile.ClosureConv.IR where

open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.List using (List; []; _∷_; _++_; length)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

import TheoryGrammar.Instances.LinLam.Syntax as L

-- ==================================================================
-- §0  TWO `Maybe` UTILITIES, AT A COMPUTING MOTIVE.
--
-- `Compile/Relational/Refutation.agda`'s `IsJust`/`theJust` idiom: the
-- motive is `Unit`/`⊥`, so the observation is `tt` and never blocks.
-- ==================================================================

private
  Nothing? : {A : Type₀} → Maybe A → Type₀
  Nothing? nothing  = Unit
  Nothing? (just _) = ⊥

  fromJust : {A : Type₀} → A → Maybe A → A
  fromJust d nothing  = d
  fromJust d (just a) = a

-- PRIMITIVE (phase 1)
nothing≢just : {A : Type₀} {a : A} → nothing Eq.≡ just a → ⊥
nothing≢just e = Eq.transport Nothing? e tt

-- PRIMITIVE (phase 1)
just-inj : {A : Type₀} {a b : A} → just a Eq.≡ just b → a Eq.≡ b
just-inj {a = a} e = Eq.ap (fromJust a) e

-- ==================================================================
-- §1  SLOTS.
--
-- `slotOf` is `ArithToARM/Base.agda`'s, repeated so this path does not
-- depend on that one; `zeros` and `zsplitL` are the unit of the usage
-- promodel, which `idCap` needs.
-- ==================================================================

-- PRIMITIVE (phase 1)
slotOf : ℕ → (u : L.Usage) → L.Solo u → ℕ
slotOf p []          ()
slotOf p (true  ∷ u) e = p
slotOf p (false ∷ u) s = slotOf (suc p) u s

slotOf-shift : (p : ℕ) (u : L.Usage) (s : L.Solo u)
             → slotOf (suc p) u s Eq.≡ suc (slotOf p u s)
slotOf-shift p []          ()
slotOf-shift p (true  ∷ u) e = Eq.refl
slotOf-shift p (false ∷ u) s = slotOf-shift (suc p) u s

-- the all-dead usage of the same length, and its two facts
zeros : L.Usage → L.Usage
zeros []      = []
zeros (_ ∷ u) = false ∷ zeros u

zerosEmpty : (u : L.Usage) → L.Empty (zeros u)
zerosEmpty []      = tt
zerosEmpty (_ ∷ u) = zerosEmpty u

-- the UNIT LAW of the usage promodel: nothing, joined with `u`, is `u`
zsplitL : (u : L.Usage) → L.Use⊎ (zeros u) u u
zsplitL []          = L.unil
zsplitL (true  ∷ u) = L.uright (zsplitL u)
zsplitL (false ∷ u) = L.uskip  (zsplitL u)

-- ==================================================================
-- §2  CAPTURES.
--
-- `Cap sh u`: values for exactly the live slots of the block's shape
-- `sh`, drawn from the current usage `u` and consuming ALL of it.  The
-- two usages are independent -- `sh` is the callee's scope, `u` the
-- caller's -- which is precisely what closure conversion has to
-- express and what a de Bruijn shift cannot.
-- ==================================================================

data Cap : L.Usage → L.Usage → Type₀ where
  cnil  : ∀ {u} → L.Empty u → Cap [] u
  cdead : ∀ {sh u} → Cap sh u → Cap (false ∷ sh) u
  clive : ∀ {sh u₁ u₂ u} → L.Use⊎ u₁ u₂ u → L.Solo u₁ → Cap sh u₂
        → Cap (true ∷ sh) u

-- ------------------------------------------------------------------
-- A capture survives an unused slot being prepended to the CALLER's
-- scope; every captured position shifts by one.  `L.Solo (false ∷ v)`
-- is `L.Solo v` definitionally, so the entries are unchanged.
-- ------------------------------------------------------------------
capWkD : ∀ {sh u} → Cap sh u → Cap sh (false ∷ u)
capWkD (cnil e)        = cnil e
capWkD (cdead c)       = cdead (capWkD c)
capWkD (clive sp so c) = clive (L.uskip sp) so (capWkD c)

-- THE CAPTURE A BINDER EMITS: every live slot of the current usage,
-- taken once, at the same position.  This is the capture `Convert.agda`
-- uses, and it is why a block's shape IS the usage at its λ.
idCap : (u : L.Usage) → Cap u u
idCap []          = cnil tt
idCap (false ∷ u) = cdead (capWkD (idCap u))
idCap (true  ∷ u) = clive (L.uleft (zsplitL u)) (zerosEmpty u) (capWkD (idCap u))

-- ==================================================================
-- §3  THE IR.  THREE CONSTRUCTORS, NONE OF THEM A BINDER.
-- ==================================================================

data IR : L.Usage → Type₀ where
  ivar  : ∀ {u} → L.Solo u → IR u
  iapp  : ∀ {u₁ u₂ u} → L.Use⊎ u₁ u₂ u → IR u₁ → IR u₂ → IR u
  iclos : ∀ {sh u} → ℕ → Cap sh u → IR u

-- a code block: its environment shape, and its body over
-- (argument at slot 0, environment at slots 1 ..)
Blk : Type₀
Blk = Σ[ sh ∈ L.Usage ] IR (true ∷ sh)

Table : Type₀
Table = List Blk

-- a whole program
Prog : Type₀
Prog = Table × IR []

-- ==================================================================
-- §4  RUNTIME VALUES AND FRAMES.
--
-- A value is a CLOSURE and nothing else -- which is exactly
-- `Compile/Semantics/CBV.agda`'s `closedVal`, "every closed β-normal
-- linear term is a λ", transported to the target.  Frames are TOTAL
-- (`ℕ → Val`), so no lookup is partial and `Ev` needs no side
-- condition; a slot the usage says is dead reads junk, and nothing
-- reads it.
-- ==================================================================

data Val : Type₀ where
  clos : ℕ → List Val → Val

junk : Val
junk = clos 0 []

Frame : Type₀
Frame = ℕ → Val

emptyF : Frame
emptyF _ = junk

extF : Val → Frame → Frame
extF v σ zero    = v
extF v σ (suc p) = σ p

-- PRIMITIVE (phase 1): building a closure's environment.  One value
-- per LIVE slot of the shape, in order; `cdead` contributes nothing.
capVals : ∀ {sh u} → Frame → Cap sh u → List Val
capVals σ (cnil _)                     = []
capVals σ (cdead c)                    = capVals σ c
capVals σ (clive {u₁ = u₁} sp so c)    = σ (slotOf 0 u₁ so) ∷ capVals σ c

-- PRIMITIVE (phase 1): ... and reading it back, positionally.  This is
-- the inverse of `capVals` at the identity capture, in the only sense
-- that matters: `spread u (capVals σ (idCap u))` agrees with `σ` on
-- every live position of `u`.
spread : L.Usage → List Val → Frame
spread []           vs       p       = junk
spread (false ∷ sh) vs       zero    = junk
spread (false ∷ sh) vs       (suc p) = spread sh vs p
spread (true  ∷ sh) []       p       = junk
spread (true  ∷ sh) (v ∷ vs) zero    = v
spread (true  ∷ sh) (v ∷ vs) (suc p) = spread sh vs p

-- the callee's frame: the argument at slot 0, the environment above it
callFrame : L.Usage → List Val → Val → Frame
callFrame sh vs va = extF va (spread sh vs)

-- ==================================================================
-- §5  THE CODE TABLE, AS A RELATION AND AS A FUNCTION.
--
-- `At T i sh b` is the lookup as DATA, so the big-step rule below can
-- bind `sh` and `b` without a `Σ`-equation and without transporting at
-- a family over a variable table -- the documented trap.  `blkAt` is
-- the same lookup as a function, for the evaluator; `atFrom` is the
-- bridge, and it is what turns a `refl` computation into a derivation.
-- ==================================================================

data At : Table → ℕ → (sh : L.Usage) → IR (true ∷ sh) → Type₀ where
  ahere  : ∀ {T sh b} → At ((sh , b) ∷ T) 0 sh b
  athere : ∀ {T B i sh b} → At T i sh b → At (B ∷ T) (suc i) sh b

-- PRIMITIVE (phase 1)
blkAt : Table → ℕ → Maybe Blk
blkAt []      _       = nothing
blkAt (B ∷ T) zero    = just B
blkAt (B ∷ T) (suc i) = blkAt T i

atFrom : (T : Table) (i : ℕ) {sh : L.Usage} {b : IR (true ∷ sh)}
       → blkAt T i Eq.≡ just (sh , b) → At T i sh b
atFrom []      i       e       = E.rec (nothing≢just e)
atFrom (B ∷ T) zero    Eq.refl = ahere
atFrom (B ∷ T) (suc i) e       = athere (atFrom T i e)

-- appending code before a table shifts its indices, and appending
-- after leaves them alone.  Both are one-line inductions and both are
-- what `Convert.agda`'s block numbering needs.
at-++ˡ : ∀ {T₁ i sh b} (T₂ : Table) → At T₁ i sh b → At (T₁ ++ T₂) i sh b
at-++ˡ T₂ ahere      = ahere
at-++ˡ T₂ (athere a) = athere (at-++ˡ T₂ a)

at-++ʳ : ∀ (T₁ : Table) {T₂ i sh b} → At T₂ i sh b → At (T₁ ++ T₂) (length T₁ + i) sh b
at-++ʳ []       a = a
at-++ʳ (B ∷ T₁) a = athere (at-++ʳ T₁ a)

-- ==================================================================
-- §6  THE BIG-STEP SEMANTICS.
--
-- Three rules, and only one of them recurses.  `ivar` and `iclos` are
-- IMMEDIATE -- a frame read and a copy of k slots -- which is the sense
-- in which this is a machine and not a rewriter.
-- ==================================================================

data Ev (T : Table) : {u : L.Usage} → Frame → IR u → Val → Type₀ where

  ⇓var  : ∀ {u} {σ : Frame} (s : L.Solo u)
        → Ev T σ (ivar s) (σ (slotOf 0 u s))

  ⇓clos : ∀ {sh u} {σ : Frame} (i : ℕ) (cap : Cap sh u)
        → Ev T σ (iclos i cap) (clos i (capVals σ cap))

  ⇓call : ∀ {u₁ u₂ u} {σ : Frame} {sp : L.Use⊎ u₁ u₂ u}
            {f : IR u₁} {a : IR u₂} {i sh vs} {body : IR (true ∷ sh)} {va w}
        → Ev T σ f (clos i vs)                       -- (1) the callee
        → At T i sh body                             --     its code
        → Ev T σ a va                                -- (2) the argument
        → Ev T (callFrame sh vs va) body w           -- (3) the body
        → Ev T σ (iapp sp f a) w

-- ==================================================================
-- §7  THE EXECUTABLE EVALUATOR.
--
-- Fuelled, and written WITHOUT `with` -- `Compile/Semantics/Size.agda`'s
-- header explains why: a `with`-lifted auxiliary is inaccessible, so a
-- proof about it cannot case-split.  Three named mutual functions cost
-- nothing and make `evalSound` below a plain induction.
-- ==================================================================

evalI : ℕ → (T : Table) → ∀ {u} → Frame → IR u → Maybe Val
callI : ℕ → (T : Table) → Maybe Val → Maybe Val → Maybe Val
callB : ℕ → (T : Table) → Maybe Blk → List Val → Val → Maybe Val

-- PRIMITIVE (phase 1)
evalI zero    T σ e             = nothing
evalI (suc k) T σ (ivar {u} s)  = just (σ (slotOf 0 u s))
evalI (suc k) T σ (iclos i cap) = just (clos i (capVals σ cap))
evalI (suc k) T σ (iapp sp f a) = callI k T (evalI k T σ f) (evalI k T σ a)

callI k T (just (clos i vs)) (just va) = callB k T (blkAt T i) vs va
callI k T _                  _         = nothing

callB k T nothing            vs va = nothing
callB k T (just (sh , body)) vs va = evalI k T (callFrame sh vs va) body

runI : ℕ → Table → IR [] → Maybe Val
runI k T e = evalI k T emptyF e

runP : ℕ → Prog → Maybe Val
runP k P = runI k (P .fst) (P .snd)

-- ==================================================================
-- §8  THE EVALUATOR IS SOUND FOR THE RELATION.
--
-- This is what lets a `refl` computation in `Correct.agda` be used as a
-- DERIVATION: `Compile/Relational/Refutation.agda` gets the same thing
-- from `theJust`, at the cost of `evalRust` carrying its derivations in
-- its type.  Here the evaluator is a plain `Maybe Val` and the bridge
-- is proved once.
-- ==================================================================

private
  -- the inversion `callI` needs: a successful call names its block.
  CallInv : Table → Maybe Val → Maybe Val → Val → ℕ → Type₀
  CallInv T mf ma v k =
    Σ[ i ∈ ℕ ] Σ[ vs ∈ List Val ] Σ[ va ∈ Val ]
    Σ[ sh ∈ L.Usage ] Σ[ body ∈ IR (true ∷ sh) ]
      ( (mf Eq.≡ just (clos i vs)) × (ma Eq.≡ just va)
      × At T i sh body
      × (evalI k T (callFrame sh vs va) body Eq.≡ just v) )

  callI-inv : (k : ℕ) (T : Table) (mf ma : Maybe Val) (v : Val)
            → callI k T mf ma Eq.≡ just v → CallInv T mf ma v k
  callI-inv k T nothing            ma         v p = E.rec (nothing≢just p)
  callI-inv k T (just (clos i vs)) nothing    v p = E.rec (nothing≢just p)
  callI-inv k T (just (clos i vs)) (just va)  v p = go (blkAt T i) Eq.refl
    where
    go : (mb : Maybe Blk) → blkAt T i Eq.≡ mb
       → CallInv T (just (clos i vs)) (just va) v k
    go nothing e =
      E.rec (nothing≢just (Eq.transport (λ z → callB k T z vs va Eq.≡ just v) e p))
    go (just (sh , body)) e =
      i , vs , va , sh , body , Eq.refl , Eq.refl , atFrom T i e
      , Eq.transport (λ z → callB k T z vs va Eq.≡ just v) e p

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

-- ==================================================================
-- §9  IT COMPUTES.
--
-- The identity closure, by hand: one block, `λ_. slot 0`, and the
-- closure that names it.  Nothing here goes through `Convert.agda`, so
-- these tests measure the MACHINE and not the compiler.
-- ==================================================================

private
  -- block 0 : shape `[]`, body = the argument
  idBlk : Blk
  idBlk = [] , ivar tt

  Tid : Table
  Tid = idBlk ∷ []

  idClos : IR []
  idClos = iclos 0 (cnil tt)

  selfClos : IR []
  selfClos = iapp L.unil idClos idClos

  _ : runI 10 Tid idClos Eq.≡ just (clos 0 [])
  _ = Eq.refl

  -- applying the identity closure to itself returns it
  _ : runI 10 Tid selfClos Eq.≡ just (clos 0 [])
  _ = Eq.refl

  -- ... and the derivation is extracted from that computation
  selfDeriv : Ev Tid emptyF selfClos (clos 0 [])
  selfDeriv = evalSound 10 Tid emptyF selfClos (clos 0 []) Eq.refl

  -- the identity capture reads the live slots and nothing else
  _ : capVals (extF (clos 7 []) emptyF) (idCap (true ∷ [])) Eq.≡ (clos 7 [] ∷ [])
  _ = Eq.refl

  _ : capVals (extF (clos 7 []) emptyF) (idCap (false ∷ [])) Eq.≡ []
  _ = Eq.refl
