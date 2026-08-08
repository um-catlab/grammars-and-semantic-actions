{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE C TARGET, AS A THEORY -- AND A MODEL OF IT.

  Everything about the C backend so far has been stated in the target's
  own idiom: `CStmt` is a datatype, `CProg` is a list, `evalC` is a
  function, `sem` is a relation.  This file says the same things in the
  framework's currency -- a `SortedSig`, a `Fibered` promodel over it, a
  `Theory`, a `Model`, and a `Pass` -- so that the C backend is an object
  of the same kind as `Reindex.Sanity.layoutPass` and `ISA.Pass.semPass`
  rather than a parallel development that merely resembles one.

  ------------------------------------------------------------------
  §A  THE FRAGMENT.  NOTHING IS INVENTED.
  ------------------------------------------------------------------

  `cSig` below is read off `Machine.CStmt` and `Print.stmtToks`, and off
  nothing else.  Its operations are, in one-to-one correspondence with
  the source text the printer actually emits:

      emptyOp        (nothing)                    -- the empty block
      seqOp          `p₁ p₂`                      -- juxtaposition
      embOp          a statement, as a program
      skipOp         `;`
      declOp  l x    `val_t x<l> = <x>;`
      storeOp l x    `*(mem + <l>) = <x>;`
      mallocOp  x    `val_t *p = malloc(sizeof(val_t)); *p = <x>;`

  There is no `if`, no `while`, no `goto`, no expression, no call and no
  `free`, for exactly the reasons `Machine.agda`'s header gives: program
  text here is the FREE MONOID on statements, and a free monoid has
  juxtaposition and nothing else.  Adding a branch would change `Split
  seqOp`, not add a constant, so it is a different theory and not this
  one extended.

  The signature is TWO-SORTED (`stmt`, `prog`) because C is: a statement
  is not a program, `embOp` is the coercion, and the printer's
  `stmtToks`/`toks` split along exactly that line.  This is the first
  genuinely many-sorted signature in the compile pipeline -- `monoidSig`
  is `Unit`-sorted -- and it costs nothing, which is the point of
  `SortedSig` being many-sorted from the start.

  ------------------------------------------------------------------
  §B  WHICH CARRIER?  TEXT, NOT HEAP -- AND WHY.
  ------------------------------------------------------------------

  There are two candidate carriers and only one of them is the C target.

    TEXT.   `carrier prog = CProg`, `carrier stmt = CStmt`.  Splittings
            are `Strings`-shaped: `Split seqOp p` is a way of writing
            `p = p₁ ++ p₂` (`PT.Split3`, reused verbatim), and the leaf
            splittings are Unit/⊥-valued recognisers.  This is the
            SYNTAX of the fragment, and it is what a "theory of C" must
            be about: its elements are C programs.

    HEAP.   `carrier _ = Heap`, splittings disjoint (`heapFib`).  This is
            not the C target, it is the OBSERVABLE -- the thing three
            backends were pinned to so their agreement is composition
            (`Showcase.agreeᴬᶜ`).  It is already a theory
            (`Reindex.Sanity.heapTheory`) and it is the CODOMAIN of a
            compiler, not a presentation of a target language.

  So `cFib` is the text promodel, and the heap enters only through the
  semantics.  That decision is forced, not stylistic, and §D says by
  what.

  ------------------------------------------------------------------
  §C  THE MODEL: COMMANDS, NOT HEAP TRANSFORMERS.
  ------------------------------------------------------------------

  `cmdModel` interprets every operation as a `Cmd` (a relation on heaps):
  `seqOp` as `⨟`, `emptyOp`/`skipOp` as `skip`, `declOp`/`storeOp` as
  `Write`, `mallocOp` as `ISA.Toy.Alloc`.  It is TOTAL.

  The obvious alternative -- interpret a program as a function `Heap →
  Heap`, which is literally what `evalC` is -- cannot be total, and the
  obstruction is in the fragment: `cmalloc` does not name its address, so
  it has no functional interpretation.  `Machine.Det (cmalloc x) = ⊥` is
  that fact already recorded, and `Machine.evalS (cmalloc x) h = h` is a
  junk clause its own comment marks unreachable.  Making the model
  relational removes the junk instead of documenting it, and it is the
  same trade `ISA.Machine` made: a nondeterministic allocator is what
  makes `Local` and hence the frame rule available at all
  (`Machine.mallocLocal`), while a statement that NAMES its address is
  not local (`Machine.noWriteLocal`).

  Both promodels have a `LaxPoint` (`cPoint`, `cmdPoint`), so both really
  are pointed by their operations.  They differ in HONESTY, in
  `Fibered.Honest`'s sense:

      cHonest    -- PROVED.  Every splitting of C text recomposes to the
                   text it split, so `cFib` is the term model: the
                   splitting relation is exactly the graph of `cOp`.

      cmdNotHonest -- PROVED, the other way.  `Split seqOp c` is a LAX
                   factorisation `c ⊑ c₁ ⨟ c₂`, so a splitting recomposes
                   only to something the command REFINES, and the empty
                   command witnesses the gap.  This is `ISA.Machine`'s
                   design and `Bags`' `Ilv` one more time.

  ------------------------------------------------------------------
  §D  WHY THE PASS DOES NOT LAND IN `heapFib` -- `noOwnership`, AS A
      STATEMENT ABOUT THEORIES.
  ------------------------------------------------------------------

  It is tempting to make the semantic side the heap directly: send `p` to
  `objects p = evalC p []`.  That map exists, and `noSeqSeparation` below
  proves it is NOT a map of promodels into `heapFib`.

  `Machine.aliasC = cdecl 0 v1 ∷ cstore 0 v1 ∷ []` splits in the text
  theory -- `PT.splitAll` gives the canonical `seqOp` splitting into its
  two statements, and NOTHING in C objects, which is `Machine.noOwnership`
  read as a property of the syntax.  Its two halves have footprints
  `single 0 v1` and `single 0 v1`.  A `heapFib` splitting requires `_#_`,
  and `single 0 v1 # single 0 v1` is absurd.  So:

      SEQUENCING IN C IS NOT SEPARATION.

  and the semantic theory must be one whose `seqOp` splitting is plain
  composition.  That is `cmdCFib`.  Where separation does appear is on
  the far side of the COMPILER (`Codegen.noAliasC`), and it gets there
  from `LinLam/Codegen.layPres` -- four modules upstream, out of the
  constructor `Use⊎` does not have.  The theory-level reading of the C
  backend's whole moral is therefore: the target theory is too weak to
  state alias-freedom, and the compiler is where it is established.

  ------------------------------------------------------------------
  §E  SCOPE LIMIT.  READ THIS BEFORE QUOTING ANYTHING BELOW.
  ------------------------------------------------------------------

  `allocSpec` -- the repackaging of `Codegen.runC` -- says

      the C emitted for the usage `u`, read in `cmdModel`, relates the
      empty heap to `u`'s layout.

  That is a theorem about ALLOCATION AND LAYOUT.  It is NOT a
  computational correctness theorem, and no strengthening of this file
  can make it one.  The reason is structural, not a missing lemma:

      compileC : Usage → CProg

  factors through the INDEX.  The compiler never sees the source term, so
  `Compile.Semantics.Simulation.noBlindBackend` refutes the value-level
  square for this entire family at once (witnesses `x y` and `y x`:
  distinct β-normal terms, one usage, one program), and
  `Simulation.strong→weak`/`weak→strong` show that for a usage-directed
  observable the strong statement and the weak one are interderivable --
  so proving the strong square here would carry exactly as much
  information about computation as `allocSpec` already does, namely none.
  `Compile.Showcase` §7 is the long form of this paragraph and should be
  read with it.

  Concretely, and this is the sharpest way to see it: `L.idLin` and
  `L.selfApp` are different terms, both compile to the EMPTY C program,
  and every theorem in this file is satisfied.  The `refl` lines in §9
  say so on purpose.

  What this file DOES add over `Codegen`: the statements are now in the
  currency that composes.  `cPass` is a `Pass`, so `_⨟P_` and `Chain`
  apply to it, and the C target can be a link in a pipeline rather than a
  terminus with a bespoke theorem.

  ------------------------------------------------------------------
  §F  PHASE
  ------------------------------------------------------------------

  Phase 1, all marked: the Unit/⊥ recognisers (`IsStmt1`, `SameLoc`,
  `SameVal`, `IsSkip`, `IsDecl`, `IsStore`, `IsMalloc`) and their
  projections, `cSplit3++`, `sem-one`, `coeCmd`, and the four `⊑`
  coercions.  Everything from `cPass` down is a composite of `homSplit3`,
  `semNil`, `evalC-sound` and `runC`, none of which is proved here.

      inductions over a program in this file:  1  (`cSplit3++`)
      Hoare rules proved in this file:         0
      recursions over a usage in this file:    0
-}
open import Cubical.Foundations.Prelude

module Compile.LinToC.Theory where

open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.List using (List; []; _∷_; _++_)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.ChangeOfTheory using (SigMor)
open import TheoryGrammar.Reindex.Base
open import TheoryGrammar.Reindex.Pass

-- the C target: `CStmt`, `CProg`, `cStep`, `Write`, `sem`, `evalC`,
-- `Dets`, `aliasC`, `_#_`, and (through `ISA.Program`) `PT` -- the
-- `Strings` promodel at the statement alphabet
open import Compile.LinToC.Machine

-- `Alloc`, for `cmalloc`'s interpretation.  `Machine` uses it but does
-- not re-export it.
import ISA.Toy as Toy

-- the compiler, for §8 only
import Compile.LinToC.Codegen as CG
import TheoryGrammar.Instances.LinLam.Codegen as L

-- ==================================================================
-- §1  THE SIGNATURE OF THE FRAGMENT.
--
-- Two sorts, seven operation families, and each one is a line of
-- `Print.stmtToks`.  Nothing here is a C feature the backend does not
-- emit; see §A of the header for what is deliberately absent.
-- ==================================================================

data CSort : Type₀ where
  stmt prog : CSort

data COp : Type₀ where
  emptyOp  : COp                 -- the empty block
  seqOp    : COp                 -- `p₁ p₂`
  embOp    : COp                 -- a statement, used as a program
  skipOp   : COp                 -- `;`
  declOp   : Loc → Val → COp     -- `val_t x<l> = <x>;`
  storeOp  : Loc → Val → COp     -- `*(mem + <l>) = <x>;`
  mallocOp : Val → COp           -- `val_t *p = malloc(…); *p = <x>;`

CAr : COp → Type₀
CAr emptyOp      = ⊥
CAr seqOp        = Bool
CAr embOp        = Unit
CAr skipOp       = ⊥
CAr (declOp _ _)  = ⊥
CAr (storeOp _ _) = ⊥
CAr (mallocOp _)  = ⊥

cSortOf : (o : COp) → CAr o → CSort
cSortOf emptyOp      ()
cSortOf seqOp        _ = prog
cSortOf embOp        _ = stmt
cSortOf skipOp       ()
cSortOf (declOp _ _)  ()
cSortOf (storeOp _ _) ()
cSortOf (mallocOp _)  ()

cResult : COp → CSort
cResult emptyOp      = prog
cResult seqOp        = prog
cResult embOp        = prog
cResult skipOp       = stmt
cResult (declOp _ _)  = stmt
cResult (storeOp _ _) = stmt
cResult (mallocOp _)  = stmt

cSig : SortedSig CSort ℓ-zero ℓ-zero
cSig .ops          = COp
cSig .arities      = CAr
cSig .sortOf       = cSortOf
cSig .resultSort   = cResult

-- ==================================================================
-- §2  THE RECOGNISERS.
--
-- Every leaf operation's splitting is "this statement IS that
-- statement", and every one of them is Unit/⊥-valued, so a splitting is
-- a nest of `tt` and the `refl` lines in §9 go through.  This is
-- `Heap/Base`'s discipline for `Diff`/`Fresh`/`IsNil`, applied to
-- syntax.
--
-- PRIMITIVE (phase 1): all of §2 matches representations.
-- ==================================================================

-- "this program is a single statement", and which one
IsStmt1 : CProg → Type₀
IsStmt1 []          = ⊥
IsStmt1 (_ ∷ [])    = Unit
IsStmt1 (_ ∷ _ ∷ _) = ⊥

theStmt : (p : CProg) → IsStmt1 p → CStmt
theStmt []            ()
theStmt (s ∷ [])      _ = s
theStmt (_ ∷ _ ∷ _)   ()

-- decidable equality of locations and values, Unit/⊥-valued
SameLoc : Loc → Loc → Type₀
SameLoc zero    zero    = Unit
SameLoc zero    (suc _) = ⊥
SameLoc (suc _) zero    = ⊥
SameLoc (suc m) (suc n) = SameLoc m n

sameLoc-refl : (l : Loc) → SameLoc l l
sameLoc-refl zero    = tt
sameLoc-refl (suc l) = sameLoc-refl l

sameLoc→Eq : (l k : Loc) → SameLoc l k → l Eq.≡ k
sameLoc→Eq zero    zero    _ = Eq.refl
sameLoc→Eq zero    (suc k) ()
sameLoc→Eq (suc l) zero    ()
sameLoc→Eq (suc l) (suc k) e = Eq.ap suc (sameLoc→Eq l k e)

SameVal : Val → Val → Type₀
SameVal v0 v0 = Unit
SameVal v0 v1 = ⊥
SameVal v0 v2 = ⊥
SameVal v1 v0 = ⊥
SameVal v1 v1 = Unit
SameVal v1 v2 = ⊥
SameVal v2 v0 = ⊥
SameVal v2 v1 = ⊥
SameVal v2 v2 = Unit

sameVal-refl : (x : Val) → SameVal x x
sameVal-refl v0 = tt
sameVal-refl v1 = tt
sameVal-refl v2 = tt

sameVal→Eq : (x y : Val) → SameVal x y → x Eq.≡ y
sameVal→Eq v0 v0 _ = Eq.refl
sameVal→Eq v0 v1 ()
sameVal→Eq v0 v2 ()
sameVal→Eq v1 v0 ()
sameVal→Eq v1 v1 _ = Eq.refl
sameVal→Eq v1 v2 ()
sameVal→Eq v2 v0 ()
sameVal→Eq v2 v1 ()
sameVal→Eq v2 v2 _ = Eq.refl

-- PRIMITIVE (phase 1): the binary congruence of `Eq`, which
-- `Cubical.Data.Equality` has only in its unary form.
eqAp₂ : {A B C : Type₀} (f : A → B → C) {a a' : A} {b b' : B}
      → a Eq.≡ a' → b Eq.≡ b' → f a b Eq.≡ f a' b'
eqAp₂ f Eq.refl Eq.refl = Eq.refl

-- the four statement recognisers
IsSkip : CStmt → Type₀
IsSkip cskip        = Unit
IsSkip (cdecl _ _)  = ⊥
IsSkip (cstore _ _) = ⊥
IsSkip (cmalloc _)  = ⊥

IsDecl : Loc → Val → CStmt → Type₀
IsDecl l x cskip        = ⊥
IsDecl l x (cdecl k y)  = SameLoc l k × SameVal x y
IsDecl l x (cstore _ _) = ⊥
IsDecl l x (cmalloc _)  = ⊥

IsStore : Loc → Val → CStmt → Type₀
IsStore l x cskip        = ⊥
IsStore l x (cdecl _ _)  = ⊥
IsStore l x (cstore k y) = SameLoc l k × SameVal x y
IsStore l x (cmalloc _)  = ⊥

IsMalloc : Val → CStmt → Type₀
IsMalloc x cskip        = ⊥
IsMalloc x (cdecl _ _)  = ⊥
IsMalloc x (cstore _ _) = ⊥
IsMalloc x (cmalloc y)  = SameVal x y

-- ==================================================================
-- §3  THE SYNTAX PROMODEL.  C PROGRAM TEXT.
--
-- `Split seqOp` is `PT.Split3` -- the `Strings` promodel at the
-- statement alphabet, reused with nothing added.  That is what makes
-- `⊗ˢ seqOp` sequential composition of C text and `homSplit3` (already
-- proved, once, in `ISA.Program`) the whole of §5's `seqOp` clause.
-- ==================================================================

CCarrier : CSort → Type₀
CCarrier stmt = CStmt
CCarrier prog = CProg

CSplit : (o : COp) → CCarrier (cResult o) → Type₀
CSplit emptyOp       p = PT.IsNil p
CSplit seqOp         p = Σ[ p₁ ∈ CProg ] Σ[ p₂ ∈ CProg ] PT.Split3 p₁ p₂ p
CSplit embOp         p = IsStmt1 p
CSplit skipOp        s = IsSkip s
CSplit (declOp l x)  s = IsDecl l x s
CSplit (storeOp l x) s = IsStore l x s
CSplit (mallocOp x)  s = IsMalloc x s

CParts : (o : COp) (m : CCarrier (cResult o))
       → CSplit o m → (a : CAr o) → CCarrier (cSortOf o a)
CParts emptyOp       p sp ()
CParts seqOp         p (p₁ , p₂ , _) = boolΠ {M = λ _ → CProg} p₁ p₂
CParts embOp         p sp _ = theStmt p sp
CParts skipOp        s sp ()
CParts (declOp _ _)  s sp ()
CParts (storeOp _ _) s sp ()
CParts (mallocOp _)  s sp ()

cFib : Fibered cSig ℓ-zero ℓ-zero
cFib .carrier = CCarrier
cFib .Split   = CSplit
cFib .parts   = CParts

-- ==================================================================
-- §4  ... AND IT IS POINTED, AND HONEST.
--
-- `cOp` is the syntax: juxtaposition, the singleton program, and the
-- four constructors.  `cHonest` says the splitting relation is EXACTLY
-- the graph of `cOp` -- `cFib` is the term model of `cSig`.  Contrast
-- `cmdCFib` in §6, where honesty fails by design.
-- ==================================================================

cOp : (o : COp) → ((a : CAr o) → CCarrier (cSortOf o a))
    → CCarrier (cResult o)
cOp emptyOp       _  = []
cOp seqOp         m⃗ = m⃗ true ++ m⃗ false
cOp embOp         m⃗ = m⃗ tt ∷ []
cOp skipOp        _  = cskip
cOp (declOp l x)  _  = cdecl l x
cOp (storeOp l x) _  = cstore l x
cOp (mallocOp x)  _  = cmalloc x

cPoint : LaxPoint cFib
cPoint .op = cOp
cPoint .split emptyOp       m⃗ = tt
cPoint .split seqOp         m⃗ = m⃗ true , m⃗ false , PT.splitAll (m⃗ true) (m⃗ false)
cPoint .split embOp         m⃗ = tt
cPoint .split skipOp        m⃗ = tt
cPoint .split (declOp l x)  m⃗ = sameLoc-refl l , sameVal-refl x
cPoint .split (storeOp l x) m⃗ = sameLoc-refl l , sameVal-refl x
cPoint .split (mallocOp x)  m⃗ = sameVal-refl x
cPoint .parts-split emptyOp       m⃗ = funExt λ ()
cPoint .parts-split seqOp         m⃗ =
  funExt (boolΠ {M = λ a → boolΠ {M = λ _ → CProg} (m⃗ true) (m⃗ false) a ≡ m⃗ a}
                refl refl)
cPoint .parts-split embOp         m⃗ = funExt λ _ → refl
cPoint .parts-split skipOp        m⃗ = funExt λ ()
cPoint .parts-split (declOp _ _)  m⃗ = funExt λ ()
cPoint .parts-split (storeOp _ _) m⃗ = funExt λ ()
cPoint .parts-split (mallocOp _)  m⃗ = funExt λ ()

-- PRIMITIVE (phase 1): the ONE induction over a program in this file.
-- It is the free monoid's defining property, and nothing else in the
-- file recurses.
cSplit3++ : {p₁ p₂ p : CProg} → PT.Split3 p₁ p₂ p → (p₁ ++ p₂) Eq.≡ p
cSplit3++ PT.nil      = Eq.refl
cSplit3++ (PT.cons s) = Eq.ap (_ ∷_) (cSplit3++ s)

cNil : (p : CProg) → PT.IsNil p → [] Eq.≡ p
cNil []      _  = Eq.refl
cNil (_ ∷ _) ()

cStmt1 : (p : CProg) (sp : IsStmt1 p) → (theStmt p sp ∷ []) Eq.≡ p
cStmt1 []            ()
cStmt1 (_ ∷ [])      _ = Eq.refl
cStmt1 (_ ∷ _ ∷ _)   ()

-- THE SYNTAX PROMODEL IS HONEST: every splitting recomposes.
cHonest : Honest cPoint
cHonest emptyOp       p sp = cNil p sp
cHonest seqOp         p (p₁ , p₂ , s) = cSplit3++ s
cHonest embOp         p sp = cStmt1 p sp
cHonest skipOp        cskip        _ = Eq.refl
cHonest skipOp        (cdecl _ _)  ()
cHonest skipOp        (cstore _ _) ()
cHonest skipOp        (cmalloc _)  ()
cHonest (declOp l x)  cskip        ()
cHonest (declOp l x)  (cdecl k y)  (el , ex) =
  eqAp₂ cdecl (sameLoc→Eq l k el) (sameVal→Eq x y ex)
cHonest (declOp l x)  (cstore _ _) ()
cHonest (declOp l x)  (cmalloc _)  ()
cHonest (storeOp l x) cskip        ()
cHonest (storeOp l x) (cdecl _ _)  ()
cHonest (storeOp l x) (cstore k y) (el , ex) =
  eqAp₂ cstore (sameLoc→Eq l k el) (sameVal→Eq x y ex)
cHonest (storeOp l x) (cmalloc _)  ()
cHonest (mallocOp x)  cskip        ()
cHonest (mallocOp x)  (cdecl _ _)  ()
cHonest (mallocOp x)  (cstore _ _) ()
cHonest (mallocOp x)  (cmalloc y)  e = Eq.ap cmalloc (sameVal→Eq x y e)

-- ==================================================================
-- §5  THE THEORY.
-- ==================================================================

cTheory : Theory ℓ-zero ℓ-zero ℓ-zero ℓ-zero ℓ-zero
cTheory = theory cSig cFib

-- ==================================================================
-- §6  THE MODEL: COMMANDS.
--
-- One interpretation per operation, and every right-hand side is a name
-- that already existed: `skip` and `⨟` from `ISA.Machine`, `Write` from
-- `Machine`, `Alloc` from `ISA.Toy`.  The model is TOTAL, which is the
-- reason it is relational -- see §C of the header.
--
-- Note `declOp` and `storeOp` receive the SAME interpretation.  That is
-- `Machine.noOwnership`, stated at the level of the model rather than at
-- a point: C's declaration of a fresh object and a store through an
-- alias are one operation with two spellings.
-- ==================================================================

cmdModel : Model cSig (ℓ-suc ℓ-zero)
cmdModel .carrier _ = Cmd
cmdModel .op emptyOp       _  = skip
cmdModel .op seqOp         m⃗ = m⃗ true ⨟ m⃗ false
cmdModel .op embOp         m⃗ = m⃗ tt
cmdModel .op skipOp        _  = skip
cmdModel .op (declOp l x)  _  = Write l x
cmdModel .op (storeOp l x) _  = Write l x
cmdModel .op (mallocOp x)  _  = Toy.Alloc x

-- ... and the promodel it points.  `Split` at every operation is "the
-- command REFINES the interpretation" -- lax, exactly as `ISA.Machine`'s
-- `CmdSplit`, of which `emptyOp`/`seqOp` here are literally the two
-- cases.
CmdCSplit : (o : COp) → Cmd → Type (ℓ-suc ℓ-zero)
CmdCSplit emptyOp       c = Lift (ℓ-suc ℓ-zero) (c ⊑ skip)
CmdCSplit seqOp         c = Σ[ c₁ ∈ Cmd ] Σ[ c₂ ∈ Cmd ] (c ⊑ c₁ ⨟ c₂)
CmdCSplit embOp         c = Σ[ d ∈ Cmd ] (c ⊑ d)
CmdCSplit skipOp        c = Lift (ℓ-suc ℓ-zero) (c ⊑ skip)
CmdCSplit (declOp l x)  c = Lift (ℓ-suc ℓ-zero) (c ⊑ Write l x)
CmdCSplit (storeOp l x) c = Lift (ℓ-suc ℓ-zero) (c ⊑ Write l x)
CmdCSplit (mallocOp x)  c = Lift (ℓ-suc ℓ-zero) (c ⊑ Toy.Alloc x)

CmdCParts : (o : COp) (c : Cmd) → CmdCSplit o c → (a : CAr o) → Cmd
CmdCParts emptyOp       c sp ()
CmdCParts seqOp         c (c₁ , c₂ , _) = boolΠ {M = λ _ → Cmd} c₁ c₂
CmdCParts embOp         c (d , _) _ = d
CmdCParts skipOp        c sp ()
CmdCParts (declOp _ _)  c sp ()
CmdCParts (storeOp _ _) c sp ()
CmdCParts (mallocOp _)  c sp ()

cmdCFib : Fibered cSig (ℓ-suc ℓ-zero) (ℓ-suc ℓ-zero)
cmdCFib .carrier _ = Cmd
cmdCFib .Split     = CmdCSplit
cmdCFib .parts     = CmdCParts

cmdPoint : LaxPoint cmdCFib
cmdPoint .op = cmdModel .op
cmdPoint .split emptyOp       m⃗ = lift (⊑-refl skip)
cmdPoint .split seqOp         m⃗ = m⃗ true , m⃗ false , ⊑-refl (m⃗ true ⨟ m⃗ false)
cmdPoint .split embOp         m⃗ = m⃗ tt , ⊑-refl (m⃗ tt)
cmdPoint .split skipOp        m⃗ = lift (⊑-refl skip)
cmdPoint .split (declOp l x)  m⃗ = lift (⊑-refl (Write l x))
cmdPoint .split (storeOp l x) m⃗ = lift (⊑-refl (Write l x))
cmdPoint .split (mallocOp x)  m⃗ = lift (⊑-refl (Toy.Alloc x))
cmdPoint .parts-split emptyOp       m⃗ = funExt λ ()
cmdPoint .parts-split seqOp         m⃗ =
  funExt (boolΠ {M = λ a → boolΠ {M = λ _ → Cmd} (m⃗ true) (m⃗ false) a ≡ m⃗ a}
                refl refl)
cmdPoint .parts-split embOp         m⃗ = funExt λ _ → refl
cmdPoint .parts-split skipOp        m⃗ = funExt λ ()
cmdPoint .parts-split (declOp _ _)  m⃗ = funExt λ ()
cmdPoint .parts-split (storeOp _ _) m⃗ = funExt λ ()
cmdPoint .parts-split (mallocOp _)  m⃗ = funExt λ ()

cSemTheory : Theory ℓ-zero ℓ-zero ℓ-zero (ℓ-suc ℓ-zero) (ℓ-suc ℓ-zero)
cSemTheory = theory cSig cmdCFib

-- ... AND IT IS NOT HONEST, unlike `cFib`.  A splitting recomposes only
-- to something the command REFINES, and the witness is the empty
-- command: it refines `skip`, so `⊗ˢ emptyOp` accepts it, but it is not
-- `skip`.  This is the promodel being strictly larger than the graph of
-- its point -- `Fibered`'s header calls `Bags` the standing example, and
-- commands are the second one.
private
  botCmd : Cmd
  botCmd _ _ = ⊥

  botLe : botCmd ⊑ skip
  botLe h h' ()

  coeAt : {c d : Cmd} → c Eq.≡ d → c [] [] → d [] []
  coeAt Eq.refl r = r

cmdNotHonest : Honest cmdPoint → ⊥
cmdNotHonest hon = coeAt (hon emptyOp botCmd (lift botLe)) Eq.refl

-- ==================================================================
-- §7  THE PASS.  `sem` AND `cStep`, AND NOTHING ELSE.
--
-- The carrier map is the machine: a statement goes to its command, a
-- program to the extension of that along the free monoid.  Both already
-- exist (`Machine.cStep`, `ISA.Program.sem`).
-- ==================================================================

semCOver : ReindexOver (idSigMor cSig) cFib cmdCFib
semCOver .homO stmt s = cStep s
semCOver .homO prog p = sem p

-- PRIMITIVE (phase 1): the unit law of `⨟`, which is what makes a
-- one-statement program its statement.  `sem (s ∷ []) = cStep s ⨟ skip`.
coeCmd : (c : Cmd) {h a b : Heap} → a Eq.≡ b → c h a → c h b
coeCmd c Eq.refl r = r

sem-one : (p : CProg) (sp : IsStmt1 p) → sem p ⊑ cStep (theStmt p sp)
sem-one []          ()
sem-one (s ∷ [])    _ h h' (h₁ , r , e) = coeCmd (cStep s) e r
sem-one (_ ∷ _ ∷ _) ()

-- PRIMITIVE (phase 1): the three leaf coercions.  Each is one `Eq.refl`
-- match; the recognisers of §2 supply the equations.
writeSame : (l k : Loc) (x y : Val) → l Eq.≡ k → x Eq.≡ y
          → Write k y ⊑ Write l x
writeSame l .l x .x Eq.refl Eq.refl = ⊑-refl (Write l x)

allocSame : (x y : Val) → x Eq.≡ y → Toy.Alloc y ⊑ Toy.Alloc x
allocSame x .x Eq.refl = ⊑-refl (Toy.Alloc x)

declPres : (l : Loc) (x : Val) (s : CStmt) → IsDecl l x s → cStep s ⊑ Write l x
declPres l x cskip        ()
declPres l x (cdecl k y)  (el , ex) =
  writeSame l k x y (sameLoc→Eq l k el) (sameVal→Eq x y ex)
declPres l x (cstore _ _) ()
declPres l x (cmalloc _)  ()

storePres : (l : Loc) (x : Val) (s : CStmt) → IsStore l x s → cStep s ⊑ Write l x
storePres l x cskip        ()
storePres l x (cdecl _ _)  ()
storePres l x (cstore k y) (el , ex) =
  writeSame l k x y (sameLoc→Eq l k el) (sameVal→Eq x y ex)
storePres l x (cmalloc _)  ()

mallocPres : (x : Val) (s : CStmt) → IsMalloc x s → cStep s ⊑ Toy.Alloc x
mallocPres x cskip        ()
mallocPres x (cdecl _ _)  ()
mallocPres x (cstore _ _) ()
mallocPres x (cmalloc y)  e = allocSame x y (sameVal→Eq x y e)

skipPres : (s : CStmt) → IsSkip s → cStep s ⊑ skip
skipPres cskip        _ = ⊑-refl skip
skipPres (cdecl _ _)  ()
skipPres (cstore _ _) ()
skipPres (cmalloc _)  ()

-- SPLIT PRESERVATION AT EVERY OPERATION.
--
-- `seqOp` is `ISA.Program.homSplit3` verbatim -- the two-clause monoid
-- homomorphism, which is the only Hoare-relevant induction in the whole
-- ISA layer and was proved once for every instruction set.  `emptyOp` is
-- `semNil`.  The five remaining clauses are §7's coercions, and each is
-- a coercion because a nullary operation has nothing to preserve.
semCPres : (o : COp) → SplitPresAtOver semCOver o
semCPres emptyOp .homSplitO p sp = lift (semNil p sp)
semCPres emptyOp .homPartsO p sp ()
semCPres seqOp .homSplitO p (p₁ , p₂ , s) = sem p₁ , sem p₂ , homSplit3 s
semCPres seqOp .homPartsO p (p₁ , p₂ , s) =
  boolΠ {M = λ a → boolΠ {M = λ _ → Cmd} (sem p₁) (sem p₂) a
                   Eq.≡ sem (boolΠ {M = λ _ → CProg} p₁ p₂ a)}
        Eq.refl Eq.refl
semCPres embOp .homSplitO p sp = cStep (theStmt p sp) , sem-one p sp
semCPres embOp .homPartsO p sp _ = Eq.refl
semCPres skipOp .homSplitO s sp = lift (skipPres s sp)
semCPres skipOp .homPartsO s sp ()
semCPres (declOp l x) .homSplitO s sp = lift (declPres l x s sp)
semCPres (declOp l x) .homPartsO s sp ()
semCPres (storeOp l x) .homSplitO s sp = lift (storePres l x s sp)
semCPres (storeOp l x) .homPartsO s sp ()
semCPres (mallocOp x) .homSplitO s sp = lift (mallocPres x s sp)
semCPres (mallocOp x) .homPartsO s sp ()

-- THE PASS.  "The semantics of the C fragment is sound" IS "the
-- semantics is a pass", in `Reindex.Pass`'s sense, so `_⨟P_`, `Chain`
-- and `composite` all apply to it.
cPass : Pass cTheory cSemTheory
cPass .sigOf  = idSigMor cSig
cPass .mapOf  = semCOver
cPass .presOf = semCPres

-- the interpretation, named: `⟦ p ⟧ᶜ` is the pass at the sort `prog`
⟦_⟧ᶜ : CProg → Cmd
⟦ p ⟧ᶜ = cPass .mapOf .homO prog p

⟦_⟧ˢ : CStmt → Cmd
⟦ s ⟧ˢ = cPass .mapOf .homO stmt s

-- ... and it really is `sem`/`cStep`, on the nose
_ : (p : CProg) → ⟦ p ⟧ᶜ ≡ sem p
_ = λ p → refl

_ : (s : CStmt) → ⟦ s ⟧ˢ ≡ cStep s
_ = λ s → refl

-- ==================================================================
-- §8  `evalC` IS THIS MODEL'S INTERPRETATION, AND `runC` IS A STATEMENT
--     ABOUT IT.
--
-- `evalC` is the FUNCTIONAL reading of the model, available exactly on
-- `Dets` -- the fragment without `cmalloc`, which has no functional
-- reading at all because it does not name its address.  `evalC-sound`
-- (already proved in `Machine`) says the function computes a run of the
-- model; nothing new is needed.
-- ==================================================================

-- THE INTERPRETATION THEOREM.  For a deterministic program, the heap
-- `evalC` computes is a run of the model.
evalIsModel : (p : CProg) → Dets p → (h : Heap) → ⟦ p ⟧ᶜ h (evalC p h)
evalIsModel = evalC-sound

-- ... and the three homomorphism equations that say `evalC` is THE
-- interpretation and not merely A run: it is the extension of `evalS`
-- along the free monoid, one equation per operation of §1 that the
-- deterministic fragment admits.
evalHomEmpty : (p : CProg) → PT.IsNil p → (h : Heap) → evalC p h Eq.≡ h
evalHomEmpty []      _  h = Eq.refl
evalHomEmpty (_ ∷ _) () h

evalHomEmb : (p : CProg) (sp : IsStmt1 p) (h : Heap)
           → evalC p h Eq.≡ evalS (theStmt p sp) h
evalHomEmb []          () h
evalHomEmb (s ∷ [])    _  h = Eq.refl
evalHomEmb (_ ∷ _ ∷ _) () h

-- `seqOp`: this is the free monoid's universal property for `evalC`,
-- and its induction is `cSplit3++`'s -- reused, not repeated.
evalHomSeq : {p₁ p₂ p : CProg} → PT.Split3 p₁ p₂ p → (h : Heap)
           → evalC p h Eq.≡ evalC p₂ (evalC p₁ h)
evalHomSeq PT.nil      h = Eq.refl
evalHomSeq (PT.cons s) h = evalHomSeq s (evalS _ h)

-- the leaf equations, all `Eq.refl`: `Machine.evalS` IS `cmdModel`'s
-- interpretation read functionally
evalHomDecl : (l : Loc) (x : Val) (h : Heap)
            → evalS (cdecl l x) h Eq.≡ (h ++h single l x)
evalHomDecl l x h = Eq.refl

evalHomStore : (l : Loc) (x : Val) (h : Heap)
             → evalS (cstore l x) h Eq.≡ (h ++h single l x)
evalHomStore l x h = Eq.refl

evalHomSkip : (h : Heap) → evalS cskip h Eq.≡ h
evalHomSkip h = Eq.refl

-- ==================================================================
-- ... AND `runC`, REPACKAGED.
--
--     Codegen.runC : evalC (compileC u) [] Eq.≡ layout u
--
-- becomes: the C emitted for `u`, READ IN THE MODEL, relates the empty
-- heap to `u`'s layout.  Nothing is reproved -- `evalIsModel` puts the
-- computed heap into the model and `runC` names it.
--
-- READ §E OF THE HEADER BEFORE QUOTING THIS.  It is a theorem about
-- ALLOCATION.  `compileC` takes a USAGE, so by
-- `Compile.Semantics.Simulation.noBlindBackend` no computational
-- correctness theorem is available for this backend at all.
-- ==================================================================

allocSpec : (u : L.Usage) → ⟦ CG.compileC u ⟧ᶜ [] (L.layout u)
allocSpec u =
  coeCmd ⟦ CG.compileC u ⟧ᶜ (CG.runC u)
         (evalIsModel (CG.compileC u) (CG.detCode 0 u) [])

-- at a TERM, where `compileTm u t .fst` is the emitted C.  The two
-- arguments `u` and `t` and the single right-hand side are exactly the
-- limitation: `t` is not consulted.
allocSpecTm : (u : L.Usage) (t : L.Tm u)
            → ⟦ CG.compileTm u t .fst ⟧ᶜ [] (L.layout u)
allocSpecTm u t = allocSpec u

-- ==================================================================
-- §9  THE NEGATIVE HALF.  SEQUENCING IN C IS NOT SEPARATION.
--
-- This is why §6's model is relational commands and not heaps, and it is
-- `Machine.noOwnership` in the theory's own language.
--
-- `Machine.aliasC` splits in `cFib` -- `PT.splitAll` gives the canonical
-- `seqOp` splitting into its two statements, and the C theory has no
-- means to object, because the two statements have the same denotation.
-- The footprints of the two halves are both `single 0 v1`, and a
-- `heapFib` splitting demands `_#_`, which those two heaps do not have.
-- So `objects` is not a map of promodels `cFib → heapFib` at `seqOp`.
-- ==================================================================

aliasSplit : CSplit seqOp aliasC
aliasSplit =
  (cdecl 0 v1 ∷ []) , (cstore 0 v1 ∷ []) , PT.splitAll _ _

-- the two halves' footprints COLLIDE
noSeqSeparation :
    ( objects (CParts seqOp aliasC aliasSplit true)
    # objects (CParts seqOp aliasC aliasSplit false) )
  → ⊥
noSeqSeparation = #-same-loc 0 v1 v1

-- ... and the same splitting IS carried by the pass, into `cmdCFib`,
-- with no disjointness asked for.  The contrast is the content.
aliasSem : CmdCSplit seqOp ⟦ aliasC ⟧ᶜ
aliasSem = semCPres seqOp .homSplitO aliasC aliasSplit

-- ==================================================================
-- §10  OBSERVATION.  `refl` lines only.
-- ==================================================================

-- the recognisers compute: a splitting is a nest of `tt`
_ : CSplit (declOp 0 v1) (cdecl 0 v1) ≡ (Unit × Unit)
_ = refl

_ : cPoint .split (declOp 3 v1) (λ ()) ≡ (tt , tt)
_ = refl

-- the syntax promodel's point is juxtaposition
_ : cOp seqOp (boolΠ {M = λ _ → CProg} (cdecl 0 v1 ∷ []) (cdecl 1 v1 ∷ []))
  ≡ cdecl 0 v1 ∷ cdecl 1 v1 ∷ []
_ = refl

-- honesty computes at a concrete splitting
_ : cHonest seqOp aliasC aliasSplit ≡ Eq.refl
_ = refl

-- the model, at the emitted program: `evalC` computes the run
_ : evalC (CG.compileC (true ∷ true ∷ [])) [] ≡ (0 , v1) ∷ (1 , v1) ∷ []
_ = refl

-- ... AND THE REPACKAGED THEOREM REDUCES.  `allocSpec u` is a RUN of
-- the model, so its normal form is the trace: the intermediate heap
-- after each declaration, with `Eq.refl` at every step.  That it
-- evaluates is the model-level version of `Codegen`'s `runC u ≡ Eq.refl`.
_ : allocSpec (true ∷ true ∷ [])
  ≡ ( single 0 v1
    , Eq.refl
    , ( (0 , v1) ∷ (1 , v1) ∷ [] , Eq.refl , Eq.refl ) )
_ = refl

-- the dead middle position leaves an ADDRESS GAP in the trace, too
_ : allocSpec (true ∷ false ∷ true ∷ [])
  ≡ ( single 0 v1
    , Eq.refl
    , ( (0 , v1) ∷ (2 , v1) ∷ [] , Eq.refl , Eq.refl ) )
_ = refl

-- ==================================================================
-- THE LIMITATION, VISIBLE.  Two DIFFERENT terms, one program, one
-- theorem -- and `allocSpec` is satisfied by both.  See §E.
-- ==================================================================

_ : CG.compileTm [] L.idLin .fst ≡ []
_ = refl

_ : CG.compileTm [] L.selfApp .fst ≡ []
_ = refl

_ : allocSpecTm [] L.idLin ≡ allocSpecTm [] L.selfApp
_ = refl
