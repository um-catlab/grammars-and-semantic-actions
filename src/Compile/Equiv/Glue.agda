{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  TWO BACKENDS, ONE GLUING -- AND WHERE THE LOGICAL RELATION ACTUALLY
  HAS TO LIVE.

  ------------------------------------------------------------------
  §0  THE TWO PROMODELS, AND WHY THEY ARE THESE TWO
  ------------------------------------------------------------------

  `Compile/LinToRust/Theory.agda` §0 settles the design question once
  and for all: the carrier of a target theory is the RESOURCE, never
  the SYNTAX, because a `⊢`-term over the syntax preserves the
  expression and the calculus collapses to "predicates on a fixed
  term".  This file takes that verdict as given and applies it to BOTH
  backends at once.

    * THE CLOSURE-CONVERSION BACKEND'S PROMODEL IS `linFib` ITSELF.
      This is not a choice -- it is a reading.  `Compile/ClosureConv/
      IR.agda` indexes the IR by the SOURCE usage (`IR : Usage → Type`)
      and `Convert.agda`'s headline is `convertT : TmG ⊢ IRG`.  So
      closure conversion does not move the carrier at all: it is a pass
      whose carrier map is the identity, and `IRG` is a GRAMMAR over
      the source's own promodel.  (That is the whole content of
      "closure conversion captures exactly the free variables": it is
      the type, not a lemma.)

    * THE RUST BACKEND'S PROMODEL IS `rustFib`, carrier `Own = List
      Ident`, over `rustSig` -- with the caveat that `rustSig` is not
      `monoidSig`.  `Theory.agda` bridges them with `φ : SigMor
      monoidSig rustSig` (`appop ↦ callOp`, `nilop ↦ ctorOp cA`), so
      §2 below restricts `rustFib` ALONG `φ` to `rustMon`, a promodel
      over the monoid signature.  Nothing is lost: `φ .onAr appop` is
      the identity on `Bool` and `φ .onAr nilop` is a map out of `⊥`,
      which is exactly the `ArSection` that `rustReflective .secOf`
      already provides.

    * THE CORRELATION IS THE GRAPH OF THE PASS.

          graphR tt u l  =  l Eq.≡ Names 0 u

      i.e. "the Rust expression owns exactly the names the source usage
      licenses".  `Names 0 : Usage → Own` is `rustPass`'s carrier map,
      so `graphR` is not an invention: it is `namesOver .homO` read as a
      relation.

  WHY THE GRAPH AND NOT SOMETHING FINER.  A correlation is free to be
  anything (`Corr` asks no law).  The graph is the one that makes the
  glue say what the pair of backends means:

      the glued carrier is a source usage TOGETHER WITH the Rust
      resource it forces, so a type over the glue is a pair of
      payloads AT CORRESPONDING RESOURCES, and

          IRG ⊛ UsesG   =   pull₁ IRG & pull₂ UsesG

      is exactly "an IR expression and a Rust expression, compiled
      from the same source usage".  That grammar is the PAIR OF
      IMPLEMENTATIONS the hypothesis under test asks for, and `pairT`
      (§6) is the term producing it.

  ------------------------------------------------------------------
  §0.1  WHAT IS PROVED HERE
  ------------------------------------------------------------------

      determined    : GL.Determined                       (§3)  PROVED
      noCoherent    : GL.Coherent → ⊥                     (§4)  REFUTED
      pairIsPull    : GS.pull (A ⊛ B) ≡ (A & RP.pullO B)  (§5)  refl
      pairT         : TmG ⊢ GS.pull (IRG ⊛ UsesG)         (§6)
      resourceAgree : Uses (compileRust t) (Names 0 u)    (§6)  a PROJECTION
      relConvert    : RelE (tableOf t) emptyF t (convert t)  (§7)
      agree         : (t : Tm []) → Agree t               (§7)

  NO HOLES AND NO POSTULATES.  `relConvert` -- the fundamental lemma
  for the closure-conversion backend, which the development did not
  have (`Correct.squareProg` took it as a hypothesis) -- is proved here
  in §7, and it is what makes `agree` unconditional.

  `Determined` is the useful one, and it holds for the sharpest
  possible reason: it IS `rustPass .presOf`, field for field.  A source
  splitting determines the Rust one because the pass preserves
  splittings, and `Gluing.agda`'s reading of `Determined` -- "the right
  factor is an ATTRIBUTE of the left" -- is precisely the sentence
  `Theory.agda` §0 was making about ownership.  Consequence
  (`liftsSource`): `π₁` reflects splittings, so `pull⊗₁` applies and
  EVERY source program lifts into the glue, landing where it can be
  paired with Rust data.  Nothing about the Rust backend has to be
  re-proved to run a source program over the pair.

  `Coherent` FAILS, and the witness is one line: at the source usage
  `true ∷ true ∷ []` take the source splitting that sends position 0
  left and position 1 right, and take the Rust interleaving that sends
  `fre 0` RIGHT and `fre 1` LEFT.  Both are legitimate splittings of
  related wholes; their parts are not related, because `fre 1 ∷ []` is
  not `Names 0 (true ∷ false ∷ []) = fre 0 ∷ []`.  So `zip` is lax and
  not strong, and the moral is exact:

      A PAIR OF IMPLEMENTATIONS CANNOT BE TAKEN APART INDEPENDENTLY.
      The two backends' resource decompositions agree only because one
      DETERMINES the other, so any relation between them must be built
      by recursion on the SOURCE -- never on either target.

  Which is what both existing square proofs already do
  (`Relational/Square.square` and `ClosureConv/Correct.square` are both
  structural in the SOURCE derivation).  §4 is the reason they have to
  be.

  ------------------------------------------------------------------
  §0.2  THE VERDICT ON "A LOGICAL RELATION ONLY AT THE FINAL STAGE"
  ------------------------------------------------------------------

  The hypothesis was: relate the two backends at the final IR, map that
  input to a pair of implementations, and the earlier passes need
  nothing.  Three findings, in order of how much they cost.

  (1) THERE IS NO SHARED FINAL IR.  The two backends branch at the
      SOURCE.  `compileRust : Tm u → RExpr` goes straight from the
      linear λ-calculus to Rust; `convert : Tm u → IR u` goes from the
      same place into the closure-converted IR (and only then to
      `CProg`/ARM).  The last representation they share is `Tm u`.  So
      the relation is at the FIRST stage, not the final one -- which is
      good news for the hypothesis in one respect (there are no earlier
      passes to break it) and fatal in another (see (3)).

  (2) AT THAT STAGE THE FRAMEWORK IS AS STRONG AS IT CAN BE.
      `Determined` holds, so the source's whole multiplicative fragment
      transports into the glue.  This is the part of the hypothesis
      that is simply TRUE, and §3/§5/§6 are its proof.

  (3) BUT THE RELATION DOES NOT COMPOSE TO AN EQUATION, AND CANNOT.
      c-c-l's `Gluing/BiCartesianClosedCategory/` gets "the two
      implementations are the same" out of a logical relation by
      IDENTITY EXTENSION: at a CLOSED type built only from
      `⊤ ⊥ × + ⇒`, the relation is the identity, so relatedness at the
      observable type IS equality (`IdentityExtension.agda`,
      `StackParametricity.stack-representation-independence`).  The
      induction there has no base case because closed types contain no
      base type.

      Here the observable type IS a base type.  The Rust answer is an
      `RExpr`; the closure-conversion answer is a `Val` carrying a code
      pointer into a table.  There is no type constructor between them
      and the source, so there is no identity-extension step to run,
      and this is not a gap in the proof -- it is refuted twice over:

          Relational/Refutation.agda  -- the Rust square is false
                                         (binder levels move)
          ClosureConv/Correct         -- `noNoseSquare`, and worse,
                                         `valuesCollapse`: the CC
                                         observation separates NOTHING

      So the strongest true statement is §7's `Agree`: the two answers
      REALISE THE SAME SOURCE VALUE, through two incomparable
      realisation relations (`Rel ν`, quotienting binder names;
      `RelV T`, quotienting code-table indices).  "The same answer" is
      a span, not an equation.

  (4) AND ONE PASS DOES BREAK LOCALITY, WHICH IS THE PART OF THE
      HYPOTHESIS THAT IS OUTRIGHT FALSE.  `Convert.convApp` offsets the
      right premise's block indices by `length` of the left premise's
      table.  A block index is therefore a fact about the WHOLE
      PROGRAM, so the closure-conversion realisation relation is
      indexed by a `Table` (`RelE T σ t e`) that only exists once the
      top-level compilation is finished.  The relation cannot be
      assembled locally at the branch point and then transported; it
      has to be threaded from the top, and the fundamental lemma
      (`relConvert`, §7) needs `IR.at-++ˡ`/`at-++ʳ` -- table weakening
      -- for exactly that reason.  Closure conversion is the pass that
      breaks "only at the final stage".

      By contrast the Rust backend's own instability (binder levels)
      IS local: `Relational.Base.relCompile` is a plain induction with
      the name assignment as a parameter, and it is proved.

  ------------------------------------------------------------------
  §0.3  WHAT THIS FILE DOES *NOT* DEPEND ON
  ------------------------------------------------------------------

  `Compile/ClosureConv/ARMCorrect.agda`'s `simulate` is open.  Nothing
  here uses it: §7 stops at `Ev`, the IR's own big-step semantics,
  which is the semantics `Correct.obs` runs.  Carrying the statement
  down to `ARM.answerT` would need `simulate`, and that is said and not
  assumed.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1: §2 builds a promodel (matches on `MonOp`), §3/§4 build and
  refute splitting conditions, §7 is metatheory.  §5 and §6 are phase
  2 -- `&-I` and `pullTerm`, no match on a carrier.
-}
open import Cubical.Foundations.Prelude

module Compile.Equiv.Glue where

open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; +-zero; +-suc; +-assoc)
open import Cubical.Data.List using (List; []; _∷_; _++_; length)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Theories.Monoid
open import TheoryGrammar.CarrierMap
open import TheoryGrammar.Reindex.Base
open import TheoryGrammar.ChangeOfTheory using (onOp)
open import TheoryGrammar.Gluing

-- THE SOURCE, AND THE CLOSURE-CONVERSION BACKEND.  Unqualified: this
-- file's ambient theory is `linFib`, and `Correct` re-exports it
-- (`Convert` → `Opt` → `LinLam.Syntax`) together with `IR`, `convert`,
-- `tableOf`, `RelE`, `RelV`, `square`, `squareProg`.
open import Compile.ClosureConv.Correct

-- THE RUST BACKEND.  Qualified throughout -- `Theory` has its own
-- `ClosedTm`, and `Codegen` its own `Ident`/`Same`.
import Compile.LinToRust.Theory   as RT
import Compile.LinToRust.Codegen  as RC
import Compile.LinToRust.Syntax   as RS
import Compile.Relational.Base    as R
import Compile.Semantics.CBV      as S

-- ==================================================================
-- §2  THE RUST PROMODEL, OVER THE MONOID SIGNATURE.
--
-- `rustFib` restricted along `φ`.  `ChangeOfTheory.restrict` does this
-- for a `Model`; a `Fibered` restriction additionally needs the arity
-- map to go FORWARDS, which for this `φ` it does (`onAr appop` is the
-- identity on `Bool`, `onAr nilop` is out of `⊥`) -- so the two clauses
-- below are the restriction, written out.
--
-- PRIMITIVE (phase 1).
-- ==================================================================

rustMon : Fibered monoidSig ℓ-zero ℓ-zero
rustMon .carrier _     = RT.Own
rustMon .Split o l     = RT.rustFib .Split (RT.φ .onOp o) l
rustMon .parts nilop l sp ()
rustMon .parts appop l sp a = RT.rustFib .parts RT.callOp l sp a

-- ==================================================================
-- §2.1  THE CORRELATION: THE GRAPH OF `rustPass`'s CARRIER MAP.
-- ==================================================================

graphR : Corr linFib rustMon ℓ-zero
graphR _ u l = l Eq.≡ RC.Names 0 u

module GL = Glue linFib rustMon graphR

-- the glued carrier, for reading: a usage, the Rust resource it
-- forces, and the fact that it does.
GlueCarrier : Type₀
GlueCarrier = GL.glue .carrier tt

_ : GlueCarrier ≡ (Σ[ u ∈ Usage ] Σ[ l ∈ RT.Own ] (l Eq.≡ RC.Names 0 u))
_ = refl

-- ==================================================================
-- §3  `Determined` HOLDS, AND IT IS `rustPass .presOf` VERBATIM.
--
-- Match the relatedness witness as `Eq.refl` -- the right carrier is
-- then literally `Names 0 u` and there is nothing to transport.  At
-- `appop` the displayed splitting is `presCall` and the relatedness of
-- the parts is `presCall .homPartsO`, which is `Codegen.ilvNames`; at
-- `nilop` it is `presCtor`, whose arity is `⊥` so the second component
-- is vacuous.
--
-- This is the sharpest form of the claim that the Rust resource is an
-- ATTRIBUTE of the linear usage: no new proof, only a reindexing of
-- the one `Theory.agda` §5 already gave.
-- ==================================================================

determined : GL.Determined
determined nilop (u , _ , Eq.refl) sp =
  RT.presCtor .homSplitO u sp , λ ()
determined appop (u , _ , Eq.refl) sp =
  RT.presCall .homSplitO u sp , RT.presCall .homPartsO u sp

-- THE PAYOFF.  `π₁` reflects splittings, so `pull⊗₁` is available:
-- every source `⊗ˢ` transports into the glue and every source program
-- lifts, landing paired with Rust data.
reflectsSource : (o : MonOp) → GL.Reflects₁ o
reflectsSource = GL.determined→reflects determined

liftsSource : (B : (a : MonAr appop) → Ctx)
            → GL.pull₁ (⊗ˢ appop B) GL.G.⊢ GL.G.⊗ˢ appop (λ a → GL.pull₁ (B a))
liftsSource B = GL.pull⊗₁ appop (reflectsSource appop) {B = B}

-- ==================================================================
-- §4  `Coherent` FAILS, WITH A WITNESS.
--
-- House style is `Compile/LinToISA/NoTextPres.agda`: name the two
-- splittings, name the position they disagree at, and let a
-- `Unit`/`⊥`-valued predicate do the discrimination so that nothing is
-- transported.
--
-- The source usage `true ∷ true ∷ []` has names `fre 0 ∷ fre 1 ∷ []`.
-- Split the SOURCE so that position 0 goes left; split the RUST names
-- so that `fre 0` goes RIGHT.  Both are splittings of related wholes.
-- Their left parts are `true ∷ false ∷ []` and `fre 1 ∷ []`, and
-- `Names 0 (true ∷ false ∷ [])` is `fre 0 ∷ []`.
-- ==================================================================

twoU : Usage
twoU = true ∷ true ∷ []

-- the names really are what one expects
_ : RC.Names 0 twoU Eq.≡ (RS.fre 0 ∷ RS.fre 1 ∷ [])
_ = Eq.refl

srcSplit : linFib .Split appop twoU
srcSplit = (true ∷ false ∷ []) , (false ∷ true ∷ []) , uleft (uright unil)

-- the SWAPPED interleaving: `fre 0` to the right, `fre 1` to the left
swapSplit : rustMon .Split appop (RC.Names 0 twoU)
swapSplit = (RS.fre 1 ∷ []) , (RS.fre 0 ∷ []) , RC.iright (RC.ileft RC.inil)

gluePt : GlueCarrier
gluePt = twoU , RC.Names 0 twoU , Eq.refl

-- PRIMITIVE (phase 1): `Unit`/`⊥`-valued, in the style of
-- `Theory.IsNilI`, so the refutation is a `transport` of `tt` and no
-- path is ever formed.
isFre1 : RT.Own → Type₀
isFre1 (RS.fre (suc zero) ∷ []) = Unit
isFre1 _                        = ⊥

noCoherent : GL.Coherent → ⊥
noCoherent c = Eq.transport isFre1 (c appop gluePt srcSplit swapSplit true) tt

-- ... and `Determined` is unharmed, so `Gluing.coherent→determined` is
-- strictly weaker than §3: the implication does not run backwards.

-- ==================================================================
-- §5  THE SECTION, AND WHAT THE GLUE IS IN THE OLD LANGUAGE.
--
-- The correlation is a GRAPH, so the left projection has a section:
-- every usage is related to exactly one resource.  Reindexing along it
-- turns a glued grammar back into a `Ctx`, and the identification is
-- definitional:
--
--     GS.pull (A ⊛ B)  ≡  A & RP.pullO B
--
-- i.e. THE GLUE ALONG THE GRAPH OF THE PASS REPRODUCES, ON THE NOSE,
-- THE PULLBACK-ALONG-THE-PASS THAT `Theory.agda` §6 ALREADY USED
-- (`objIsPull`).  What is new is that the glued version carries a
-- `⊗`-structure: `zip` (unconditional) and `unzip` (only under
-- `Coherent`, hence -- by §4 -- not here).
-- ==================================================================

graphSec : Reindex linFib GL.glue
graphSec .hom _ u = u , RC.Names 0 u , Eq.refl

module GS = Along graphSec
module RP = AlongOver RT.namesOver

pairIsPull : (A : Ctx) (B : RT.RustG)
           → GS.pull (A GL.⊛ B) ≡ (A & RP.pullO {s = tt} B)
pairIsPull A B = refl

-- ==================================================================
-- §6  THE PAIR OF IMPLEMENTATIONS, AS A TERM.
--
-- `PairG` is the hypothesis's "pair of implementations, one in each
-- backend" -- and it is a single grammar over a single carrier, which
-- is the point of gluing rather than of taking a metalanguage product.
-- `pairT` is the two compilers run together; it is `&-I` of two terms
-- that already exist, and nothing about either backend is re-proved.
--
-- Phase 2.
-- ==================================================================

PairG : GL.G.TheoryTy ℓ-zero tt
PairG = IRG GL.⊛ RT.UsesG

pairT : TmG ⊢ GS.pull PairG
pairT = &-I convertT RT.compileG

-- the two components really are the two backends
pairLeft : (u : Usage) (t : Tm u) → pairT u t .fst ≡ convert t
pairLeft u t = refl

pairRight : (u : Usage) (t : Tm u) → pairT u t .snd .fst ≡ RC.compileRust t
pairRight u t = refl

-- ------------------------------------------------------------------
-- THE PART OF "THE TWO BACKENDS AGREE" THAT NEEDS NO LOGICAL RELATION
-- AT ALL, AND IS THEREFORE COMPLETE.
--
-- `pairT` lands in a grammar over the GLUE, so its Rust component owns
-- exactly the names its IR component's usage licenses.  There is no
-- proof to give: the index is the proof, and this is a projection.
-- Compare `Theory.agda` §0 -- "ownership-correctness is FREE rather
-- than a separate obligation" -- now stated across BOTH backends.
-- ------------------------------------------------------------------
resourceAgree : (u : Usage) (t : Tm u)
              → RC.Uses (RC.compileRust t) (RC.Names 0 u)
resourceAgree u t = pairT u t .snd .snd

-- ... and `zip` is available unconditionally, so the pair grammar is
-- LAX MONOIDAL for the source's own tensor.  (By §4 it is not strong.)
irPair : (a : MonAr appop) → Ctx
irPair = boolΠ {M = λ _ → Ctx} IRG IRG

usesPair : (a : MonAr appop) → RT.RustG
usesPair = boolΠ {M = λ _ → RT.RustG} RT.UsesG RT.UsesG

zipPair : GL.G.⊗ˢ appop (λ a → irPair a GL.⊛ usesPair a)
          GL.G.⊢ ((GL.F₁.⊗ˢ appop irPair) GL.⊛ (GL.F₂.⊗ˢ appop usesPair))
zipPair = GL.zip appop irPair usesPair

-- ==================================================================
-- §7  THE EQUIVALENCE THEOREM.
--
-- "The two backends produce the same answer", in the only form the
-- refutations leave available: BOTH ANSWERS REALISE THE SAME SOURCE
-- VALUE.  A span, not an equation -- see §0.2(3).
--
-- The Rust half is complete and already proved:
--     RT.progress      -- the emitted Rust evaluates
--     RT.runsRealises  -- and its value realises `S.evalV t`
--
-- The closure-conversion half is `Correct.squareProg`, which is also
-- proved -- but it takes the FUNDAMENTAL LEMMA as a hypothesis, and
-- that lemma was not in the development.  `relConvert` supplies it.
-- ==================================================================

-- ------------------------------------------------------------------
-- THE FUNDAMENTAL LEMMA, AND WHAT IT COSTS.
--
-- `relConvert` is closure conversion's `Relational.Base.relCompile`.
-- It is harder here for the reason §0.2(4) names: `convT` threads a
-- block counter and `convApp` offsets the right premise, so the
-- statement cannot be about `tableOf t` -- it has to be about an
-- ARBITRARY whole-program table into which this subterm's blocks have
-- been placed at a known offset.  `Fits` is that hypothesis, and the
-- three uses of `IR.at-++ˡ` / `at-++ʳ` / `athere` below are the whole
-- content: closure conversion's numbering is GLOBAL, so its logical
-- relation cannot be assembled locally.
--
-- Two things do NOT cost anything, and it is worth naming them.  The
-- frame `σ` is arbitrary -- nothing has been substituted yet at
-- compile time, so `rcap` never fires and `rvar` relates the two sides
-- by `Eq.refl`.  And the splitting is carried over verbatim
-- (`convApp` reuses the source's `Use⊎`), so `rapp`'s two splittings
-- coincide here even though the relation allows them to differ.
-- ------------------------------------------------------------------

private
  -- transport of a lookup along an arithmetic identity.  The only
  -- transport in the section, and it never has to compute: it feeds a
  -- premise, it is not projected from.
  atCoe : {T : Table} {i j : ℕ} {sh : Usage} {b : IR (true ∷ sh)}
        → i ≡ j → At T i sh b → At T j sh b
  atCoe {T = T} {sh = sh} {b = b} p a =
    Eq.transport (λ z → At T z sh b) (Eq.pathToEq p) a

-- "the blocks `Ts` sit inside `T` starting at index `n`"
Fits : Table → ℕ → Table → Type₀
Fits T n Ts = {i : ℕ} {sh : Usage} {b : IR (true ∷ sh)}
            → At Ts i sh b → At T (n + i) sh b

-- PRIMITIVE (phase 1): structural on the SOURCE term -- which is the
-- §4 moral in action.  `convT` is `foldTm`, so each clause reduces and
-- the recursion is the source's own.
relConvG : {u : Usage} (t : Tm u) (T : Table) (n : ℕ) (σ : Frame)
         → Fits T n (convT u t n .snd)
         → RelE T σ t (convT u t n .fst)

relConvG (tvar s) T n σ h = rvar s s Eq.refl

relConvG (tapp {u₁} {u₂} sp a b) T n σ h =
  rapp (relConvG a T n σ hL) (relConvG b T m σ hR)
  where
  Ta : Table
  Ta = convT u₁ a n .snd

  m : ℕ
  m = n + length Ta

  hL : Fits T n Ta
  hL x = h (at-++ˡ _ x)

  hR : Fits T m (convT u₂ b m .snd)
  hR {i} x = atCoe (+-assoc n (length Ta) i) (h (at-++ʳ Ta x))

relConvG {u} (tlam b) T n σ h =
  rclos at (relConvG b T (suc n) (callFrame u (capVals σ (idCap u)) junk) hB)
  where
  r : IR (true ∷ u) × Table
  r = convT (true ∷ u) b (suc n)

  at : At T n u (r .fst)
  at = atCoe (+-zero n) (h ahere)

  hB : Fits T (suc n) (r .snd)
  hB {i} x = atCoe (+-suc n i) (h (athere x))

-- ... and at the top the offset is `0`, so `Fits` is the identity.
relConvert : (t : Tm []) → RelE (tableOf t) emptyF t (convert t)
relConvert t = relConvG t (tableOf t) 0 emptyF (λ x → x)

-- ------------------------------------------------------------------
-- THE STATEMENT.
-- ------------------------------------------------------------------

-- "the two backends' answers denote the same thing": a source value
-- realised by both.  Composite of the two realisation relations, and
-- necessarily a span -- there is no map between `RExpr` and `Val`.
Same : Tm [] → RS.RExpr → Val → Type₀
Same t wR wC =
  Σ[ v ∈ Tm [] ] (R.Rel (RC.nameOf 0) v wR × RelV (tableOf t) v wC)

Agree : Tm [] → Type₀
Agree t =
  Σ[ wR ∈ RS.RExpr ] Σ[ wC ∈ Val ]
    ( (RC.compileRust t RC.⇓ wR)                    -- the Rust backend runs
    × Ev (tableOf t) emptyF (convert t) wC          -- the CC backend runs
    × Same t wR wC )                                -- and the answers agree

-- ------------------------------------------------------------------
-- THE THEOREM.  The witnessing source value is `S.evalV t` on BOTH
-- sides -- which is the content: the span is not merely inhabited, its
-- apex is the source's own answer.
-- ------------------------------------------------------------------
agree : (t : Tm []) → Agree t
agree t =
    RT.progress t .fst
  , cc .fst
  , RT.progress t .snd
  , cc .snd .fst
  , S.evalV t
  , RT.runsRealises t (RT.progress t .fst) (RT.progress t .snd)
  , cc .snd .snd
  where
  cc : Σ[ w ∈ Val ] (Ev (tableOf t) emptyF (convert t) w
                     × RelV (tableOf t) (S.evalV t) w)
  cc = squareProg t (relConvert t)

-- ==================================================================
-- §8  OBSERVATION.  `refl` lines only.
-- ==================================================================

-- THE TWO ANSWERS, FOR `(λx.x)(λx.x)`.  This is the whole motivation
-- for §7 being a span: the two backends' answers are not merely
-- different values of one type, they are values of DIFFERENT TYPES,
-- and even their tags disagree with the source's.
_ : RT.progress selfApp .fst Eq.≡ RS.rClos 0 (RS.rVar (RS.bnd 0))
_ = Eq.refl

_ : obs selfApp Eq.≡ just (clos 1 [])
_ = Eq.refl

-- ... and `idLin`, which IS `selfApp`'s value, observes as `clos 0 []`
-- on the CC side (`Correct.noNoseSquare`) while the Rust side is
-- stable.  The Rust answer for the VALUE is the same expression:
_ : RT.progress idLin .fst Eq.≡ RS.rClos 0 (RS.rVar (RS.bnd 0))
_ = Eq.refl

-- THE GLUE COMPUTES.  The pair compiler at a closed term.
_ : pairT [] selfApp .snd .fst Eq.≡ RS.rCall (RS.rClos 0 (RS.rVar (RS.bnd 0)))
                                             (RS.rClos 0 (RS.rVar (RS.bnd 0)))
_ = Eq.refl

_ : pairT [] selfApp .fst Eq.≡ convert selfApp
_ = Eq.refl

-- DETERMINED, AT THE WITNESS OF §4: the source splitting picks the
-- Rust one, and it is the ORDER-PRESERVING interleaving -- not the
-- swapped one, which is exactly why `Coherent` fails.
_ : determined appop gluePt srcSplit .fst
  Eq.≡ (RS.fre 0 ∷ [] , RS.fre 1 ∷ [] , RC.ileft (RC.iright RC.inil))
_ = Eq.refl

-- the swapped splitting is a genuine splitting of the SAME resource --
-- so §4's counterexample is not a type error dressed up as one
_ : swapSplit .snd .fst Eq.≡ (RS.fre 0 ∷ [])
_ = Eq.refl

-- ------------------------------------------------------------------
-- THE CAPSTONE.  `agree` computes, and what it computes is the point
-- of the whole file: the two answers for `(λx.x)(λx.x)` are
--
--     rClos 0 (rVar (bnd 0))     : RExpr        -- the Rust backend
--     clos 1 []                  : Val          -- the CC backend
--
-- There is no equation between them and there cannot be -- they are
-- not even of the same type, and `Correct.valuesCollapse` says the
-- second one's type separates nothing.  What `Same` supplies is the
-- APEX: both realise `idLin`, which is `selfApp`'s source value.
-- ------------------------------------------------------------------

_ : agree selfApp .fst Eq.≡ RS.rClos 0 (RS.rVar (RS.bnd 0))
_ = Eq.refl

_ : agree selfApp .snd .fst Eq.≡ clos 1 []
_ = Eq.refl

-- ... and the source value the span is centred on is `idLin`
_ : agree selfApp .snd .snd .snd .snd .fst Eq.≡ idLin
_ = Eq.refl

-- the CC component of the span really is the machine's own answer
_ : obs selfApp Eq.≡ just (agree selfApp .snd .fst)
_ = Eq.refl
