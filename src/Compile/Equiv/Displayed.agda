{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE SAME EQUIVALENCE, BY DISPLAYED-MODEL GLUING.

  `Compile/Equiv/Glue.agda` proves the fundamental lemma for closure
  conversion (`relConvG`/`relConvert`) by an EXPLICIT STRUCTURAL
  RECURSION on the source term, threading the offset hypothesis `Fits`
  by hand.  This file proves the same theorem with no recursion at all:
  the logical relation is packaged as a DISPLAYED MODEL over the target,
  reindexed along the interpretation, and the section is produced by the
  FREE MODEL'S ELIMINATOR.

  ------------------------------------------------------------------
  §0  THE RECIPE, AND WHERE EACH PIECE COMES FROM
  ------------------------------------------------------------------

  c-c-l's gluing program (branch `parametricity`,
  `Gluing/BiCartesianClosedCategory/BinaryLogicalRelation.agda`) is
  three lines:

      pointwise       = ⟨F,G⟩ : FREE → D × D          the paired interp
      LRGenerators    = ElimInterpᴰ Q (elimLocalMotive Q pointwise Dⱽ)
      logicalRelation = elimLocal Q pointwise Dⱽ generators
                      : Section (pointwise .fst) Dⱽ.Cᴰ

  `Dⱽ` is a VERTICAL displayed structure over the semantic category --
  the logical relation, stated about semantic objects only.
  `elimLocalMotive` REINDEXES it along `pointwise` to a displayed model
  over the FREE model.  `elimLocal` is the free model's eliminator, and
  the fundamental lemma is the SECTION it returns.  Nobody writes an
  induction.

  Transcribed here (`TheoryGrammar/Instances/LinLam/Elim.agda`):

      c-c-l                             this development
      ---------------------------------------------------------------
      FREE BiCCC, elimLocal             `TmG`, `roll`, `indTm`
      Dⱽ  (vertical displayed model)    `RelD : Ctxᴰ (TmG & ConvG)`
      pointwise = ⟨F,G⟩                 `pairFold ConvG convAlg`
                                          = ⟨ idg , convT ⟩
      elimLocalMotive (reindexing)      `reindexPair`
      Section                           `fundamental`

  The free model here is `TmG` presented as the initial `StepG`-algebra
  (`Opt.agda`: `roll`, `foldTm`), NOT as a `μ` of
  `TheoryGrammar.Inductive`.  It cannot be the latter --
  `Inductive.Functor` has no reindexing former, so the recursive
  occurrence of `tlam : Tm (true ∷ u) → Tm u` at a WEAKENED world has no
  code -- but it does not need to be: `StepG`'s third summand `BodyOf A
  u = A (true ∷ u)` is that reindexing, written directly, and `indTm` is
  its eliminator.

  ------------------------------------------------------------------
  §0.1  WHAT IS PROVED HERE, AND HOW IT DIFFERS FROM `Glue.agda`
  ------------------------------------------------------------------

      relD          : Algᴰ (TmG & ConvG) pairAlg RelD    -- THE DISPLAYED
                                                            MODEL: 3 clauses,
                                                            NO recursion
      relConvert    : (t : Tm []) → RelE (tableOf t) emptyF t (convert t)
                                                         -- = eliminator ∘
                                                            displayed model
      agree         : (t : Tm []) → Agree t

  `relConvert` below is `fundamental ConvG convAlg RelD relD` applied at
  the empty usage.  Its three clauses are `Glue.relConvG`'s three
  bodies verbatim -- WITH THE RECURSIVE CALLS DELETED.  That deletion is
  the whole point: `relConvG a T n σ hL` becomes the argument `pa T n σ
  hL`, and the recursion that produced it is `indTm`'s, once, generically,
  for every displayed model over this signature.

  Neither `Glue.agda` nor anything it proves is touched; the two files
  are meant to be read side by side.

  ------------------------------------------------------------------
  §0.2  WHAT THE REINDEXING BUYS, CONCRETELY
  ------------------------------------------------------------------

  `RelD` is stated about a source term AND its image, i.e. about the
  pair grammar `TmG & ConvG` -- never about `Tm` alone.  That is what
  makes it a displayed model over the TARGET rather than a predicate on
  syntax, and it is why `reindexPair` (not `pullᴰ` alone) is the
  reindexing needed: the left leg of the pairing is the identity, so the
  motive can mention the source term, and the right leg is `convT`, so
  it can mention the compiled one.

  The transport is free.  `foldTm`'s three defining clauses ARE the
  algebra-map equations for `⟨ idg , convT ⟩`, definitionally, so
  `reindexPair`'s clauses carry no `subst` and no `Eq.transport`.  §3's
  `refl` tests are the evidence: `agree selfApp` still computes.

  ------------------------------------------------------------------
  §0.3  WHAT STILL DOES NOT COME FROM THE ELIMINATOR
  ------------------------------------------------------------------

  The `Fits` hypothesis.  Closure conversion numbers blocks GLOBALLY
  (`convApp` offsets the right premise by the left premise's table
  length), so the displayed grammar is not `RelE T σ t e` but

      Π T n σ. Fits T n (tableOf-of-this-subterm) → RelE T σ t e

  -- a Π-type in the motive, threaded by the eliminator like any other
  motive.  That is not a defect of the recipe; it is `Glue.agda` §0.2(4)
  showing up as the SHAPE of the displayed model instead of as a
  hand-threaded parameter.  `at-++ˡ`/`at-++ʳ`/`athere` still appear --
  three times, in the displayed model's data, where they belong.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1 is `Elim.agda` (the eliminator).  §1-§2 here are data for it:
  `relD` matches only `StepG`'s summands and a splitting's PROJECTIONS,
  never `Tm`.  There is no `Tm` pattern in this file.
-}
open import Cubical.Foundations.Prelude

module Compile.Equiv.Displayed where

open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; +-zero; +-suc; +-assoc)
open import Cubical.Data.List using (List; []; _∷_; _++_; length)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Data.Unit using (Unit; tt; Unit*; tt*)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib

-- THE ELIMINATOR OF THE FREE MODEL, and the reindexing theorem.
open import TheoryGrammar.Instances.LinLam.Elim

-- THE SOURCE AND THE CLOSURE-CONVERSION BACKEND.  Re-exports `Tm`,
-- `convT`, `convert`, `tableOf`, `RelE`, `RelV`, `Ev`, `squareProg`.
open import Compile.ClosureConv.Correct

-- THE RUST BACKEND, for §3's `agree`.  Qualified, as in `Glue.agda`.
import Compile.LinToRust.Theory   as RT
import Compile.LinToRust.Codegen  as RC
import Compile.LinToRust.Syntax   as RS
import Compile.Relational.Base    as R
import Compile.Semantics.CBV      as S

-- THE FILE THIS ONE IS THE ANSWER TO.  Imported only for §4's
-- cross-check, and qualified so nothing here can accidentally cite it.
import Compile.Equiv.Glue         as HandRolled

-- ==================================================================
-- §1  THE DISPLAYED MODEL.
--
-- A displayed grammar over the PAIRED carrier `TmG & ConvG`: at a
-- source term `t` and a numbering function `c`, the statement that
-- every whole-program table into which `c`'s blocks have been placed at
-- a known offset relates the two.
--
-- Read as c-c-l's `Dⱽ`: a relation between the two interpretations,
-- stated with no reference to the free model's eliminator.
-- ==================================================================

-- "the blocks `Ts` sit inside `T` starting at index `n`"
Fits : Table → ℕ → Table → Type₀
Fits T n Ts = {i : ℕ} {sh : Usage} {b : IR (true ∷ sh)}
            → At Ts i sh b → At T (n + i) sh b

private
  -- transport of a lookup along an arithmetic identity.  Feeds a
  -- premise; never projected from, so it never has to compute.
  atCoe : {T : Table} {i j : ℕ} {sh : Usage} {b : IR (true ∷ sh)}
        → i ≡ j → At T i sh b → At T j sh b
  atCoe {T = T} {sh = sh} {b = b} p a =
    Eq.transport (λ z → At T z sh b) (Eq.pathToEq p) a

RelD : Ctxᴰ (TmG & ConvG) ℓ-zero
RelD u (t , c) = (T : Table) (n : ℕ) (σ : Frame)
               → Fits T n (c n .snd) → RelE T σ t (c n .fst)

-- ------------------------------------------------------------------
-- THE DISPLAYED ALGEBRA -- the whole mathematical content of the file.
--
-- One clause per rule of the source.  Each is `Glue.relConvG`'s
-- corresponding body with the recursive calls replaced by the displayed
-- data the eliminator will supply, and nothing else changed.
-- ------------------------------------------------------------------

relD : Algᴰ (TmG & ConvG) (pairAlg ConvG convAlg) RelD

-- VARIABLE.  No premise, no block, and the two sides read the same
-- slot -- so the displayed datum is `tt*` and the answer is `rvar`.
relD u (inl s) tt* T n σ h = rvar s s Eq.refl

-- APPLICATION.  The two premises' displayed data are `pa` and `pb`;
-- all this clause does is SPLIT the offset hypothesis between them.
-- `at-++ˡ`/`at-++ʳ` are the global-numbering tax named in §0.3.
relD u (inr (inl (sp , k))) (pa , pb) T n σ h =
  rapp (pa T n σ hL) (pb T m σ hR)
  where
  Ta : Table
  Ta = k true .snd n .snd

  m : ℕ
  m = n + length Ta

  hL : Fits T n Ta
  hL x = h (at-++ˡ _ x)

  hR : Fits T m (k false .snd m .snd)
  hR {i} x = atCoe (+-assoc n (length Ta) i) (h (at-++ʳ Ta x))

-- ABSTRACTION.  The body's block is filed at index `n`, so `ahere`
-- locates it and the rest of the table shifts by one.  `pb` is the
-- body's displayed datum, at the extended usage -- which is exactly
-- what `BodyOfᴰ` gives, with no weakening lemma in sight.
relD u (inr (inr b)) pb T n σ h =
  rclos at (pb T (suc n) (callFrame u (capVals σ (idCap u)) junk) hB)
  where
  r : IR (true ∷ u) × Table
  r = b .snd (suc n)

  at : At T n u (r .fst)
  at = atCoe (+-zero n) (h ahere)

  hB : Fits T (suc n) (r .snd)
  hB {i} x = atCoe (+-suc n i) (h (athere x))

-- ==================================================================
-- §2  THE SECTION.  The fundamental lemma, from the eliminator.
--
-- `fundamental` is `indTm ∘ reindexPair`: no induction here, and none
-- in §1.  Compare `Glue.relConvG`, which is the same three bodies with
-- three recursive calls threading `Fits` by hand.
-- ==================================================================

relSection : (u : Usage) (t : Tm u) → RelD u (t , convT u t)
relSection = fundamental ConvG convAlg RelD relD

-- ... and at the top the offset is `0`, so `Fits` is the identity.
relConvert : (t : Tm []) → RelE (tableOf t) emptyF t (convert t)
relConvert t = relSection [] t (tableOf t) 0 emptyF (λ x → x)

-- ==================================================================
-- §3  THE EQUIVALENCE THEOREM, unchanged from `Glue.agda` §7 except
-- that its one hypothesis now comes from §2.
-- ==================================================================

Same : Tm [] → RS.RExpr → Val → Type₀
Same t wR wC =
  Σ[ v ∈ Tm [] ] (R.Rel (RC.nameOf 0) v wR × RelV (tableOf t) v wC)

Agree : Tm [] → Type₀
Agree t =
  Σ[ wR ∈ RS.RExpr ] Σ[ wC ∈ Val ]
    ( (RC.compileRust t RC.⇓ wR)                    -- the Rust backend runs
    × Ev (tableOf t) emptyF (convert t) wC          -- the CC backend runs
    × Same t wR wC )                                -- and the answers agree

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
-- §4  OBSERVATION.  The eliminator-produced relation still COMPUTES --
-- `reindexPair` introduced no coercion, so nothing is stuck.
-- ==================================================================

_ : agree selfApp .fst Eq.≡ RS.rClos 0 (RS.rVar (RS.bnd 0))
_ = Eq.refl

_ : agree selfApp .snd .fst Eq.≡ clos 1 []
_ = Eq.refl

-- the apex of the span is the source's own value
_ : agree selfApp .snd .snd .snd .snd .fst Eq.≡ idLin
_ = Eq.refl

-- the CC component really is the machine's answer
_ : obs selfApp Eq.≡ just (agree selfApp .snd .fst)
_ = Eq.refl

-- ------------------------------------------------------------------
-- ... AND IT IS THE SAME PROOF.  `Glue.relConvert` is the hand-rolled
-- recursion, `relConvert` is the eliminator applied to `relD`; at a
-- closed term the two derivations are equal ON THE NOSE.  So the
-- rewrite is not a different theorem proved a different way -- the
-- eliminator produces exactly the derivation the induction did, and
-- the induction was the eliminator all along.
-- ------------------------------------------------------------------

_ : relConvert selfApp Eq.≡ HandRolled.relConvert selfApp
_ = Eq.refl

_ : relConvert idLin Eq.≡ HandRolled.relConvert idLin
_ = Eq.refl
