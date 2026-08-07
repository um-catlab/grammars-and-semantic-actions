{-
  THE MOTIVATING INSTANCE: THE DE BRUIJN THEORY MEETS THE LINEAR-CONTEXT
  THEORY.

  `Instances/LinLam/Check.agda` names this file's subject in its header,
  under "WHERE THE FRAMEWORK DOES NOT REACH":

      "`join?` is a metalanguage `⊎`, not an internal `Dec⟨_⟩`, and it
       has to be.  `Use⊎` is a splitting of `linFib`, which lives over
       `monoidSig`, while everything else here lives over `λSig`.
       `CarrierMap.Reindex` relates two promodels over ONE signature, so
       there is NO `Reindex` between the de Bruijn theory and the
       linear-context theory, and the bridge cannot be a map of
       promodels at all.

       BELONGS UPSTREAM: `Reindex` along a MAP OF SIGNATURES [...] With
       it, `join?` would be the image of the linear theory's own
       decision for `Split appop`."

  With `Reindex.Base` the bridge exists.  This file writes it down and
  reports what it does and does not buy, which is not quite what the note
  predicted.

  --------------------------------------------------------------------
  THE SIGNATURE MORPHISM.  It goes `λSig → monoidSig`, and that direction
  is FORCED -- there is no morphism the other way.  `onAr` is
  contravariant, so `onOp nilop` would have to be an operation of `λSig`
  with an EMPTY arity, and `λSig` has none (`varOp` has arity `Unit`).
  So the AST theory maps into the resource theory and not conversely,
  which is what "each pass lands in a slightly richer theory" says when
  read on signatures rather than on carriers.

  Since `monoidSig` is single-sorted, `resEq` and `sortEq` are `Eq.refl`
  on the nose: the two sorts `nm`/`tm` both go to `tt`.  So this instance
  exercises the OPERATION and ARITY translation without any coherence
  transport at all, which is the right first instance to have.

      onOp varOp = nilop      onAr varOp : ⊥ → Unit
      onOp appOp = appop      onAr appOp : Bool → Bool     (the identity)
      onOp lamOp = nilop      onAr lamOp : ⊥ → Bool

  --------------------------------------------------------------------
  THE CARRIER MAP is the free-variable set, as a usage: `fv`.  A name
  goes to the usage owning exactly it (`Check.onlyF`, reused verbatim), a
  term to the positions it mentions.

  --------------------------------------------------------------------
  WHAT SPLIT PRESERVATION SAYS HERE, WHICH IS THE POINT OF THE FILE.

  `SplitPresAtOver fvMap appOp` unfolds to: for every `dapp U V`, the
  free-variable sets of `U` and of `V` form a `Use⊎`-decomposition of the
  free-variable set of the whole.  `Use⊎` has no clause taking `true` on
  both sides, so that says exactly

      NO VARIABLE IS FREE IN BOTH PREMISES OF AN APPLICATION

  -- linearity, at that node.  Hence:

    * `¬presApp`   -- preservation FAILS globally, refuted at
                     `dapp (dvar 0) (dvar 0)`, i.e. at the standard
                     non-linear term.  It is not a defect of the map;
                     the map is right and the property is false.

    * `presAppAt` / `presAppAt⁻` -- preservation AT A POINT is LOGICALLY
                     EQUIVALENT to `Check.Join (fv U) (fv V)`.  Both
                     directions, no side conditions.

    * `presApp?`  -- therefore `Check.join?` IS the decision of split
                     preservation at an application.  This is the
                     sentence the note asked for, as a term: the
                     metalanguage `⊎` in `Check.agda` was not an
                     accident of exposition, it was the decision of a
                     property that had no home.  It has one now.

  The note's exact prediction -- that `join?` would become the image of
  `Decidable.Splittings` for `Split appop` -- is NOT what happens, and
  the difference is worth recording.  `DecSplittings` decides `⊗ˢ` at a
  GIVEN whole; `join?` asks whether two given parts have a whole, which
  is decidability of the LaxPoint's partial operation, not of the
  splitting relation.  What the bridge supplies is the type for `join?`'s
  conclusion, not a derivation of `join?` from an existing decision.

  --------------------------------------------------------------------
  AND AT THE OTHER OPERATIONS: `varOp` fails too (`¬presVar`) -- a
  variable is not the unit of the resource monoid -- and `lamOp` fails
  for the same reason.  So `fvBridge` is a `Link` and not a `Pass`, and
  that is the honest shape of the AST → resources phase: it is a bridge
  that becomes a pass only on the linear fragment, and cutting out that
  fragment is what `Check.linear?` does.

  --------------------------------------------------------------------
  THE CHAIN.  `fvBridge ⨟L forget layoutPass` is the two-link chain

      AST  --fv-->  linear usages  --layout-->  heap

  crossing a signature at the first link and not at the second.  It
  computes: the last `refl` in this file is the heap frame of a
  two-variable application, obtained straight from the de Bruijn term.

  PHASE DISCIPLINE.  Everything here is phase 1 -- it is the
  construction of a pass, so it matches `Use⊎`, `IsDApp` and the carrier.
  The phase-2 interface is `AlongOver`.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Reindex.LinLam where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false; _or_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Empty as E using (⊥)
open import Cubical.Data.FinData.Base using (Fin)
  renaming (zero to fzero; suc to fsuc)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.ChangeOfTheory
  using (SigMor; onSort; onOp; onAr; resEq; sortEq)
open import TheoryGrammar.Reindex.Base
open import TheoryGrammar.Reindex.Pass

-- the two signatures
open import TheoryGrammar.Instances.Lambda.Signature

-- the SOURCE theory: scoped de Bruijn terms over `λSig`
open import TheoryGrammar.Instances.LinLam.DB
  using (DBTm; dvar; dapp; dlam; Scope•; Term•; DBCar;
         IsDVar; IsDApp; IsDLam; mkDVar; mkDApp; mkDLam;
         DBSplit; DBParts; dbFib)

-- the TARGET theory: linear usages over `monoidSig`
import TheoryGrammar.Instances.LinLam.Context as L

-- THE FILE THIS EXISTS FOR.  `onlyF`, `Join` and `join?` are taken
-- verbatim; nothing in `Check.agda` is changed or restated.
open import TheoryGrammar.Instances.LinLam.Check
  using (onlyF; Join; Dec⊎; join?)

-- the downstream phase, to make a two-link chain
open import TheoryGrammar.Reindex.Sanity
  using (linTheory; heapTheory; layoutPass; layoutOver)
import TheoryGrammar.Instances.Heap.Graded as H

-- ==================================================================
-- THE FREE-VARIABLE SET OF A DE BRUIJN TERM, AS A USAGE.
-- PRIMITIVE (phase 1): recursion on the tree.
-- ==================================================================

-- pointwise disjunction; only the equal-length case is ever used, and
-- the two ragged clauses are there so it is total
orU : L.Usage → L.Usage → L.Usage                    -- PRIMITIVE
orU []      v       = v
orU (a ∷ u) []      = a ∷ u
orU (a ∷ u) (b ∷ v) = (a or b) ∷ orU u v

-- a binder consumes position 0
dropU : L.Usage → L.Usage                            -- PRIMITIVE
dropU []      = []
dropU (_ ∷ u) = u

fv : {n : ℕ} → DBTm n → L.Usage                      -- PRIMITIVE
fv (dvar i)   = onlyF i
fv (dapp u v) = orU (fv u) (fv v)
fv (dlam b)   = dropU (fv b)

-- THE ONE STRUCTURAL FACT.  A splitting of ANY whole is a splitting of
-- the pointwise disjunction -- `Use⊎` determines its output (this is
-- `Check.joinFun` read constructively).  Constructor for constructor,
-- no arithmetic, no coercion.
use⊎-or : {a b w : L.Usage} → L.Use⊎ a b w → L.Use⊎ a b (orU a b)
use⊎-or L.unil       = L.unil
use⊎-or (L.uleft s)  = L.uleft  (use⊎-or s)
use⊎-or (L.uright s) = L.uright (use⊎-or s)
use⊎-or (L.uskip s)  = L.uskip  (use⊎-or s)

-- ==================================================================
-- THE SIGNATURE MORPHISM.  See the header for why the direction is
-- forced and why every coherence equation is `Eq.refl`.
-- ==================================================================

onOpλ : LOp → L.MonOp
onOpλ varOp = L.nilop
onOpλ appOp = L.appop
onOpλ lamOp = L.nilop

onArλ : (o : LOp) → L.MonAr (onOpλ o) → LAr o
onArλ varOp ()
onArλ appOp b = b
onArλ lamOp ()

λ→mon : SigMor λSig L.monoidSig
λ→mon .onSort _   = tt
λ→mon .onOp       = onOpλ
λ→mon .onAr       = onArλ
λ→mon .resEq  o   = Eq.refl
λ→mon .sortEq o b = Eq.refl

-- ==================================================================
-- THE CARRIER MAP, OVER IT.  This is the object `Check.agda` says does
-- not exist: a map of promodels ACROSS a change of signature.
-- ==================================================================

fvMap : ReindexOver λ→mon dbFib L.linFib
fvMap .homO nm (n , i) = onlyF i
fvMap .homO tm (n , t) = fv t

dbTheory : Theory ℓ-zero ℓ-zero ℓ-zero ℓ-zero ℓ-zero
dbTheory = theory λSig dbFib

fvLink : Link dbTheory linTheory
fvLink .sigL = λ→mon
fvLink .mapL = fvMap

-- ==================================================================
-- SPLIT PRESERVATION AT AN APPLICATION *IS* THE LINEARITY CONDITION.
-- Both directions.
-- ==================================================================

-- PRIMITIVE (phase 1)
presAppAt : (n : ℕ) (u v : DBTm n) → Join (fv u) (fv v)
          → PresAt fvMap appOp (n , dapp u v)
presAppAt n u v (w , s) (mkDApp _ _) =
    (fv u , fv v , use⊎-or s)
  , L.boolΠ
      {M = λ b → L.linFib .parts L.appop (fv (dapp u v))
                    (fv u , fv v , use⊎-or s) b
                 Eq.≡ homSlotOf fvMap appOp b
                        (DBParts appOp (n , dapp u v) (mkDApp u v) b)}
      Eq.refl Eq.refl

private
  -- PRIMITIVE (phase 1)
  useCo : {a a' b b' w : L.Usage} → a Eq.≡ a' → b Eq.≡ b'
        → L.Use⊎ a b w → L.Use⊎ a' b' w
  useCo Eq.refl Eq.refl s = s

-- PRIMITIVE (phase 1): and conversely.  The transported splitting's two
-- slots ARE the free-variable sets -- that is `homPartsO` -- so the
-- `Use⊎` it carries is already the one wanted.
presAppAt⁻ : (n : ℕ) (u v : DBTm n) → PresAt fvMap appOp (n , dapp u v)
           → Join (fv u) (fv v)
presAppAt⁻ n u v P =
    fv (dapp u v)
  , useCo (P (mkDApp u v) .snd true) (P (mkDApp u v) .snd false)
          (P (mkDApp u v) .fst .snd .snd)

-- ==================================================================
-- THE SENTENCE `Check.agda` ASKED FOR.  `join?` decides split
-- preservation of the bridge at an application.
-- ==================================================================

presApp? : (n : ℕ) (u v : DBTm n)
         → Dec⊎ (PresAt fvMap appOp (n , dapp u v))
presApp? n u v = go (join? (fv u) (fv v))
  where
  go : Dec⊎ (Join (fv u) (fv v))
     → Dec⊎ (PresAt fvMap appOp (n , dapp u v))
  go (inl j) = inl (presAppAt n u v j)
  go (inr k) = inr (λ P → k (presAppAt⁻ n u v P))

-- ==================================================================
-- ... AND THE NEGATIVE HALF, which is why the decision is needed.
--
-- Compare `Codegen.noPackPres` and `Scope.¬presLam`: three passes, three
-- different operations at which preservation fails, each refuted by an
-- explicit point.  Here the point is the standard non-linear term.
-- ==================================================================

private
  -- THE MISSING CONSTRUCTOR, used -- exactly as `Check.dupUse`.
  dupJ : {a b : L.Usage} → Join (true ∷ a) (true ∷ b) → ⊥
  dupJ (w , ())

selfAppDB : Term•
selfAppDB = 1 , dapp (dvar fzero) (dvar fzero)

¬presApp : SplitPresAtOver fvMap appOp → ⊥
¬presApp P =
  dupJ (presAppAt⁻ 1 (dvar fzero) (dvar fzero)
         (fromPres fvMap appOp P selfAppDB))

-- A VARIABLE IS NOT THE UNIT OF THE RESOURCE MONOID.  `onOp varOp` has
-- to be `nilop` -- nothing else in `monoidSig` has a small enough arity
-- -- so preservation at `varOp` would say the free-variable set of a
-- variable is empty.
¬presVar : SplitPresAtOver fvMap varOp → ⊥
¬presVar P = fromPres fvMap varOp P (1 , dvar fzero) (mkDVar fzero) .fst

-- ==================================================================
-- REFLECTION FAILS TOO, AND EARLIER.  A decomposition of `fv (dapp U V)`
-- is any pair of usages that joins to it; the source has exactly one
-- decomposition, whose parts are `fv U` and `fv V`.  So a split that is
-- not that one has nothing to reflect back to.  `[false] ⊎ [true]` is
-- such a split of `fv (dapp (dvar 0) (dvar 0)) = [true]` at scope 1.
-- ==================================================================

private
  oddSplit : L.linFib .Split L.appop (fv (dapp (dvar {n = 1} fzero) (dvar fzero)))
  oddSplit = (false ∷ []) , (true ∷ []) , L.uright L.unil

  falseNotTrue : (false ∷ []) Eq.≡ (true ∷ []) → ⊥
  falseNotTrue ()

  -- unique readability, used once: the source's only splitting is
  -- `mkDApp`, so its left slot maps to `fv (dvar 0) = [true]`, and the
  -- reflected equation would identify that with `[false]`.
  reflAppInv : (sp : IsDApp (dapp (dvar {n = 1} fzero) (dvar fzero)))
             → (false ∷ [])
               Eq.≡ homSlotOf fvMap appOp true
                      (DBParts appOp selfAppDB sp true)
             → ⊥
  reflAppInv (mkDApp _ _) e = falseNotTrue e

¬reflApp : ReflectsSplitAtOver fvMap appOp → ⊥
¬reflApp R =
  reflAppInv (R selfAppDB oddSplit .fst) (R selfAppDB oddSplit .snd true)

-- ==================================================================
-- THE CHAIN.  AST  --fv-->  usages  --layout-->  heap.
--
-- The first link crosses a signature; the second does not.  `_⨟L_`
-- composes them anyway, and the composite still COMPUTES -- which is the
-- test that the `Eq`-world bookkeeping did not go inert.
-- ==================================================================

db→heap : Link dbTheory heapTheory
db→heap = fvLink ⨟L forget layoutPass

-- the composite's signature morphism, spelled out
_ : db→heap .sigL .onOp appOp ≡ L.appop
_ = refl

-- two free variables lay out to two disjoint cells
_ : db→heap .mapL .homO tm (2 , dapp (dvar fzero) (dvar (fsuc fzero)))
  ≡ (0 , H.v1) ∷ (1 , H.v1) ∷ []
_ = refl

-- ... and the non-linear term collapses them onto one, which is why the
-- first link is not a pass
_ : db→heap .mapL .homO tm selfAppDB ≡ H.single 0 H.v1
_ = refl

-- a closed term allocates nothing
_ : db→heap .mapL .homO tm (0 , dlam (dvar fzero)) ≡ []
_ = refl
