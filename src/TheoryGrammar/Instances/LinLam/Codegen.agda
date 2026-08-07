{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  PHASE 4: CODE GENERATION AS A MAP OF PARTIAL COMMUTATIVE MONOIDS,
  AND NO-ALIASING AS `SplitPresAt`.

  THE CLAIM UNDER TEST.  Both ends of this compiler are PCMs presented as
  promodels over `monoidSig`, and they are presented in the SAME shape:

      LinLam/Context   Split appop u = Σ u₁, Σ u₂, Use⊎ u₁ u₂ u
      Heap/Base        Split appop h = Σ h₁, Σ h₂, Ilv h₁ h₂ h × (h₁ # h₂)

  In the first, linearity is the ABSENT constructor -- there is no clause
  of `Use⊎` taking `true` on both sides.  In the second, partiality is the
  `h₁ # h₂` conjunct -- two regions may not own a location.  The claim is
  that a layout of variables into memory is a `Reindex linFib heapFib`
  whose `SplitPresAt appop` holds, i.e. that

      the source's missing constructor MANUFACTURES the target's
      disjointness conjunct,

  so that "the code emitted for the two premises of an application does
  not alias" is not a theorem about the pass but the pass's very type.

  VERDICT: IT HOLDS -- and more than holds.  `layPres` below builds
  `SplitPresAt` at BOTH operations, and `layRefl` builds
  `Along.ReflectsSplitAt` at both as well.  So the layout is not merely a
  lax map of PCMs; splittings correspond BIJECTIVELY, which is the
  discrete Conduché condition of `ChangeOfTheory` read at a promodel.
  Concretely `push⊗`/`pull⊗` give both halves of

      Lay A ⊛ Lay B   ⊣⊢   Lay (A ∗ B)

  -- the layout is a STRONG monoidal functor from linear contexts to
  separation logic, `⊛` (context splitting) to `∗` (heap separation).

  THE LAYOUT, AND WHY IT IS THIS ONE.  A usage is a `List Bool` whose
  position `i` says whether variable `i` is still available.  The layout
  sends position `i` to LOCATION `i`, keeping only the live ones:

      lay i []          = []
      lay i (true  ∷ u) = (i , v1) ∷ lay (suc i) u
      lay i (false ∷ u) = lay (suc i) u

      layout = lay 0

  The offset argument is what makes the recursion go through: a usage
  carries no absolute addresses, so the layout of a TAIL must be told
  where it starts.  `v1` is a constant because the layout is about
  OWNERSHIP, not contents -- `Val` is three-valued precisely so that a
  cell is a reducible closed term and every test below is `refl`.

  Two facts make the correspondence work, and they are the only two:

    (1) POSITIONS ARE ADDRESSES, so distinct variables get distinct
        locations.  This is `freshLay`: everything `lay i u` allocates is
        at a location ≥ i, hence apart from any `j < i`.  It is what turns
        the ABSENCE of a `(true,true)` clause into the PRESENCE of `_#_`,
        because the only way `Use⊎` lets two slots both reach position `i`
        is the clause that does not exist.

    (2) THE OFFSET IS SHARED.  `Use⊎ u₁ u₂ u` puts all three usages in
        lockstep, so `lay i u₁`, `lay i u₂` and `lay i u` walk the same
        positions and `ilvLay` is a literal constructor-for-constructor
        translation: `uleft ↦ left`, `uright ↦ right`, `uskip ↦ id`.
        `unil ↦ nil`.  There is no arithmetic anywhere in it.

  Nothing here is contrived to make the claim come out; the two clauses
  of `apartLay` that do work (`uleft`, `uright`) both discharge exactly
  `freshLay`, and the third (`uskip`) is the identity.  The one asymmetry
  -- `uright` needs `#-cons-r` while `uleft` does not -- is an artifact of
  `_#_` recursing on its LEFT argument, not a mathematical fact.

  WHERE IT COULD HAVE BROKEN -- and this half is PROVED, not asserted.
  The obvious alternative layout COMPACTS: drop the dead positions and
  address the live ones consecutively from 0, so a frame is as small as
  possible.  That is what a real compiler does, and `noPackPres` below
  shows it FAILS `SplitPresAt appop` -- at the two-variable application
  `twoVar`, both premises compact to `single 0 v1`, `_#_` is uninhabited,
  and `H.#-self` refutes the field.  So split preservation is not a
  formality that any layout satisfies; it is a genuine constraint, and it
  says exactly this:

      a linear source language buys no-aliasing for free precisely when
      the ALLOCATOR IS INJECTIVE ON VARIABLES, uniformly in the context.

  Compaction is injective on each usage separately but not stably across a
  split, and that is the whole difference.  `CarrierMap` localises the
  failure at one operation of one pass, which is what it is for.

  PHASE DISCIPLINE.  Everything from `lay` down to `layRefl` is phase 1 --
  it is the construction of the pass, and it matches on `Use⊎`, on `Ilv`
  and on the carrier, which is what an intro/elim rule is allowed to do.
  Everything from `Lay` down is phase 2: `push⊗`, `pull⊗`, `pullTerm`,
  `⊗ˢ-map`, `_∘g_`, `boolΠ`, and nothing else.  In particular
  `noDupLay` -- "no usage splits into two halves that both lay out to the
  same single cell", i.e. no variable is used twice -- is obtained by
  TRANSPORTING the heap-side theorem `apart-self` along `pullTerm`, not by
  reproving it.  That is the pass doing work: a fact about memory becomes
  a fact about linearity, with no new induction.
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.LinLam.Codegen where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib
open import TheoryGrammar.CarrierMap

-- the SOURCE theory, opened plainly: all the `⊢`-combinators below are
-- the linear-context ones
open import TheoryGrammar.Instances.LinLam.Syntax public

-- the TARGET theory, qualified -- it re-exports its own `⊢`, `⊗ˢ`,
-- `boolΠ`, ... and the two must not collide
import TheoryGrammar.Instances.Heap.Graded as H

-- ==================================================================
-- THE LAYOUT.  PRIMITIVE (phase 1): recursion on the usage.
-- ==================================================================

lay : ℕ → Usage → H.Heap
lay i []          = []
lay i (true  ∷ u) = (i , H.v1) ∷ lay (suc i) u
lay i (false ∷ u) = lay (suc i) u

layout : Usage → H.Heap
layout = lay 0

-- ==================================================================
-- (1) POSITIONS ARE ADDRESSES.  `Below j i` is `j < i` written
-- structurally, so that it is Unit/⊥-valued and never blocks a `refl`
-- -- the same choice `Heap/Base` makes for `Diff`, `Fresh` and `_#_`.
-- ==================================================================

Below : ℕ → ℕ → Type₀                                  -- PRIMITIVE
Below _       zero    = ⊥
Below zero    (suc _) = Unit
Below (suc j) (suc i) = Below j i

below→Diff : (j i : ℕ) → Below j i → H.Diff j i        -- PRIMITIVE
below→Diff j       zero    ()
below→Diff zero    (suc i) b = tt
below→Diff (suc j) (suc i) b = below→Diff j i b

below-suc : (j : ℕ) → Below j (suc j)                  -- PRIMITIVE
below-suc zero    = tt
below-suc (suc j) = below-suc j

below-weak : (j i : ℕ) → Below j i → Below j (suc i)   -- PRIMITIVE
below-weak j       zero    ()
below-weak zero    (suc i) b = tt
below-weak (suc j) (suc i) b = below-weak j i b

-- everything `lay i u` allocates sits at a location ≥ i.  THE fact that
-- turns "positions are distinct" into "locations are apart".
freshLay : (u : Usage) (i j : ℕ) → Below j i → H.Fresh j (lay i u)
freshLay []          i j b = tt
freshLay (true  ∷ u) i j b =
  below→Diff j i b , freshLay u (suc i) j (below-weak j i b)
freshLay (false ∷ u) i j b = freshLay u (suc i) j (below-weak j i b)

-- ==================================================================
-- Two structural facts about `_#_` that `Heap/Base` does not export.
-- Both are pure bookkeeping: `_#_` recurses on its LEFT argument, so
-- growing or shrinking the RIGHT one needs a clause.
-- ==================================================================

diff-sym : (l k : H.Loc) → H.Diff l k → H.Diff k l     -- PRIMITIVE
diff-sym zero    zero    d = d
diff-sym zero    (suc k) d = tt
diff-sym (suc l) zero    d = tt
diff-sym (suc l) (suc k) d = diff-sym l k d

#-cons-r : (h k : H.Heap) (l : H.Loc) (x : H.Val)      -- PRIMITIVE
         → H.Fresh l h → h H.# k → h H.# ((l , x) ∷ k)
#-cons-r []            k l x fr          d          = tt
#-cons-r ((m , y) ∷ h) k l x (dlm , fr) (frm , d) =
  (diff-sym l m dlm , frm) , #-cons-r h k l x fr d

#-tail-r : (h k : H.Heap) (l : H.Loc) (x : H.Val)      -- PRIMITIVE
         → h H.# ((l , x) ∷ k) → h H.# k
#-tail-r []            k l x d              = tt
#-tail-r ((m , y) ∷ h) k l x ((_ , fr) , d) = fr , #-tail-r h k l x d

-- ==================================================================
-- (2) THE OFFSET IS SHARED, so a `Use⊎` becomes an `Ilv`
-- constructor-for-constructor.  No arithmetic occurs.
-- ==================================================================

ilvLay : ∀ {u₁ u₂ u} → Use⊎ u₁ u₂ u → (i : ℕ)
       → H.Ilv (lay i u₁) (lay i u₂) (lay i u)
ilvLay unil       i = H.nil
ilvLay (uleft  s) i = H.left  (ilvLay s (suc i))
ilvLay (uright s) i = H.right (ilvLay s (suc i))
ilvLay (uskip  s) i = ilvLay s (suc i)

-- ... and the MISSING (true,true) clause becomes the PRESENT `_#_`.
-- This is the heart of the phase: there is nothing to prove in `unil`
-- and `uskip`, and the two real clauses discharge exactly `freshLay`.
apartLay : ∀ {u₁ u₂ u} → Use⊎ u₁ u₂ u → (i : ℕ) → lay i u₁ H.# lay i u₂
apartLay unil                  i = tt
apartLay (uleft  {v = v} s)    i =
  freshLay v (suc i) i (below-suc i) , apartLay s (suc i)
apartLay (uright {u = u} s)    i =
  #-cons-r (lay (suc i) u) _ i H.v1
           (freshLay u (suc i) i (below-suc i)) (apartLay s (suc i))
apartLay (uskip s)             i = apartLay s (suc i)

-- the nullary operation: an exhausted usage lays out to the empty heap
emptyLay : (u : Usage) (i : ℕ) → Empty u → H.IsNil (lay i u)
emptyLay []          i e = tt
emptyLay (true  ∷ u) i e = e            -- both sides are `⊥`
emptyLay (false ∷ u) i e = emptyLay u (suc i) e

-- ==================================================================
-- THE PASS, as a map of promodels.  Note the two `Fibered`s differ --
-- this is `Reindex`, not the endo `CarrierMap`, and it is exactly the
-- generalisation the phase needed.
-- ==================================================================

layoutMap : Reindex linFib H.heapFib
layoutMap .hom _ = layout

-- ==================================================================
-- SPLIT PRESERVATION.  THE RESULT OF THE PHASE.
--
-- At `appop`: a linear context split becomes a DISJOINT heap split, so
-- the emitted regions cannot alias -- and nothing else had to be said.
-- At `nilop`: an exhausted context becomes the empty heap.
-- ==================================================================

layPres : (o : MonOp) → SplitPresAt layoutMap o

layPres nilop .homSplit u e    = emptyLay u 0 e
layPres nilop .homParts u e ()

layPres appop .homSplit u (u₁ , u₂ , s) =
  layout u₁ , layout u₂ , ilvLay s 0 , apartLay s 0
layPres appop .homParts u (u₁ , u₂ , s) =
  boolΠ {M = λ a → H.boolΠ {M = λ _ → H.Heap} (layout u₁) (layout u₂) a
                     Eq.≡ layout (boolΠ {M = λ _ → Usage} u₁ u₂ a)}
        Eq.refl Eq.refl

module A = Along layoutMap

-- ==================================================================
-- ... AND SPLIT REFLECTION, which is the stronger half.
--
-- Given a disjoint decomposition of `layout u` we can READ BACK a
-- `Use⊎`: the interleaving already says which cell went left and which
-- went right, and cells are positions, so the two usages are determined.
-- Disjointness is not even used -- it is `Ilv` alone that reflects, which
-- says the layout is injective enough on the nose.
-- ==================================================================

reflLay : (u : Usage) (i : ℕ) {h₁ h₂ : H.Heap}
        → H.Ilv h₁ h₂ (lay i u) → h₁ H.# h₂
        → Σ[ u₁ ∈ Usage ] Σ[ u₂ ∈ Usage ]
            (Use⊎ u₁ u₂ u × ((h₁ Eq.≡ lay i u₁) × (h₂ Eq.≡ lay i u₂)))
reflLay []          i H.nil       d = [] , [] , unil , Eq.refl , Eq.refl
reflLay (true  ∷ u) i (H.left  p) d =
  let (a , b , s , e₁ , e₂) = reflLay u (suc i) p (d .snd)
  in true ∷ a , false ∷ b , uleft s , Eq.ap ((i , H.v1) ∷_) e₁ , e₂
reflLay (true  ∷ u) i (H.right p) d =
  let (a , b , s , e₁ , e₂) = reflLay u (suc i) p (#-tail-r _ _ i H.v1 d)
  in false ∷ a , true ∷ b , uright s , e₁ , Eq.ap ((i , H.v1) ∷_) e₂
reflLay (false ∷ u) i p           d =
  let (a , b , s , e₁ , e₂) = reflLay u (suc i) p d
  in false ∷ a , false ∷ b , uskip s , e₁ , e₂

reflNil : (u : Usage) (i : ℕ) → H.IsNil (lay i u) → Empty u
reflNil []          i n = tt
reflNil (true  ∷ u) i n = n            -- both sides are `⊥`
reflNil (false ∷ u) i n = reflNil u (suc i) n

layRefl : (o : MonOp) → A.ReflectsSplitAt o
layRefl nilop u n = reflNil u 0 n , λ ()
layRefl appop u (h₁ , h₂ , p , d) =
  let (u₁ , u₂ , s , e₁ , e₂) = reflLay u 0 p d
  in (u₁ , u₂ , s)
   , boolΠ {M = λ a → H.boolΠ {M = λ _ → H.Heap} h₁ h₂ a
                        Eq.≡ layout (boolΠ {M = λ _ → Usage} u₁ u₂ a)}
           e₁ e₂

-- ==================================================================
-- PHASE 2 FROM HERE DOWN.  `Lay` reinterprets a separation-logic
-- predicate as a predicate on linear contexts, and the two directions of
-- strong monoidality are `push⊗` and `pull⊗`, nothing else.
-- ==================================================================

Lay : H.Gr → Ctx
Lay B = A.pull {s = tt} B

-- `boolΠ` commutes with `Lay` -- the same pure respelling `Heap/
-- Connectives.respell` needs, and for the same reason: `boolΠ` is stuck
-- at a variable arity, so the two spellings are distinct TERMS even
-- though they agree at `true` and at `false`.
respellIn : (B C : H.Gr) (a : Bool)
          → boolΠ {M = λ _ → Ctx} (Lay B) (Lay C) a
          ⊢ Lay (H.boolΠ {M = λ _ → H.Gr} B C a)
respellIn B C =
  boolΠ {M = λ a → boolΠ {M = λ _ → Ctx} (Lay B) (Lay C) a
                 ⊢ Lay (H.boolΠ {M = λ _ → H.Gr} B C a)}
        idg idg

respellOut : (B C : H.Gr) (a : Bool)
           → Lay (H.boolΠ {M = λ _ → H.Gr} B C a)
           ⊢ boolΠ {M = λ _ → Ctx} (Lay B) (Lay C) a
respellOut B C =
  boolΠ {M = λ a → Lay (H.boolΠ {M = λ _ → H.Gr} B C a)
                 ⊢ boolΠ {M = λ _ → Ctx} (Lay B) (Lay C) a}
        idg idg

-- CONTEXT SPLITTING BECOMES HEAP SEPARATION.  This term is the phase's
-- claim, and its proof is `layPres appop` -- i.e. no-aliasing is not
-- established here, it is what `push⊗` consumed.
lay∗ : (B C : H.Gr) → (Lay B ⊛ Lay C) ⊢ Lay (B H.∗ C)
lay∗ B C =
    A.push⊗ appop (layPres appop) {B = H.boolΠ {M = λ _ → H.Gr} B C}
  ∘g ⊗ˢ-map appop
       {A = boolΠ {M = λ _ → Ctx} (Lay B) (Lay C)}
       {B = λ a → Lay (H.boolΠ {M = λ _ → H.Gr} B C a)}
       (respellIn B C)

-- ... and back, by reflection.  Together: `Lay` is STRONG monoidal.
lay∗⁻ : (B C : H.Gr) → Lay (B H.∗ C) ⊢ (Lay B ⊛ Lay C)
lay∗⁻ B C =
    ⊗ˢ-map appop
      {A = λ a → Lay (H.boolΠ {M = λ _ → H.Gr} B C a)}
      {B = boolΠ {M = λ _ → Ctx} (Lay B) (Lay C)}
      (respellOut B C)
  ∘g A.pull⊗ appop (layRefl appop) {B = H.boolΠ {M = λ _ → H.Gr} B C}

-- the unit, both ways: "no variable left" ⊣⊢ "the empty heap"
layEmp : nothingLeft ⊢ Lay H.emp
layEmp = A.push⊗ nilop (layPres nilop) {B = λ ()}

layEmp⁻ : Lay H.emp ⊢ nothingLeft
layEmp⁻ = A.pull⊗ nilop (layRefl nilop) {B = λ ()}

-- ==================================================================
-- TRANSPORT.  The pass doing real work: two theorems of separation
-- logic become theorems about linear contexts, with no new induction.
-- ==================================================================

-- (a) THE FRAME RULE, pulled back.  `H.frame` is a heap-side term;
-- `pullTerm` reinterprets it, and `lay∗`/`lay∗⁻` transpose it across
-- the monoidal structure.  So the linear calculus inherits framing.
layFrame : {B B' : H.Gr} (C : H.Gr) → B H.⊢ B'
         → (Lay B ⊛ Lay C) ⊢ (Lay B' ⊛ Lay C)
layFrame {B} {B'} C f =
  lay∗⁻ B' C ∘g A.pullTerm (H.frame C f) ∘g lay∗ B C

-- (b) NO VARIABLE IS USED TWICE -- from `apart-self`, the heap-side
-- statement that a location cannot be owned twice.  `Lay H.⌈ h ⌉` is
-- "my context lays out to exactly `h`", so this says: no usage splits
-- into two halves that both lay out to the single cell `l`.  It is
-- `Context.noDupUse`, obtained by TRANSPORT rather than by matching the
-- missing constructor.
noDupLay : (l : H.Loc) (x : H.Val)
         → (Lay H.⌈ H.single l x ⌉ ⊛ Lay H.⌈ H.single l x ⌉) ⊢ ⊥G
noDupLay l x =
  A.pullTerm (H.apart-self l x) ∘g lay∗ H.⌈ H.single l x ⌉ H.⌈ H.single l x ⌉

-- ==================================================================
-- EMITTING CODE.  The output of the pass is the internal existential
-- over the target carrier -- exactly `Lambda/Passes/Framework`'s `Out`,
-- with `Raw` replaced by `Heap`.
-- ==================================================================

Code : Ctx
Code = ⊕ᴰ H.Heap (λ h → Lay H.⌈ h ⌉)

-- PRIMITIVE (phase 1): `⊕ᴰ-I` at the index itself.  This is the ONE
-- place the pass names its own output, and it is `Framework.emit`.
emit : {B : Ctx} → B ⊢ Code
emit u _ = ⊕ᴰ-I H.Heap {A = λ h → Lay H.⌈ h ⌉} (layout u) u (H.⌈⌉-pt (layout u))

-- the emitted heap of a term, as a term of the calculus
emitTm : TmG ⊢ Code
emitTm = emit

-- ==================================================================
-- OBSERVATION.  `run` only in a `refl` line, as the house rule says.
-- ==================================================================

-- a term at usage `true ∷ []` (one live variable) and one at
-- `true ∷ true ∷ []` (two), so the tests are not all about the empty heap
xVar : Tm (true ∷ [])
xVar = tvar tt

twoSplit : Use⊎ (true ∷ false ∷ []) (false ∷ true ∷ []) (true ∷ true ∷ [])
twoSplit = uleft (uright unil)

twoVar : Tm (true ∷ true ∷ [])
twoVar = tapp twoSplit (tvar tt) (tvar tt)

-- the layout itself
_ : layout [] ≡ []
_ = refl

_ : layout (true ∷ []) ≡ H.single 0 H.v1
_ = refl

_ : layout (true ∷ false ∷ true ∷ []) ≡ (0 , H.v1) ∷ (2 , H.v1) ∷ []
_ = refl

-- CODE EMITTED FROM CLOSED TERMS.  `idLin` and `selfApp` are closed, so
-- their frame is the empty heap: a closed linear term allocates nothing.
_ : emitTm [] idLin .fst ≡ []
_ = refl

_ : emitTm [] selfApp .fst ≡ []
_ = refl

-- ... and from open ones, where the layout has content
_ : emitTm (true ∷ []) xVar .fst ≡ H.single 0 H.v1
_ = refl

_ : emitTm (true ∷ true ∷ []) twoVar .fst ≡ (0 , H.v1) ∷ (1 , H.v1) ∷ []
_ = refl

-- ==================================================================
-- THE POINT, as a `refl`: the application in `twoVar` splits its
-- context, and `layPres appop` turns that into two DISJOINT regions.
-- The last component is the `_#_` proof -- it reduces to a nest of `tt`,
-- which is the statement that disjointness held on the nose.
-- ==================================================================

_ : layPres appop .homSplit (true ∷ true ∷ [])
      (true ∷ false ∷ [] , false ∷ true ∷ [] , twoSplit)
  ≡ ( H.single 0 H.v1
    , H.single 1 H.v1
    , H.left (H.right H.nil)
    , ((tt , tt) , tt) )
_ = refl

-- and reflection inverts it: the disjoint heap split reads back as the
-- context split it came from
_ : layRefl appop (true ∷ true ∷ [])
      ( H.single 0 H.v1 , H.single 1 H.v1
      , H.left (H.right H.nil) , ((tt , tt) , tt) ) .fst
  ≡ (true ∷ false ∷ [] , false ∷ true ∷ [] , twoSplit)
_ = refl

-- ==================================================================
-- THE NEGATIVE HALF: the COMPACTING layout is not split-preserving.
--
-- `compact` drops the dead positions, so every frame is as small as it
-- can be and the live variables are addressed consecutively from 0.
-- That is what a real allocator does, and it is exactly what breaks:
-- compaction is injective on each usage SEPARATELY but not stably across
-- a split, so the two premises of an application both claim location 0.
--
-- This is the counterweight to `layPres`.  Split preservation is a
-- genuine constraint on the layout, not a formality -- and `CarrierMap`
-- localises the failure at ONE operation of ONE pass.
-- ==================================================================

compact : Usage → Usage                                -- PRIMITIVE
compact []          = []
compact (true  ∷ u) = true ∷ compact u
compact (false ∷ u) = compact u

pack : Usage → H.Heap
pack u = layout (compact u)

packMap : Reindex linFib H.heapFib
packMap .hom _ = pack

-- both premises of `twoVar`'s application compact to the SAME cell ...
_ : pack (true ∷ false ∷ []) ≡ H.single 0 H.v1
_ = refl

_ : pack (false ∷ true ∷ []) ≡ H.single 0 H.v1
_ = refl

-- ... so `SplitPresAt` would hand us `single 0 v1 # single 0 v1`, and
-- `H.#-self` -- the one fact `Heap/Connectives` turns on -- refutes it.
-- Phase 2: `split-#`, `#-Eq`, `#-self`, all already primitives there.
noPackPres : SplitPresAt packMap appop → ⊥
noPackPres P =
  H.#-self 0 H.v1
    (H.#-Eq (P .homParts u sp true) (P .homParts u sp false)
            (H.split-# (pack u) (P .homSplit u sp)))
  where
  u : Usage
  u = true ∷ true ∷ []

  sp : linFib .Split appop u
  sp = true ∷ false ∷ [] , false ∷ true ∷ [] , twoSplit
