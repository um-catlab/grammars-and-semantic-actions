{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  COMPILING THE LINEAR λ-CALCULUS INTO PURE RUST, AND THE SIMULATION
  SQUARE THAT SAYS THE EMITTED SOURCE MEANS WHAT THE TERM MEANS.

  ------------------------------------------------------------------
  THE TRANSLATION IS CLOSE TO THE IDENTITY
  ------------------------------------------------------------------

      compileE d (tvar s)      = rVar (nameOf d (soloPos s))
      compileE d (tapp _ f a)  = rCall (compileE d f) (compileE d a)
      compileE d (tlam b)      = rClos d (compileE (suc d) b)

  Three clauses, no arithmetic, no environment, no renaming pass.  The
  ONLY thing the compiler decides is a NAME, and `nameOf` decides it in
  three clauses too:

      nameOf zero    p       = fre p        -- a free variable, `yp`
      nameOf (suc d) zero    = bnd d        -- the innermost binder, `xd`
      nameOf (suc d) (suc p) = nameOf d p

  i.e. a de Bruijn INDEX under `d` binders becomes a de Bruijn LEVEL,
  and anything reaching past the binders is a free variable of the
  initial context.  Levels, because Rust source has names and levels
  are the naming scheme under which no two binders on a path collide
  and no variable is ever shadowed -- which is what makes `Eval`'s
  naive substitution correct.

  ------------------------------------------------------------------
  WHERE THE LINEARITY GUARANTEE LIVES
  ------------------------------------------------------------------

      compileTm : L.TmG L.⊢ Obj,      Obj = ⊕ᴰ RExpr Scoped
      Scoped e u = Uses e (Names 0 u)

  `L._⊢_` PRESERVES THE USAGE, so a term of this type cannot compile a
  source term at one usage into Rust for another.  And the payload is
  not a bare well-scopedness claim: `Uses e l` is a LINEAR use
  judgement for the Rust fragment -- `uCall` splits the name list by an
  interleaving, so the callee and the argument use DISJOINT names, and
  `uClos` requires the binder's own name to be among the body's uses.
  So `Scoped e u` says:

      the emitted Rust uses each of `u`'s live names EXACTLY ONCE.

  That is the ownership property, stated about the output, and it is
  what makes the "borrow checker accepts this" claim in `Syntax`'s
  header formal rather than rhetorical: every `move` capture is the
  unique consumer of a uniquely-owned binding, so no `&`, no `Clone`
  and no `drop` is ever required.

  The proof, `usesCompile`, is three clauses plus four small list
  lemmas, and its `tapp` clause is

      ilvNames : Use⊎ u₁ u₂ u → IlvI (names d p u₁) (names d p u₂)
                                     (names d p u)

  -- constructor for constructor, `uleft ↦ ileft`, `uright ↦ iright`,
  `uskip ↦ id`, `unil ↦ inil`, with no arithmetic anywhere in it.  It
  is `LinLam/Codegen.ilvLay` with heap cells replaced by identifiers,
  and it says the same thing: the source's SPLITTING becomes the
  target's DISJOINTNESS, and the missing `(true,true)` constructor of
  `Use⊎` is what supplies it.  Nothing about aliasing is proved here;
  it arrives from the source promodel.

  Note the corollary at `u = []`: `Names 0 [] = []`, so a CLOSED linear
  term compiles to a Rust expression with no free names -- which is
  exactly the hypothesis under which `Eval`'s semantics does not get
  stuck.

  ------------------------------------------------------------------
  THE CORRECTNESS STATEMENT, AND THE SOURCE SEMANTICS IT ASSUMES
  ------------------------------------------------------------------

  An equation between VALUES.  No heap, no separation logic, no Hoare
  triple:

      Simulates = (t v : Tm []) → t ⇓ₛ v → compileRust t ⇓ compileRust v

  `_⇓_` is `Eval`'s big-step relation.  `_⇓ₛ_` is NOT defined here: it
  is the parameter of the module `Simulation`, so that
  `Compile/Semantics/` -- a sibling's source evaluator/normaliser for
  the same calculus -- can be plugged in with no rework.

  WHAT SHAPE OF SOURCE SEMANTICS IS ASSUMED, precisely:

    (S1) A relation `_⇓ₛ_ : Tm [] → Tm [] → Type₀` on CLOSED terms.
         Closed, because `Eval`'s `rVar` is stuck: an open term has a
         free `yp` in the emitted Rust and no value to evaluate to.
         (`Uses` above is what identifies "closed" with `Names 0 [] =
         []`.)
    (S2) CALL BY VALUE, in Rust's order: callee, then argument, then
         body.  This is what `⇓call` fixes, and it is not negotiable
         because it is Rust's evaluation order.  A source semantics
         that is call-by-name will not square with it.
    (S3) VALUES ARE λs.  A source value must compile to an `IsVal`,
         i.e. to an `rClos`.  This is not a further assumption: it is
         DISCHARGED here by `lamIsVal`, for `tlam`, which is the only
         whnf the untyped λ-calculus has -- so a source semantics whose
         values are λs squares automatically on this corner, and
         `targetIsVal` derives it for whatever `_⇓ₛ_` supplies.

  NOTHING ELSE is assumed -- in particular no normalisation, no
  confluence and no typing.  `Simulation` derives, from `Simulates` alone
  and `Eval.⇓-det`, that the executable evaluator's answer on the
  emitted Rust is FORCED to be the compilation of the source value
  (`evalAgrees`), which is the form a test or a downstream client
  actually wants.

  This file does NOT prove `Simulates`.  Doing so needs the substitution
  lemma `compileE d (t [v]) ≡ substE (bnd _) (compileE d v) (compileE
  (suc d) t)`, which cannot even be STATED without the source's
  substitution operator -- that operator lives in `Compile/Semantics/`
  and does not exist yet.  What is here instead is: the square's
  statement, its parameterisation, its consequences, the value corner
  (`lamIsVal`, `compileVal`) proved outright, and a `refl` block in
  which every closed test term is compiled, printed and RUN, so that
  each instance of the square is checked by computation.

  ------------------------------------------------------------------
  EXTERNALISING LATE
  ------------------------------------------------------------------

  No producer in this file mentions `String` in its type.  The
  text-level producer is

      srcTm : L.TmG L.⊢ Δ String
      srcTm = Δ-map renderUnit ∘g exprA ∘g compileTm

  -- `Δ` is `TheoryGrammar.SemanticAction`'s discrete type, `exprA` is
  `⊕ᴰ-E` reading the expression out of `Obj`, and the printer is
  applied INSIDE `Δ-map`, i.e. as a semantic action rather than as an
  exit.  The only exit is `runAt`, and it occurs solely in the `refl`
  block at the bottom, where the emitted Rust is quoted as a literal.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1, all marked: `nameOf`, `soloAt`, `compileE`, `names`,
  `IlvI`, `Uses`, `usesCompile` and the four list lemmas -- recursions
  on a usage, on a term or on a list, i.e. on a carrier, which is what
  building a pass is allowed to do.  `compileTm` is `⊕ᴰ-I` at the
  index itself (`LinLam/Codegen.emit`'s shape, marked there too), and
  everything from `exprA` down is a composite of `⊕ᴰ-E`, `Δ-map`,
  `pureA` and `∘g`.
-}
open import Cubical.Foundations.Prelude

module Compile.LinToRust.Codegen where

open import Agda.Builtin.String using (String)
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Theories.Monoid
import TheoryGrammar.SemanticAction as SA

-- the TARGET, unqualified
open import Compile.LinToRust.Eval public

-- the SOURCE, qualified.  NOTE: `LinLam.Syntax`, not `LinLam.Codegen`
-- -- the latter imports `Heap.Graded`, and this backend mentions no
-- heap at any point.
import TheoryGrammar.Instances.LinLam.Syntax as L

-- the discrete type at the SOURCE theory: `Δ X u = X × Unit*`, a
-- payload that does not depend on the usage.  This is how a `String`
-- gets to be the codomain of a `⊢` without appearing in one.
module LA = SA.Act {σ = monoidSig} (L.linFib .carrier)
open LA using (Δ)

-- ==================================================================
-- NAMES.  PRIMITIVE (phase 1).
--
-- `nameOf d p`: the identifier for de Bruijn index `p` under `d`
-- binders.  Indices below `d` are binders and become LEVELS; the rest
-- reach past every binder and are free variables of the initial
-- context.  Three clauses, no subtraction, no comparison.
-- ==================================================================

nameOf : ℕ → ℕ → Ident
nameOf zero    p       = fre p
nameOf (suc d) zero    = bnd d
nameOf (suc d) (suc p) = nameOf d p

-- PRIMITIVE (phase 1): the position of the unique live variable of a
-- `Solo` usage, counted from `p`.
soloAt : ℕ → (u : L.Usage) → L.Solo u → ℕ
soloAt p []          ()
soloAt p (true  ∷ u) e = p
soloAt p (false ∷ u) s = soloAt (suc p) u s

-- ==================================================================
-- THE TRANSLATION.  PRIMITIVE (phase 1): structural on the term, and
-- the ONE recursion over `Tm` in this backend.
-- ==================================================================

compileE : ℕ → {u : L.Usage} → L.Tm u → RExpr
compileE d (L.tvar {u} s)   = rVar (nameOf d (soloAt 0 u s))
compileE d (L.tapp s f a)   = rCall (compileE d f) (compileE d a)
compileE d (L.tlam b)       = rClos d (compileE (suc d) b)

compileRust : {u : L.Usage} → L.Tm u → RExpr
compileRust = compileE 0

-- ==================================================================
-- THE NAMES A USAGE LICENSES.  `names` is `LinLam/Codegen.lay` with
-- heap cells replaced by identifiers -- same recursion, same offset
-- argument, same reason (a usage carries no absolute names, so the
-- tail must be told where it starts).
-- ==================================================================

-- PRIMITIVE (phase 1)
names : ℕ → ℕ → L.Usage → List Ident
names d p []          = []
names d p (true  ∷ u) = nameOf d p ∷ names d (suc p) u
names d p (false ∷ u) = names d (suc p) u

Names : ℕ → L.Usage → List Ident
Names d = names d 0

-- ==================================================================
-- INTERLEAVING OF NAME LISTS, and THE LINEAR USE JUDGEMENT.
--
-- `Uses e l` is "the free identifiers of `e` are exactly the multiset
-- `l`, each consumed once".  `uCall` splits by an interleaving, so a
-- callee and its argument own DISJOINT names; `uMatch` gives both arms
-- the SAME names, which is the additive rule and the reason a `match`
-- does not duplicate ownership.
-- ==================================================================

data IlvI : List Ident → List Ident → List Ident → Type₀ where  -- PRIMITIVE
  inil   : IlvI [] [] []
  ileft  : ∀ {x l₁ l₂ l} → IlvI l₁ l₂ l → IlvI (x ∷ l₁) l₂ (x ∷ l)
  iright : ∀ {x l₁ l₂ l} → IlvI l₁ l₂ l → IlvI l₁ (x ∷ l₂) (x ∷ l)

ilvI-nilL : (l : List Ident) → IlvI [] l l                      -- PRIMITIVE
ilvI-nilL []      = inil
ilvI-nilL (x ∷ l) = iright (ilvI-nilL l)

-- ... and along an `Eq`, so nothing downstream needs a `subst` at a
-- family over a variable list
ilvI-nilL≡ : {l l' : List Ident} → l Eq.≡ l' → IlvI [] l l'
ilvI-nilL≡ {l} Eq.refl = ilvI-nilL l

data Uses : RExpr → List Ident → Type₀ where                    -- PRIMITIVE
  uVar   : (x : Ident) → Uses (rVar x) (x ∷ [])
  uCall  : {f a : RExpr} {l₁ l₂ l : List Ident}
         → Uses f l₁ → Uses a l₂ → IlvI l₁ l₂ l → Uses (rCall f a) l
  uClos  : {n : ℕ} {b : RExpr} {l l' : List Ident}
         → Uses b l' → IlvI (bnd n ∷ []) l l' → Uses (rClos n b) l
  uCtor  : (c : Ctor) → Uses (rCtor c) []
  uMatch : {s a b : RExpr} {l₁ l₂ l : List Ident}
         → Uses s l₁ → Uses a l₂ → Uses b l₂ → IlvI l₁ l₂ l
         → Uses (rMatch s a b) l
  uLet   : {n : ℕ} {e b : RExpr} {l₁ l₂ l l' : List Ident}
         → Uses e l₁ → Uses b l' → IlvI (bnd n ∷ []) l₂ l'
         → IlvI l₁ l₂ l → Uses (rLet n e b) l

-- coercion of the name list along `Eq` -- one `Eq.refl` match, kept
-- out of every theorem below
coeUses : {e : RExpr} {l l' : List Ident} → l Eq.≡ l' → Uses e l → Uses e l'
coeUses Eq.refl h = h

-- ==================================================================
-- THE FOUR LIST LEMMAS.  All PRIMITIVE (phase 1), all recursions on a
-- usage, none of them arithmetic.
-- ==================================================================

-- an exhausted usage licenses no names
namesEmpty : (d p : ℕ) (u : L.Usage) → L.Empty u → names d p u Eq.≡ []
namesEmpty d p []          e = Eq.refl
namesEmpty d p (true  ∷ u) e = E.rec e
namesEmpty d p (false ∷ u) e = namesEmpty d (suc p) u e

-- a `Solo` usage licenses exactly one, at its own position
namesSolo : (d p : ℕ) (u : L.Usage) (s : L.Solo u)
          → names d p u Eq.≡ (nameOf d (soloAt p u s) ∷ [])
namesSolo d p []          ()
namesSolo d p (true  ∷ u) e = Eq.ap (nameOf d p ∷_) (namesEmpty d (suc p) u e)
namesSolo d p (false ∷ u) s = namesSolo d (suc p) u s

-- going under a binder shifts depth and position together, and
-- `nameOf (suc d) (suc p) = nameOf d p` on the nose, so the licensed
-- names are unchanged
namesShift : (d p : ℕ) (u : L.Usage) → names d p u Eq.≡ names (suc d) (suc p) u
namesShift d p []          = Eq.refl
namesShift d p (true  ∷ u) = Eq.ap (nameOf d p ∷_) (namesShift d (suc p) u)
namesShift d p (false ∷ u) = namesShift d (suc p) u

-- THE SPLITTING LEMMA.  `LinLam/Codegen.ilvLay`, with cells replaced
-- by identifiers: constructor for constructor, no arithmetic.  This is
-- where the source's linearity becomes the target's disjointness.
ilvNames : ∀ {u₁ u₂ u} → L.Use⊎ u₁ u₂ u → (d p : ℕ)
         → IlvI (names d p u₁) (names d p u₂) (names d p u)
ilvNames L.unil       d p = inil
ilvNames (L.uleft  s) d p = ileft  (ilvNames s d (suc p))
ilvNames (L.uright s) d p = iright (ilvNames s d (suc p))
ilvNames (L.uskip  s) d p = ilvNames s d (suc p)

-- ==================================================================
-- THE EMITTED RUST IS LINEAR IN EXACTLY THE SOURCE'S NAMES.
--
-- Three clauses, one per constructor of `Tm`.  Nothing about aliasing
-- is established here: `uCall`'s third argument IS `ilvNames`, i.e.
-- the `Use⊎` the source term already carried.
-- ==================================================================

usesCompile : (d : ℕ) {u : L.Usage} (t : L.Tm u)
            → Uses (compileE d t) (Names d u)
usesCompile d (L.tvar {u} s) =
  coeUses (Eq.sym (namesSolo d 0 u s)) (uVar (nameOf d (soloAt 0 u s)))
usesCompile d (L.tapp s f a) =
  uCall (usesCompile d f) (usesCompile d a) (ilvNames s d 0)
usesCompile d (L.tlam {u} b) =
  uClos (usesCompile (suc d) b) (ileft (ilvI-nilL≡ (namesShift d 0 u)))

-- ==================================================================
-- COMPILATION AS A TERM OF THE CALCULUS.
--
-- A point of `Obj u` is "a Rust expression, together with a proof that
-- it uses exactly `u`'s live names, exactly once each".  `L._⊢_`
-- preserves the usage, so this type FORBIDS compiling a term at one
-- usage into Rust for another.
-- ==================================================================

Scoped : RExpr → L.Ctx
Scoped e u = Uses e (Names 0 u)

Obj : L.Ctx
Obj = L.⊕ᴰ RExpr Scoped

-- PRIMITIVE (phase 1): `⊕ᴰ-I` at the index itself.  The ONE place the
-- pass names its own output; `LinLam/Codegen.emit` has the same shape
-- and the same marking.
compileTm : L.TmG L.⊢ Obj
compileTm u t = L.⊕ᴰ-I RExpr {A = Scoped} (compileRust t) u (usesCompile 0 t)

-- CLOSED IN, CLOSED OUT.  `Names 0 [] = []`, so this is `compileTm` at
-- the empty usage read off definitionally -- and it is the hypothesis
-- under which `Eval` does not get stuck on a free `yp`.
compileClosed : (t : L.Tm []) → Uses (compileRust t) []
compileClosed t = usesCompile 0 t

-- ==================================================================
-- THE SOURCE TEXT, AS A `⊢`-TERM INTO `Δ String`.
-- ==================================================================

exprA : LA.Action Obj RExpr
exprA = L.⊕ᴰ-E {Y = RExpr} {A = Scoped} (λ e → LA.pureA RExpr e)

-- the emitted expression, as a term
exprTm : L.TmG L.⊢ Δ RExpr
exprTm = exprA L.∘g compileTm

-- ... and the emitted SOURCE TEXT.  `renderUnit` is applied inside
-- `Δ-map`, so it is a semantic action and not an exit.
srcTm : L.TmG L.⊢ Δ String
srcTm = LA.Δ-map renderUnit L.∘g exprTm

-- just the expression, without the `enum`/`main` wrapper
exprTextTm : L.TmG L.⊢ Δ String
exprTextTm = LA.Δ-map renderExpr L.∘g exprTm

-- THE EXIT.  `SemanticAction.run` is `⊤G ⊢ Δ X → Car s → X`; a
-- producer whose domain is a nonempty grammar exits at a POINT of that
-- grammar instead, which is the same projection.  Used only in `refl`
-- lines.
runAt : {X : Type₀} {A : L.Ctx} → A L.⊢ Δ X → (u : L.Usage) → A u → X
runAt f u a = f u a .fst

-- ==================================================================
-- THE VALUE CORNER OF THE SQUARE, PROVED OUTRIGHT.
--
-- A source λ compiles to a Rust closure, hence to an `IsVal`, hence
-- evaluates to itself.  This is assumption (S3) of the source
-- semantics, discharged for the only whnf the untyped λ-calculus has.
-- ==================================================================

lamIsVal : {u : L.Usage} (b : L.Tm (true ∷ u)) (d : ℕ)
         → IsVal (compileE d (L.tlam b))
lamIsVal b d = valClos d (compileE (suc d) b)

compileVal : {u : L.Usage} (b : L.Tm (true ∷ u)) (d : ℕ)
           → compileE d (L.tlam b) ⇓ compileE d (L.tlam b)
compileVal b d = ⇓clos d (compileE (suc d) b)

-- ==================================================================
-- THE SIMULATION SQUARE, PARAMETERISED OVER THE SOURCE SEMANTICS.
--
-- `Compile/Semantics/` supplies `_⇓ₛ_`; this module supplies
-- everything that follows from the square once it holds.  See the
-- header for the exact shape assumed: closed terms (S1), call by value
-- in Rust's order (S2), values are λs (S3).
-- ==================================================================

module Simulation (_⇓ₛ_ : L.Tm [] → L.Tm [] → Type₀) where

  -- THE CORRECTNESS STATEMENT.  An equation between VALUES.
  Simulates : Type₀
  Simulates = (t v : L.Tm []) → t ⇓ₛ v → compileRust t ⇓ compileRust v

  module _ (sq : Simulates) where

    -- the compiled source value really is a Rust value
    targetIsVal : (t v : L.Tm []) → t ⇓ₛ v → IsVal (compileRust v)
    targetIsVal t v r = ⇓-isVal (sq t v r)

    -- THE FORM A CLIENT WANTS.  Determinism of the target semantics
    -- (`Eval.⇓-det`) upgrades the square from "there is a derivation"
    -- to "the answer is FORCED": whatever value the emitted Rust
    -- evaluates to, at whatever budget, is the compilation of the
    -- source normal form.
    evalAgrees : (t v : L.Tm []) → t ⇓ₛ v
               → (w : RExpr) → compileRust t ⇓ w → w Eq.≡ compileRust v
    evalAgrees t v r w d = ⇓-det d (sq t v r)

    -- ... and the same read off the EXECUTABLE evaluator, which
    -- carries its own derivation, so no extra soundness lemma is
    -- needed.  `k` is any budget that suffices.
    execAgrees : (t v : L.Tm []) → t ⇓ₛ v → (k : ℕ)
               → (r : Σ[ w ∈ RExpr ] (compileRust t ⇓ w))
               → evalRust k (compileRust t) Eq.≡ just r
               → r .fst Eq.≡ compileRust v
    execAgrees t v s k r _ = evalAgrees t v s (r .fst) (r .snd)

-- ==================================================================
-- SOURCE TERMS FOR THE TESTS.  `idLin` and `selfApp` are
-- `LinLam.Syntax`'s; the rest are defined here because
-- `LinLam.Codegen` -- where the others live -- imports `Heap.Graded`,
-- and this backend mentions no heap.
-- ==================================================================

xVar : L.Tm (true ∷ [])
xVar = L.tvar tt

twoSplit : L.Use⊎ (true ∷ false ∷ []) (false ∷ true ∷ []) (true ∷ true ∷ [])
twoSplit = L.uleft (L.uright L.unil)

-- `x y` at two live variables
twoVar : L.Tm (true ∷ true ∷ [])
twoVar = L.tapp twoSplit (L.tvar tt) (L.tvar tt)

-- a scope of THREE with the middle variable DEAD
gapSplit : L.Use⊎ (true ∷ false ∷ false ∷ []) (false ∷ false ∷ true ∷ [])
                  (true ∷ false ∷ true ∷ [])
gapSplit = L.uleft (L.uskip (L.uright L.unil))

gapTm : L.Tm (true ∷ false ∷ true ∷ [])
gapTm = L.tapp gapSplit (L.tvar tt) (L.tvar tt)

-- `λf. λx. f x` -- closed, linear, and TWO nested binders, so the
-- level-based naming has something to say
appLin : L.Tm []
appLin = L.tlam (L.tlam (L.tapp (L.uright (L.uleft L.unil))
                                (L.tvar tt) (L.tvar tt)))

-- ==================================================================
-- OBSERVATION.  `refl` lines only, as the house rule says.
-- ==================================================================

-- THE TRANSLATION, at the level of the model
_ : compileRust L.idLin ≡ rClos 0 (rVar (bnd 0))
_ = refl

_ : compileRust L.selfApp
  ≡ rCall (rClos 0 (rVar (bnd 0))) (rClos 0 (rVar (bnd 0)))
_ = refl

_ : compileRust appLin
  ≡ rClos 0 (rClos 1 (rCall (rVar (bnd 0)) (rVar (bnd 1))))
_ = refl

-- free variables become `y`s at their own positions ...
_ : compileRust xVar ≡ rVar (fre 0)
_ = refl

_ : compileRust twoVar ≡ rCall (rVar (fre 0)) (rVar (fre 1))
_ = refl

-- ... and a DEAD middle position leaves a GAP in the names, exactly as
-- it leaves a gap in `LinLam/Codegen.lay`'s addresses: `y1` is absent
-- and the second live variable is still `y2`
_ : compileRust gapTm ≡ rCall (rVar (fre 0)) (rVar (fre 2))
_ = refl

-- the licensed names, at the source of that gap
_ : Names 0 (true ∷ false ∷ true ∷ []) ≡ fre 0 ∷ fre 2 ∷ []
_ = refl

_ : Names 0 [] ≡ []
_ = refl

-- ==================================================================
-- THE EMITTED RUST, AS SOURCE TEXT.
--
-- `runAt srcTm u t` is the exit; everything to its left is a `⊢`-term.
-- These are the lines a `rustc` invocation would receive.
-- ==================================================================

-- THE IDENTITY, as a compilation unit
_ : runAt srcTm [] L.idLin
  ≡ "enum U { A, B }\n\nfn main() {\n    let _ = move |x0| x0;\n}\n"
_ = refl

-- the identity applied to itself
_ : runAt exprTextTm [] L.selfApp ≡ "(move |x0| x0)(move |x0| x0)"
_ = refl

-- `λf. λx. f x`: TWO binders, and level-based naming keeps them apart
_ : runAt exprTextTm [] appLin ≡ "move |x0| move |x1| (x0)(x1)"
_ = refl

_ : runAt srcTm [] appLin
  ≡ "enum U { A, B }\n\nfn main() {\n    let _ = move |x0| move |x1| (x0)(x1);\n}\n"
_ = refl

-- an OPEN term: two free variables, used once each
_ : runAt exprTextTm (true ∷ true ∷ []) twoVar ≡ "(y0)(y1)"
_ = refl

-- ... and the gap, in the source text
_ : runAt exprTextTm (true ∷ false ∷ true ∷ []) gapTm ≡ "(y0)(y2)"
_ = refl

-- ==================================================================
-- THE EMITTED RUST ACTUALLY RUNS.  Each of these is one instance of
-- the simulation square, checked by computation: the source term's
-- meaning on the left, the emitted Rust's value on the right.
-- ==================================================================

-- `(λx.x)(λx.x)` evaluates to the identity, in Rust
_ : valOf (evalRust 10 (compileRust L.selfApp)) ≡ just (rClos 0 (rVar (bnd 0)))
_ = refl

-- the identity, applied to an enum value
_ : valOf (evalRust 10 (rCall (compileRust L.idLin) (rCtor cA)))
  ≡ just (rCtor cA)
_ = refl

-- `λf.λx. f x` applied to the identity and to `U::A`
_ : valOf (evalRust 20 (rCall (rCall (compileRust appLin)
                                     (compileRust L.idLin))
                              (rCtor cA)))
  ≡ just (rCtor cA)
_ = refl

-- the partial application, as a value: `move |x1| (move |x0| x0)(x1)`
_ : valOf (evalRust 20 (rCall (compileRust appLin) (compileRust L.idLin)))
  ≡ just (rClos 1 (rCall (rClos 0 (rVar (bnd 0))) (rVar (bnd 1))))
_ = refl

-- an OPEN term is STUCK -- which is why `Scoped` at `u = []` is the
-- hypothesis of the correctness statement, and not a decoration
_ : valOf (evalRust 10 (compileRust twoVar)) ≡ nothing
_ = refl

-- ==================================================================
-- THE LINEARITY PAYLOAD, EVALUATED.  `compileTm u t .snd` is the proof
-- that the emitted Rust uses each of `u`'s names exactly once; at
-- `twoVar` its interleaving is the source's `Use⊎`, constructor for
-- constructor.
-- ==================================================================

_ : ilvNames twoSplit 0 0 ≡ ileft (iright inil)
_ = refl

_ : ilvNames gapSplit 0 0 ≡ ileft (iright inil)
_ = refl

_ : compileTm (true ∷ true ∷ []) twoVar .fst
  ≡ rCall (rVar (fre 0)) (rVar (fre 1))
_ = refl

_ : compileTm (true ∷ true ∷ []) twoVar .snd
  ≡ uCall (uVar (fre 0)) (uVar (fre 1)) (ileft (iright inil))
_ = refl
