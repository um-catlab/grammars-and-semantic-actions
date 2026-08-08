{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE EMITTED RUST FRAGMENT, AS A THEORY -- AND WHAT IS AND IS NOT
  WELL BEHAVED IN IT.

  ------------------------------------------------------------------
  §0  WHAT THE CARRIER IS, AND WHY IT IS NOT `RExpr`
  ------------------------------------------------------------------

  There are three obvious candidates for the carrier of a promodel of
  the target language, and two of them are wrong for a reason worth
  stating.

    * RExpr ITSELF, with `Split o e` = "e is headed by o".  This is the
      SYNTACTIC promodel (`LinLam/DB`'s `IsDLam`/`mkDApp` at another
      alphabet).  It is a perfectly good `Fibered`, and it is useless
      here: a `⊢`-term over it preserves THE EXPRESSION, so the whole
      calculus collapses to "predicates on a fixed term".  Nothing is
      being decomposed except the abstract syntax tree, which the
      metalanguage already decomposes for free.

    * EVALUATION CONTEXTS, with `Split` = plugging.  These decompose a
      REDUCTION, not a resource, and `_⇓_` here is big-step: there are
      no contexts in the semantics to be a promodel of.

    * THE OWNED NAMES -- `Own = List Ident`.  This is the one that
      carries content, and the argument is exactly the one
      `LinLam/Context` makes for `Usage`:

          a `⊢`-term over `Own` can neither invent nor drop an owned
          name, so ownership-correctness of a target transformation is
          FREE rather than a separate obligation.

      It is also not a guess.  `Codegen.Uses e l` is already a family
      indexed by a `List Ident`, its constructors already split that
      index -- `uCall` by an interleaving, `uMatch` additively, `uClos`
      by adjoining the binder -- and those splittings are precisely the
      `Split` of a promodel.  The theory below is `Uses`'s index,
      promoted from an annotation to a carrier; `UsesG = ⊕ᴰ RExpr Uses`
      is then a GRAMMAR over it, and the six constructors of `Uses`
      become six `⊗ˢ`-intro rules (§4).

  So: the carrier is the RESOURCE (who owns which identifier), and the
  Rust expression is the PAYLOAD.  That is the same division as
  `linFib` (carrier `Usage`, payload `Tm`) and as `heapFib` (carrier
  `Heap`, payload a program), and it is what makes the compiler a
  `Pass` in §5 rather than a bare `Link`.

  ------------------------------------------------------------------
  §0.1  THE SIGNATURE IS SINGLE-SORTED, AND THE BINDER IS STILL THE
        PROBLEM -- JUST NOT THAT PROBLEM
  ------------------------------------------------------------------

  One operation per constructor of `RExpr`, and nothing else; the
  fragment `Syntax.agda` fixes is the fragment axiomatised here.  Two of
  the operations carry a parameter, exactly as `Machine.LI`'s `putI`
  carries an address:

      varOp x   nullary    rVar x
      closOp n  unary      rClos n ·        -- A BINDER
      callOp    binary     rCall · ·
      ctorOp c  nullary    rCtor c
      matchOp   ternary    rMatch · · ·
      letOp n   binary     rLet n · ·       -- ALSO a binder

  IS THE BINDER A SORT PROBLEM?  No, and it is worth being precise,
  because `Scope.¬presLam` makes it look as though it must be.  There
  the binder moved the target from scope `j` to scope `suc j`, and
  `suc j` is a DIFFERENT SORT, which is what made `homParts` unstatable.
  Here the body's resource `bnd n ∷ l` is another element of the SAME
  carrier, so one sort suffices and `parts` is a total function into it.

  What the binder costs instead is TOTALITY, and that is proved, not
  asserted:

      noPoint : LaxPoint rustFib → ⊥              (§8a)

  A `LaxPoint` would have to produce, from the body's resource, the
  closure's own -- i.e. DELETE the binder's name -- and deletion is
  partial: it is undefined exactly when the body does not own `bnd n`.
  The witness is `closOp 0` at the empty tuple.  So `rustFib` is a
  genuine promodel: the whole `⊗ˢ`/`⊸ˢ` layer is available (it needs
  only `Split`), and `⊗[ o ]`, `Model` and `Honest` are not.  This is
  the case `Fibered.agda`'s header says the record split exists for,
  arrived at from the target language rather than from separation logic.

  The second cost is that the binder is the one operation at which the
  resource GROWS (`closGrows`, §8b), so there is no length-based
  `Grading` (`noLenGrading`) and hence no structural recursion over the
  TARGET's splittings.  Which is fine, and is what the backend already
  does: `compileE` recurses over the SOURCE term.

  ------------------------------------------------------------------
  §0.2  WHAT IS PROVED
  ------------------------------------------------------------------

      rustPass       : Pass linTheory rustTheory
      rustReflective : Reflective rustPass

  The compiler's NAME ALLOCATION (`Names 0 : Usage → Own`) is a
  verified, reflective pass from the linear-context theory to the Rust
  ownership theory.  Preservation at `appop` is `Codegen.ilvNames`
  verbatim -- the source's `Use⊎` IS the target's `IlvI` -- and at
  `nilop` it is `namesEmpty`.  Reflection is the converse induction
  (`splitNames`): every interleaving of the emitted names comes from a
  splitting of the usage.

  Contrast `Compile.LinToISA.NoTextPres`, which proves the ISA backend
  is NOT a pass into program text.  The difference is exactly the one
  that file names: a text splitting is ORDERED (`++`) and a resource
  splitting is not.  `IlvI` is unordered, so this backend does not pay
  that price and needs no memory-model equation.

  And `Codegen.compileTm` is, on the nose, a term into the pullback of
  the target grammar along that pass:

      compileG : L.TmG L.⊢ RP.pullO UsesG           and  Obj ≡ pullO UsesG

  ------------------------------------------------------------------
  §0.3  THE MODEL, AND THE HONEST LIMIT OF WHAT IT SEES
  ------------------------------------------------------------------

  §4 gives the six `⊗ˢ`-algebra maps (`varR`, `closR`, `callR`,
  `ctorR`, `matchR`, `letR`) that interpret each operation in `UsesG`.
  §7 connects them to `Eval._⇓_`:

      progress : (t : Tm []) → Σ[ w ] (compileRust t ⇓ w)
      runsTm   : ⌈ [] ⌉ & TmG L.⊢ RP.pullO RunsG

  -- every closed linear term compiles to a Rust expression that owns
  NOTHING and EVALUATES, stated internally, with `⌈ [] ⌉` (the
  representable at the empty usage) as the closedness hypothesis.  And
  `Relational.Square.squareDet` restates as

      runsRealises : (t : Tm []) (w : RExpr)
                   → compileRust t ⇓ w → Rel (nameOf 0) (evalV t) w

  i.e. the value the model produces is FORCED to realise the source's.

  WHAT DOES NOT HOLD, AND IS PROVED NOT TO.  The obvious next theorem
  -- "evaluation preserves ownership", `Uses e l → e ⇓ w → Uses w l` --
  needs a substitution lemma for `Uses`, and that lemma is FALSE:

      noSubstUses  (§8c),  witness  rClos 0 ((x0)(x0))

  a closure that owns `bnd 0` and REBINDS it.  `substE` stops at the
  rebinding, so the substituted term still owns `bnd 0` while the
  statement demands it own nothing.  The missing hypothesis is
  non-shadowing -- which is exactly `Relational.Base.rlam`'s premise,
  and exactly the reason `Compile/Relational/` exists.  So the two
  halves of this development meet: the resource theory is a `Pass`
  because `IlvI` is unordered, and the VALUE theory is relational
  because `Ident` can shadow.  Nothing is preserved by working around
  either.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1 throughout, and marked: this file BUILDS a theory (matches on
  `Own`, on `IlvI`, on `Uses`, on a usage).  `compileG`, `appPush` and
  `compileApp` are the exceptions -- they are composites of `push⊗O`,
  `pullTermO` and `∘g`, i.e. phase 2.
-}
open import Cubical.Foundations.Prelude

module Compile.LinToRust.Theory where

open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Nat.Order using (_≤_; _<_; ¬-<-zero)
open import Cubical.Data.List using (List; []; _∷_; length)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Grading using (Grading; deg; deg≤)
open import TheoryGrammar.Theories.Monoid
open import TheoryGrammar.ChangeOfTheory using (SigMor; onSort; onOp; onAr; resEq; sortEq)
open import TheoryGrammar.Reindex.Base
open import TheoryGrammar.Reindex.Pass

-- the compiler, and (transitively) `Eval` and `Syntax`
open import Compile.LinToRust.Codegen

-- the source semantics, the relation, and the repaired square
import Compile.Semantics.CBV as S
import Compile.Relational.Base as R
import Compile.Relational.Square as Q

-- the SOURCE theory, qualified
import TheoryGrammar.Instances.LinLam.Syntax as L

-- ==================================================================
-- §1  THE SIGNATURE OF THE EMITTED FRAGMENT.
--
-- One operation per constructor of `RExpr`, and NOTHING ELSE -- no
-- `mut`, no `Box`, no borrow, because `Syntax.agda` emits none.  The
-- parameters (`Ident`, `ℕ`, `Ctor`) sit in the OPERATION, exactly as
-- `Machine.LI`'s `putI l x` carries its address: they are choices the
-- compiler makes, not slots a term fills.
-- ==================================================================

data RustOp : Type₀ where
  varOp   : Ident → RustOp        -- `x` / `y`
  closOp  : ℕ → RustOp            -- `move |xn| ·`     A BINDER
  callOp  : RustOp                -- `(·)(·)`
  ctorOp  : Ctor → RustOp         -- `U::A` / `U::B`
  matchOp : RustOp                -- `match (·) { … }`
  letOp   : ℕ → RustOp            -- `{ let xn = ·; · }`  ALSO a binder

-- the ternary arity, and its dependent eliminator.  A NAMED function,
-- for the reason `Base.boolΠ` is one: arities have no η.
data Arm : Type₀ where
  aScrut aArmA aArmB : Arm

armΠ : ∀ {ℓ} {M : Arm → Type ℓ}
     → M aScrut → M aArmA → M aArmB → (a : Arm) → M a
armΠ s x y aScrut = s
armΠ s x y aArmA  = x
armΠ s x y aArmB  = y

RustAr : RustOp → Type₀
RustAr (varOp _)  = ⊥
RustAr (closOp _) = Unit
RustAr callOp     = Bool
RustAr (ctorOp _) = ⊥
RustAr matchOp    = Arm
RustAr (letOp _)  = Bool

rustSig : SortedSig Unit ℓ-zero ℓ-zero
rustSig .ops          = RustOp
rustSig .arities      = RustAr
rustSig .sortOf _ _   = tt
rustSig .resultSort _ = tt


-- ==================================================================
-- §2  THE PROMODEL.  Carrier: the identifiers an expression OWNS.
--
-- Read each clause of `Split` against the corresponding constructor of
-- `Codegen.Uses`; they are the same data, with the index promoted to a
-- carrier.
-- ==================================================================

Own : Type₀
Own = List Ident

-- PRIMITIVE (phase 1): `Unit`/`⊥`-valued, in the style of
-- `Syntax.Same`, so no proof ever blocks a `refl`.
IsNilI : Own → Type₀
IsNilI []      = Unit
IsNilI (_ ∷ _) = ⊥

-- PRIMITIVE (phase 1)
EqI : Ident → Ident → Type₀
EqI (bnd m) (bnd n) = Same m n
EqI (fre m) (fre n) = Same m n
EqI (bnd _) (fre _) = ⊥
EqI (fre _) (bnd _) = ⊥

-- PRIMITIVE (phase 1): "the resource is exactly `x`"
OneOf : Ident → Own → Type₀
OneOf x []      = ⊥
OneOf x (y ∷ l) = EqI x y × IsNilI l

-- PRIMITIVE (phase 1).  `varOp`/`ctorOp` are nullary, so their
-- splittings are PREDICATES on the resource, not decompositions; that
-- is how a nullary operation constrains what it may be emitted at.
RustSplit : (o : RustOp) → Own → Type₀
RustSplit (varOp x)  l = OneOf x l
RustSplit (closOp n) l = Σ[ l' ∈ Own ] IlvI (bnd n ∷ []) l l'
RustSplit callOp     l = Σ[ l₁ ∈ Own ] Σ[ l₂ ∈ Own ] IlvI l₁ l₂ l
RustSplit (ctorOp c) l = IsNilI l
RustSplit matchOp    l = Σ[ l₁ ∈ Own ] Σ[ l₂ ∈ Own ] IlvI l₁ l₂ l
RustSplit (letOp n)  l = Σ[ l₁ ∈ Own ] Σ[ l₂ ∈ Own ] Σ[ l' ∈ Own ]
                           (IlvI (bnd n ∷ []) l₂ l' × IlvI l₁ l₂ l)

-- PRIMITIVE (phase 1).  Two clauses are the content:
--   closOp  the BODY owns MORE than the closure -- `bnd n` besides.
--   matchOp the two ARMS own the SAME resource.  That is the additive
--           rule, and it is why a `match` does not duplicate ownership.
RustParts : (o : RustOp) (l : Own) → RustSplit o l → RustAr o → Own
RustParts (varOp x)  l sp ()
RustParts (closOp n) l (l' , _)          _ = l'
RustParts callOp     l (l₁ , l₂ , _)       = boolΠ l₁ l₂
RustParts (ctorOp c) l sp ()
RustParts matchOp    l (l₁ , l₂ , _)       = armΠ l₁ l₂ l₂
RustParts (letOp n)  l (l₁ , l₂ , l' , _)  = boolΠ l₁ l'

rustFib : Fibered rustSig ℓ-zero ℓ-zero
rustFib .carrier _ = Own
rustFib .Split     = RustSplit
rustFib .parts     = RustParts

open FibNotation rustFib

RustG : Type₁
RustG = TheoryTy ℓ-zero tt

-- ==================================================================
-- §3  THE THEORIES.
-- ==================================================================

rustTheory : Theory ℓ-zero ℓ-zero ℓ-zero ℓ-zero ℓ-zero
rustTheory = theory rustSig rustFib

linTheory : Theory ℓ-zero ℓ-zero ℓ-zero ℓ-zero ℓ-zero
linTheory = theory monoidSig L.linFib

-- ==================================================================
-- §4  THE MODEL: `UsesG` INTERPRETS EVERY OPERATION.
--
-- `UsesG l` is "a Rust expression owning exactly `l`, each name once".
-- The six maps below are the `⊗ˢ`-algebra structure -- one per
-- operation, each of them one constructor of `Codegen.Uses` read as an
-- intro rule.  Nothing here is new content; the point is that `Uses`
-- WAS this algebra all along and the theory makes it sayable.
-- ==================================================================

UsesG : RustG
UsesG l = Σ[ e ∈ RExpr ] Uses e l

-- the arity family of a NULLARY operation, once (arities have no η, so
-- it is a named function and not an extended lambda)
noAr : (a : ⊥) → TheoryTy ℓ-zero tt
noAr ()

-- PRIMITIVE (phase 1): the intro rules.  Each matches the splitting,
-- which is what an intro rule does (compare `LinLam/Syntax.appT`).

varR : (x : Ident) → ⊗ˢ (varOp x) noAr ⊢ UsesG
varR x []           (() , _)
varR x (y ∷ [])     (_ , _)      = rVar y , uVar y
varR x (y ∷ z ∷ l)  ((_ , ()) , _)

closR : (n : ℕ) → ⊗ˢ (closOp n) (λ _ → UsesG) ⊢ UsesG
closR n l ((l' , il) , k) = rClos n (k tt .fst) , uClos (k tt .snd) il

callR : ⊗ˢ callOp (boolΠ UsesG UsesG) ⊢ UsesG
callR l ((l₁ , l₂ , il) , k) =
    rCall (k true .fst) (k false .fst)
  , uCall (k true .snd) (k false .snd) il

ctorR : (c : Ctor) → ⊗ˢ (ctorOp c) noAr ⊢ UsesG
ctorR c []      (_ , _)  = rCtor c , uCtor c
ctorR c (_ ∷ _) (() , _)

matchR : ⊗ˢ matchOp (armΠ UsesG UsesG UsesG) ⊢ UsesG
matchR l ((l₁ , l₂ , il) , k) =
    rMatch (k aScrut .fst) (k aArmA .fst) (k aArmB .fst)
  , uMatch (k aScrut .snd) (k aArmA .snd) (k aArmB .snd) il

letR : (n : ℕ) → ⊗ˢ (letOp n) (boolΠ UsesG UsesG) ⊢ UsesG
letR n l ((l₁ , l₂ , l' , ib , il) , k) =
    rLet n (k true .fst) (k false .fst)
  , uLet (k true .snd) (k false .snd) ib il

-- ==================================================================
-- §5  THE PASS.  `Names 0 : Usage → Own`, over the signature morphism
-- that reads the monoid as the multiplicative fragment of Rust:
--
--     appop ↦ callOp      a linear split becomes a CALL
--     nilop ↦ ctorOp cA   the empty usage becomes a CONSTANT
--
-- `nilop` may go to any nullary operation; `ctorOp cA` is chosen
-- because `U::A` is the fragment's canonical closed value.  Both have
-- arity `⊥`, so `onAr nilop` is `λ ()` and `homPartsO` at `nilop` is
-- vacuous -- the whole content of the pass is at `callOp`.
-- ==================================================================

φ : SigMor monoidSig rustSig
φ .onSort _    = tt
φ .onOp nilop  = ctorOp cA
φ .onOp appop  = callOp
φ .onAr nilop  ()
φ .onAr appop b = b
φ .resEq _     = Eq.refl
φ .sortEq _ _  = Eq.refl

namesOver : ReindexOver φ L.linFib rustFib
namesOver .homO _ u = Names 0 u

-- ------------------------------------------------------------------
-- the two list lemmas the pass needs, and their converses.  Both are
-- `Codegen`'s `namesEmpty` in `Unit`/`⊥` form, in both directions.
-- ------------------------------------------------------------------

-- PRIMITIVE (phase 1)
namesNil : (d p : ℕ) (u : L.Usage) → L.Empty u → IsNilI (names d p u)
namesNil d p []          e = tt
namesNil d p (true  ∷ u) e = E.rec e
namesNil d p (false ∷ u) e = namesNil d (suc p) u e

-- PRIMITIVE (phase 1)
namesNil← : (d p : ℕ) (u : L.Usage) → IsNilI (names d p u) → L.Empty u
namesNil← d p []          h = tt
namesNil← d p (true  ∷ u) ()
namesNil← d p (false ∷ u) h = namesNil← d (suc p) u h

-- THE SPLITTING LEMMA, BACKWARDS.  PRIMITIVE (phase 1): every
-- interleaving of the emitted names comes from a `Use⊎` of the usage,
-- constructor for constructor -- `ileft ↦ uleft`, `iright ↦ uright`,
-- and a dead slot contributes `uskip` with nothing to split.  This is
-- `Codegen.ilvNames` run in reverse and it is what makes the pass
-- REFLECTIVE.
splitNames : (d p : ℕ) (u : L.Usage) {l₁ l₂ : Own}
           → IlvI l₁ l₂ (names d p u)
           → Σ[ u₁ ∈ L.Usage ] Σ[ u₂ ∈ L.Usage ]
               (L.Use⊎ u₁ u₂ u
                × (l₁ Eq.≡ names d p u₁) × (l₂ Eq.≡ names d p u₂))
splitNames d p []          inil       = [] , [] , L.unil , Eq.refl , Eq.refl
splitNames d p (true  ∷ u) (ileft il) =
  let (u₁ , u₂ , s , e₁ , e₂) = splitNames d (suc p) u il
  in true ∷ u₁ , false ∷ u₂ , L.uleft s
   , Eq.ap (nameOf d p ∷_) e₁ , e₂
splitNames d p (true  ∷ u) (iright il) =
  let (u₁ , u₂ , s , e₁ , e₂) = splitNames d (suc p) u il
  in false ∷ u₁ , true ∷ u₂ , L.uright s
   , e₁ , Eq.ap (nameOf d p ∷_) e₂
splitNames d p (false ∷ u) il =
  let (u₁ , u₂ , s , e₁ , e₂) = splitNames d (suc p) u il
  in false ∷ u₁ , false ∷ u₂ , L.uskip s , e₁ , e₂

-- ------------------------------------------------------------------
-- PRESERVATION.  At `appop` this IS `ilvNames`: the source's splitting
-- becomes the target's disjointness with no arithmetic anywhere.
-- ------------------------------------------------------------------

presCall : SplitPresAtOver namesOver appop
presCall .homSplitO u (u₁ , u₂ , s)       = Names 0 u₁ , Names 0 u₂ , ilvNames s 0 0
presCall .homPartsO u (u₁ , u₂ , s) true  = Eq.refl
presCall .homPartsO u (u₁ , u₂ , s) false = Eq.refl

presCtor : SplitPresAtOver namesOver nilop
presCtor .homSplitO u e   = namesNil 0 0 u e
presCtor .homPartsO u e ()

rustPass : Pass linTheory rustTheory
rustPass .sigOf       = φ
rustPass .mapOf       = namesOver
rustPass .presOf nilop = presCtor
rustPass .presOf appop = presCall

-- ------------------------------------------------------------------
-- ... AND IT REFLECTS.  `ArSection` is invisible here: `onAr appop` is
-- the identity on `Bool` and `onAr nilop` is a map out of `⊥`.
-- ------------------------------------------------------------------

reflCall : ReflectsSplitAtOver namesOver appop
reflCall u (l₁ , l₂ , il) =
  let (u₁ , u₂ , s , e₁ , e₂) = splitNames 0 0 u il
  in (u₁ , u₂ , s)
   , boolΠ {M = λ b → boolΠ {M = λ _ → Own} l₁ l₂ b
                      Eq.≡ Names 0 (L.UseParts appop u (u₁ , u₂ , s) b)}
           e₁ e₂

reflCtor : ReflectsSplitAtOver namesOver nilop
reflCtor u h = namesNil← 0 0 u h , λ ()

rustReflective : Reflective rustPass
rustReflective .reflectsAt nilop = reflCtor
rustReflective .reflectsAt appop = reflCall
rustReflective .secOf nilop ()
rustReflective .secOf appop a    = a , Eq.refl

-- ==================================================================
-- §6  THE COMPILER IS A TERM INTO THE PULLBACK OF `UsesG`.
--
-- `Codegen.Obj` was defined before this theory existed, as `⊕ᴰ RExpr
-- Scoped`.  It IS the pullback -- on the nose, no coercion -- which is
-- the sense in which the theory was already there and is only being
-- named.
-- ==================================================================

module RP = AlongOver namesOver

objIsPull : Obj ≡ RP.pullO {s = tt} UsesG
objIsPull = refl

compileG : L.TmG L.⊢ RP.pullO {s = tt} UsesG
compileG = compileTm

-- ------------------------------------------------------------------
-- ... AND IT IS A HOMOMORPHISM AT `appop`.  `push⊗O` transports the
-- source tensor across the pass (its hypothesis is `presCall`), and
-- `pullTermO callR` applies the target's own call rule.  The composite
-- is the compiler on an application -- which is the statement
-- "compiling a call is calling the compilations", proved rather than
-- read off the three clauses of `compileE`.
-- ------------------------------------------------------------------

trApp : (b : Bool)
      → boolΠ {M = λ _ → L.Ctx} L.TmG L.TmG b
        L.⊢ RP.pullSlotO appop b (boolΠ {M = λ _ → RustG} UsesG UsesG b)
trApp = boolΠ {M = λ b → boolΠ {M = λ _ → L.Ctx} L.TmG L.TmG b
                         L.⊢ RP.pullSlotO appop b
                              (boolΠ {M = λ _ → RustG} UsesG UsesG b)}
              compileTm compileTm

appPush : (L.TmG L.⊛ L.TmG)
          L.⊢ RP.pullResO appop (⊗ˢ callOp (boolΠ {M = λ _ → RustG} UsesG UsesG))
appPush = RP.push⊗O appop presCall
            (boolΠ {M = λ _ → L.Ctx} L.TmG L.TmG)
            (boolΠ {M = λ _ → RustG} UsesG UsesG)
            trApp

compileApp : (L.TmG L.⊛ L.TmG) L.⊢ RP.pullO {s = tt} UsesG
compileApp = RP.pullTermO {s = tt}
               {A = ⊗ˢ callOp (boolΠ {M = λ _ → RustG} UsesG UsesG)}
               {B = UsesG} callR
             L.∘g appPush

-- THE SQUARE.  Both sides reduce to the same term, so this is `refl`.
homApp : compileApp ≡ (compileTm L.∘g L.appT)
homApp = refl

-- ------------------------------------------------------------------
-- AND AT THE BINDER, WHICH IS NOT AN OPERATION OF THE SOURCE THEORY.
--
-- `LinLam/Syntax.lamT` is reindexing along `u ↦ true ∷ u`, not a
-- tensor, so there is no `SplitPresAt` to state.  Its target-side
-- counterpart is the statement that compiling under a binder adjoins
-- exactly the binder's name to the resource -- which is `closOp`'s
-- splitting, and is `usesCompile`'s `tlam` clause with the `IlvI`
-- named.
-- ------------------------------------------------------------------

namesLam : (d : ℕ) (u : L.Usage)
         → Names (suc d) (true ∷ u) Eq.≡ (bnd d ∷ Names d u)
namesLam d u = Eq.ap (bnd d ∷_) (Eq.sym (namesShift d 0 u))

closSplitOfLam : (d : ℕ) (u : L.Usage) → rustFib .Split (closOp d) (Names d u)
closSplitOfLam d u = Names (suc d) (true ∷ u)
                   , ileft (ilvI-nilL≡ (namesShift d 0 u))

-- ==================================================================
-- §7  THE MODEL MEETS `Eval._⇓_`.
--
-- `RunsG` is `UsesG` refined by "and it evaluates" -- an owned Rust
-- expression together with its value.  `forgetRuns` is the inclusion.
-- ==================================================================

RunsG : RustG
RunsG l = Σ[ e ∈ RExpr ] (Uses e l × (Σ[ w ∈ RExpr ] (e ⇓ w)))

forgetRuns : RunsG ⊢ UsesG
forgetRuns l (e , h , _) = e , h

-- PROGRESS.  Not an assumption: `Semantics.CBV.evalD` says every
-- closed linear source term evaluates, and `Relational.Square` carries
-- that across the compiler.
progress : (t : L.Tm []) → Σ[ w ∈ RExpr ] (compileRust t ⇓ w)
progress t = Q.squareRust (S.evalD t) .fst , Q.squareRust (S.evalD t) .snd .fst

-- ... AND THE INTERNAL FORM.  `⌈ [] ⌉` is the representable at the
-- empty usage, i.e. closedness as a GRAMMAR rather than as a side
-- condition; `Names 0 [] = []`, so the codomain really is the empty
-- resource.
ClosedTm : L.Ctx
ClosedTm = L.⌈ [] ⌉ L.& L.TmG

runsTm : ClosedTm L.⊢ RP.pullO {s = tt} RunsG
runsTm _ (Eq.refl , t) = compileRust t , compileClosed t , progress t

-- ... and it really does refine the compiler: forgetting the value
-- gives `compileG` back.
runsForget : (t : L.Tm [])
           → forgetRuns [] (runsTm [] (Eq.refl , t)) ≡ compileG [] t
runsForget t = refl

-- ------------------------------------------------------------------
-- `squareDet`, RESTATED AT THE MODEL.  Whatever value the emitted Rust
-- runs to -- at whatever budget, by whatever derivation -- REALISES
-- the source's normal form.  This is the strongest statement in
-- `Compile/Relational/`, phrased about the object §7 produces.
--
-- IT IS NOT A `Pass`-LEVEL STATEMENT, AND THAT IS NOT A DEFECT.  A
-- `Pass` is a fact about the CARRIER -- which resource the compiled
-- object owns, and how that resource decomposes.  Evaluation does not
-- move the carrier at all: `runsTm`'s answer sits at the same `[]` its
-- subject does.  What evaluation moves is the PAYLOAD, and a payload
-- is a grammar, so the statement about it is a `⊢`-term (`forgetRuns`,
-- `runsTm`) plus a relation on expressions (`Rel`).  Trying to make
-- `⇓` a carrier map would be asking the resource to record the value,
-- which is exactly the confusion `Uses`/`Rel` were split to avoid.
-- ------------------------------------------------------------------

runsRealises : (t : L.Tm []) (w : RExpr) → compileRust t ⇓ w
             → R.Rel (nameOf 0) (S.evalV t) w
runsRealises t w d = Q.squareDet (S.evalD t) w d

modelRealises : (t : L.Tm [])
              → R.Rel (nameOf 0) (S.evalV t)
                      (runsTm [] (Eq.refl , t) .snd .snd .fst)
modelRealises t = runsRealises t _ (progress t .snd)

-- ==================================================================
-- §8  THE OBSTRUCTIONS, PROVED.
-- ==================================================================

-- ------------------------------------------------------------------
-- §8a  THE BINDER FORBIDS A TOTAL POINT.
--
-- A `LaxPoint` at `closOp n` must produce the CLOSURE's resource from
-- the BODY's, i.e. delete `bnd n` -- and deletion is undefined when the
-- body does not own it.  The witness is the empty tuple: `parts-split`
-- forces the body's resource to be `[]`, and `IlvI (bnd n ∷ []) l []`
-- has no constructor.
--
-- So `rustFib` is a promodel and NOT a model: `⊗ˢ`, `⊸ˢ` and the whole
-- additive layer are available, `⊗[ o ]` and `Honest` are not.
-- ------------------------------------------------------------------

noIlvNil : {x : Ident} {l₁ l₂ : Own} → IlvI (x ∷ l₁) l₂ [] → ⊥
noIlvNil ()

noPoint : LaxPoint rustFib → ⊥
noPoint P = noIlvNil (subst (IlvI (bnd 0 ∷ []) l) q il)
  where
  m⃗ : (a : RustAr (closOp 0)) → Own
  m⃗ _ = []

  l : Own
  l = P .op (closOp 0) m⃗

  sp : rustFib .Split (closOp 0) l
  sp = P .split (closOp 0) m⃗

  il : IlvI (bnd 0 ∷ []) l (sp .fst)
  il = sp .snd

  q : sp .fst ≡ []
  q i = P .parts-split (closOp 0) m⃗ i tt

-- ------------------------------------------------------------------
-- §8b  ... AND IT MAKES THE RESOURCE GROW, SO THERE IS NO
-- LENGTH-BASED GRADING AND NO STRUCTURAL RECURSION OVER THE TARGET.
-- ------------------------------------------------------------------

-- PRIMITIVE (phase 1)
ilvNilLen : {l l' : Own} → IlvI [] l l' → length l' Eq.≡ length l
ilvNilLen inil        = Eq.refl
ilvNilLen (iright il) = Eq.ap suc (ilvNilLen il)

-- PRIMITIVE (phase 1)
ilvOneLen : {x : Ident} {l l' : Own} → IlvI (x ∷ []) l l'
          → length l' Eq.≡ suc (length l)
ilvOneLen (ileft il)  = Eq.ap suc (ilvNilLen il)
ilvOneLen (iright il) = Eq.ap suc (ilvOneLen il)

-- THE BINDER IS THE ONE OPERATION THAT GROWS THE RESOURCE.
closGrows : (n : ℕ) (l : Own) (sp : rustFib .Split (closOp n) l)
          → length (rustFib .parts (closOp n) l sp tt) Eq.≡ suc (length l)
closGrows n l (l' , il) = ilvOneLen il

noLenGrading : (G : Grading rustFib) → ((l : Own) → G .deg tt l ≡ length l) → ⊥
noLenGrading G h = ¬-<-zero le
  where
  sp : rustFib .Split (closOp 0) []
  sp = (bnd 0 ∷ []) , ileft inil

  le : 1 ≤ 0
  le = subst2 _≤_ (h (bnd 0 ∷ [])) (h []) (G .deg≤ (closOp 0) [] sp tt)

-- ------------------------------------------------------------------
-- §8c  OWNERSHIP IS NOT STABLE UNDER SUBSTITUTION.
--
-- The witness is a closure that OWNS `bnd 0` and REBINDS it:
--
--     shadow = move |x0| (x0)(x0)      owns  bnd 0
--
-- -- linear, because `uClos` removes one of the body's two `bnd 0`s.
-- `substE (bnd 0) v` STOPS at the rebinding (correctly: that binder
-- shadows), so the result is `shadow` again and still owns `bnd 0`,
-- while the statement demands it own nothing.
--
-- The missing hypothesis is NON-SHADOWING, and it is exactly
-- `Relational.Base.rlam`'s premise.  Note the compiler never emits
-- this term -- `compileE` names binders by LEVEL, so no two binders on
-- a path collide -- which is why `Compile/Relational/` can pay for the
-- hypothesis and why "evaluation preserves ownership" is not the
-- theorem that carries the backend.  The one that does is
-- `runsRealises` above.
-- ------------------------------------------------------------------

shadowBody : RExpr
shadowBody = rCall (rVar (bnd 0)) (rVar (bnd 0))

shadow : RExpr
shadow = rClos 0 shadowBody

shadowUses : Uses shadow (bnd 0 ∷ [])
shadowUses = uClos (uCall (uVar (bnd 0)) (uVar (bnd 0)) (ileft (iright inil)))
                   (ileft (iright inil))

noShadowBody : Uses shadowBody (bnd 0 ∷ []) → ⊥
noShadowBody (uCall (uVar _) (uVar _) (ileft ()))
noShadowBody (uCall (uVar _) (uVar _) (iright ()))

noShadowUses : Uses shadow [] → ⊥
noShadowUses (uClos ub (ileft inil)) = noShadowBody ub

-- the substitution lemma `Uses` would need, and its refutation
SubstUses : Type₀
SubstUses = (x : Ident) (v b : RExpr) {l lb : Own}
          → Uses v [] → Uses b lb → IlvI (x ∷ []) l lb → Uses (substE x v b) l

noSubstUses : SubstUses → ⊥
noSubstUses su =
  noShadowUses (su (bnd 0) (rCtor cA) shadow (uCtor cA) shadowUses (ileft inil))

-- ==================================================================
-- §9  OBSERVATION.  `refl` lines only.
-- ==================================================================

-- the pass, at the gap witness of `Codegen`: a DEAD middle position
-- leaves a gap in the resource
_ : namesOver .homO tt (true ∷ false ∷ true ∷ []) ≡ fre 0 ∷ fre 2 ∷ []
_ = refl

-- preservation at `appop` really is the source's splitting, relabelled
_ : presCall .homSplitO (true ∷ true ∷ []) (_ , _ , twoSplit)
  ≡ (fre 0 ∷ [] , fre 1 ∷ [] , ileft (iright inil))
_ = refl

-- ... and reflection inverts it
_ : reflCall (true ∷ true ∷ []) (fre 0 ∷ [] , fre 1 ∷ [] , ileft (iright inil))
      .fst .snd .snd
  ≡ twoSplit
_ = refl

-- the compiler, as a term into the pullback
_ : compileG (true ∷ true ∷ []) twoVar .fst ≡ rCall (rVar (fre 0)) (rVar (fre 1))
_ = refl

-- the binder adjoins exactly its own name
_ : closSplitOfLam 0 (true ∷ []) .fst ≡ bnd 0 ∷ fre 0 ∷ []
_ = refl

-- the three operations the compiler never emits are still axiomatised,
-- and their splittings say the right thing.  A `match` gives BOTH arms
-- the SAME resource -- the additive rule, and the reason a `match` does
-- not duplicate ownership ...
_ : rustFib .parts matchOp (fre 0 ∷ []) ([] , fre 0 ∷ [] , iright inil)
  ≡ armΠ [] (fre 0 ∷ []) (fre 0 ∷ [])
_ = refl

-- ... a `let` adjoins the binder's name to the BODY and not to the
-- bound expression ...
_ : rustFib .parts (letOp 3) [] ([] , [] , bnd 3 ∷ [] , ileft inil , inil)
  ≡ boolΠ [] (bnd 3 ∷ [])
_ = refl

-- ... a constant owns nothing, and a variable owns exactly itself
_ : ctorR cA [] (tt , λ ()) .fst ≡ rCtor cA
_ = refl

_ : varR (fre 0) (fre 0 ∷ []) ((tt , tt) , λ ()) .fst ≡ rVar (fre 0)
_ = refl

-- THE MODEL RUNS.  `(λx.x)(λx.x)` compiles to something that owns
-- nothing and evaluates to the identity closure.
_ : runsTm [] (Eq.refl , L.selfApp) .snd .snd .fst ≡ rClos 0 (rVar (bnd 0))
_ = refl

_ : runsTm [] (Eq.refl , L.idLin) .fst ≡ rClos 0 (rVar (bnd 0))
_ = refl
