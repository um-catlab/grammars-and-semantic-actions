{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  α-EQUIVALENCE ON `RExpr`, BY ERASING BINDER NAMES TO DE BRUIJN.

  ------------------------------------------------------------------
  WHY THIS EXISTS
  ------------------------------------------------------------------

  `Syntax.agda` names binders by their LEVEL, and `Codegen.compileE`
  chooses that level to be the ABSOLUTE DEPTH at which the binder was
  emitted.  Substitution does not renumber, so a value that came out
  from under a binder carries levels one deeper than the compilation of
  the source value does.  That is not a defect of the backend, it is
  what `Compile/Relational/Refutation.agda` PROVES about the on-the-nose
  square:

      Simulates = (t v : Tm []) → t ⇓ₛ v → compileRust t ⇓ compileRust v

  is FALSE, refuted by `noNoseSquare` at `(λf.λx. f x)(λy.y)`, and the
  ONLY thing wrong with it is the `≡`.  The repair, already proved, is
  `Compile/Relational/Square.agda`:

      squareDet : t ⇓ₛ v → (w : RExpr) → compileRust t ⇓ w
                → Rel (nameOf 0) v w

  -- the target's answer `w` REALISES the source's value `v` relative to
  the initial naming, and `Relational/Base.agda`'s `rlam` takes the
  binder's level as an ARBITRARY natural.  So the equivalence the theory
  actually licenses between `w` and `compileRust v` is "the same term up
  to a renaming of binders", and that is what this file decides.

  ------------------------------------------------------------------
  THE PRIOR ART, AND WHY THIS ONE NEEDS ONE MORE CONSTRUCTOR
  ------------------------------------------------------------------

  `Instances/LinLam/Check.agda`'s `Skel` is the same move one level up
  the pipeline -- `skel : DBTm n → Skel` erases a parse tree to
  `svar`/`sapp`/`slam` with de Bruijn indices, and `Chain/PrintTests`'s
  `alphaInvisible` is exactly the statement that α is invisible after
  it.  `ASkel` below is that construction transported to `RExpr`.

  It has one constructor `Skel` does not: `aDang`.  `DBTm n` is
  INTRINSICALLY SCOPED, so `skel` never meets an occurrence with no
  binder; `RExpr` is a raw syntax and does.  Mapping a dangling `bnd m`
  to anything already in use would be a BUG IN THE HARNESS, not a
  convenience: `Compare`'s `bugE` mutation shifts every binder level by
  one, which turns `rClos 0 (rVar (bnd 0))` into
  `rClos 1 (rVar (bnd 0))` -- an expression whose occurrence is
  DANGLING.  If `aDang m` collapsed into `aBnd`, or into `aFre m`, that
  mutation would normalise back to the correct answer and `--broken`
  would stop reporting it.  Dangling names are therefore kept VERBATIM
  and in their own constructor, so they can never be α-identified with
  a bound occurrence or with a free variable of the initial context.

  Free names (`fre n`) are likewise preserved verbatim: they are the
  variables of the initial context, they are not bound by anything in
  the expression, and renaming them would not be α.

  ------------------------------------------------------------------
  SHADOWING
  ------------------------------------------------------------------

  `Eval.substE` resolves a variable BY NAME, so an inner binder at the
  same level SHADOWS an outer one, and evaluated expressions really do
  repeat levels on a path -- `Relational/Base.agda` measures this at
  `appLin appLin`, whose value is

      rClos 1 (rCall (rClos 0 (rClos 1 …)) (rVar (bnd 1)))

  So the scope stack is searched INNERMOST-FIRST (`idxOf` returns the
  FIRST hit), which is precisely `substE`'s discipline, and the index it
  returns is the number of binders crossed.

  ------------------------------------------------------------------
  PHASE
  ------------------------------------------------------------------

  Phase 1 throughout, and marked: this is an erasure being DEFINED, it
  matches on `RExpr` and on `Ident`, and it is used only by the test
  harness.  Nothing here is imported by any `⊢`-term.
-}
open import Cubical.Foundations.Prelude

module Compile.LinToRust.Alpha where

open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Bool using (Bool; true; false; _and_)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Maybe using (Maybe; just; nothing)

open import Compile.LinToRust.Syntax
  using ( RExpr; rVar; rClos; rCall; rCtor; rMatch; rLet
        ; Ident; bnd; fre; Ctor; cA; cB; eqℕ )

-- ==================================================================
-- §1  THE NAMELESS SKELETON.
--
-- `aClos` and `aLet` carry NO level: that is the whole point.  The
-- three leaf constructors are kept apart on purpose (see the header).
-- ==================================================================

data ASkel : Type₀ where
  aBnd   : ℕ → ASkel                        -- bound, by DE BRUIJN INDEX
  aDang  : ℕ → ASkel                        -- out of scope: level kept
  aFre   : ℕ → ASkel                        -- free variable: kept
  aClos  : ASkel → ASkel                    -- `move |_| e`, name erased
  aCall  : ASkel → ASkel → ASkel
  aCtor  : Ctor → ASkel
  aMatch : ASkel → ASkel → ASkel → ASkel
  aLet   : ASkel → ASkel → ASkel            -- binder name erased

-- ==================================================================
-- §2  THE SCOPE STACK.
--
-- `List ℕ`, innermost binder FIRST.  `idxOf` is the first hit, so an
-- inner binder shadows an outer one carrying the same level -- which is
-- what `Eval.substE` does when it resolves a name.
-- ==================================================================

-- PRIMITIVE (phase 1)
bumpM : Maybe ℕ → Maybe ℕ
bumpM nothing  = nothing
bumpM (just n) = just (suc n)

-- PRIMITIVE (phase 1): `hit b r` -- stop here if the levels matched,
-- else keep the deeper answer and count one binder crossed.
hit : Bool → Maybe ℕ → Maybe ℕ
hit true  _ = just zero
hit false r = bumpM r

-- PRIMITIVE (phase 1)
idxOf : List ℕ → ℕ → Maybe ℕ
idxOf []       _ = nothing
idxOf (l ∷ ls) m = hit (eqℕ l m) (idxOf ls m)

-- PRIMITIVE (phase 1): a bound occurrence becomes its index; an
-- occurrence with no binder keeps its level, in its OWN constructor.
occ : Maybe ℕ → ℕ → ASkel
occ (just i) _ = aBnd i
occ nothing  m = aDang m

-- ==================================================================
-- §3  THE ERASURE.
--
-- `rLet n e b` binds `n` in `b` ONLY: the bound expression `e` is
-- elaborated in the enclosing scope.
-- ==================================================================

-- PRIMITIVE (phase 1)
alphaE : List ℕ → RExpr → ASkel
alphaE env (rVar (bnd m))   = occ (idxOf env m) m
alphaE env (rVar (fre n))   = aFre n
alphaE env (rClos n b)      = aClos (alphaE (n ∷ env) b)
alphaE env (rCall f a)      = aCall (alphaE env f) (alphaE env a)
alphaE env (rCtor c)        = aCtor c
alphaE env (rMatch s a b)   = aMatch (alphaE env s) (alphaE env a) (alphaE env b)
alphaE env (rLet n e b)     = aLet (alphaE env e) (alphaE (n ∷ env) b)

-- THE α-NORMAL FORM of a whole expression: nothing is in scope yet.
alpha : RExpr → ASkel
alpha = alphaE []

-- ==================================================================
-- §4  ... AND ITS DECIDED EQUALITY, AS A `Bool`.
--
-- A `Bool`, not a `Discrete`, because what consumes it is a table
-- column.  `eqAlpha e f` is "e and f are the same expression up to a
-- renaming of BOUND levels"; free and dangling names are compared on
-- the nose.
-- ==================================================================

eqCtorA : Ctor → Ctor → Bool
eqCtorA cA cA = true
eqCtorA cB cB = true
eqCtorA _  _  = false

eqA : ASkel → ASkel → Bool
eqA (aBnd m)      (aBnd n)      = eqℕ m n
eqA (aDang m)     (aDang n)     = eqℕ m n
eqA (aFre m)      (aFre n)      = eqℕ m n
eqA (aClos a)     (aClos b)     = eqA a b
eqA (aCall f a)   (aCall g b)   = eqA f g and eqA a b
eqA (aCtor c)     (aCtor d)     = eqCtorA c d
eqA (aMatch s a b) (aMatch t c d) = eqA s t and (eqA a c and eqA b d)
eqA (aLet e a)    (aLet f b)    = eqA e f and eqA a b
eqA _             _             = false

-- α-equivalence of two `RExpr`s.
eqAlpha : RExpr → RExpr → Bool
eqAlpha e f = eqA (alpha e) (alpha f)

-- ... lifted to the evaluator's `Maybe`.  `nothing` is out of fuel or
-- stuck, and is α-equivalent to nothing but itself.
eqAlphaM : Maybe RExpr → Maybe RExpr → Bool
eqAlphaM nothing  nothing  = true
eqAlphaM nothing  (just _) = false
eqAlphaM (just _) nothing  = false
eqAlphaM (just e) (just f) = eqAlpha e f

-- ==================================================================
-- §5  IT COMPUTES, AND IT IS NOT TOO COARSE.
--
-- The first block is the fact the harness needs; the second is the
-- fact that makes the harness still able to FAIL.
-- ==================================================================

-- the two shapes `Refutation` is about: `bigT`'s answer and the
-- compilation of `bigT`'s value, which differ only in binder levels
_ : alpha (rClos 1 (rCall (rClos 0 (rVar (bnd 0))) (rVar (bnd 1))))
  ≡ aClos (aCall (aClos (aBnd 0)) (aBnd 0))
_ = refl

_ : alpha (rClos 0 (rCall (rClos 1 (rVar (bnd 1))) (rVar (bnd 0))))
  ≡ aClos (aCall (aClos (aBnd 0)) (aBnd 0))
_ = refl

_ : eqAlpha (rClos 1 (rCall (rClos 0 (rVar (bnd 0))) (rVar (bnd 1))))
            (rClos 0 (rCall (rClos 1 (rVar (bnd 1))) (rVar (bnd 0))))
  ≡ true
_ = refl

-- `applyK`'s row: `move |x1| x1` versus `move |x0| x0`
_ : eqAlpha (rClos 1 (rVar (bnd 1))) (rClos 0 (rVar (bnd 0))) ≡ true
_ = refl

-- SHADOWING is respected: the inner binder wins, so these are NOT α
_ : eqAlpha (rClos 0 (rClos 0 (rVar (bnd 0))))     -- inner
            (rClos 0 (rClos 1 (rVar (bnd 0))))     -- outer
  ≡ false
_ = refl

-- A DANGLING occurrence is not a bound one.  This is exactly the shape
-- `Compare.bugE` produces from `rClos 0 (rVar (bnd 0))`, and it is the
-- reason `--broken` still reports.
_ : alpha (rClos 1 (rVar (bnd 0))) ≡ aClos (aDang 0)
_ = refl

_ : eqAlpha (rClos 1 (rVar (bnd 0))) (rClos 0 (rVar (bnd 0))) ≡ false
_ = refl

-- ... nor is it a free variable of the initial context
_ : eqAlpha (rClos 1 (rVar (bnd 0))) (rClos 1 (rVar (fre 0))) ≡ false
_ = refl

-- free names are NEVER renamed
_ : eqAlpha (rVar (fre 0)) (rVar (fre 1)) ≡ false
_ = refl

_ : alpha (rClos 3 (rVar (fre 3))) ≡ aClos (aFre 3)
_ = refl

-- `rLet` binds in its BODY only, not in the bound expression
_ : alpha (rLet 0 (rVar (bnd 0)) (rVar (bnd 0)))
  ≡ aLet (aDang 0) (aBnd 0)
_ = refl

-- and the structure is still compared: α is not a licence to agree
_ : eqAlpha (rClos 0 (rVar (bnd 0))) (rClos 0 (rCtor cA)) ≡ false
_ = refl

_ : eqAlpha (rCtor cA) (rCtor cB) ≡ false
_ = refl

_ : eqAlpha (rCall (rCtor cA) (rCtor cB)) (rCall (rCtor cB) (rCtor cA)) ≡ false
_ = refl
