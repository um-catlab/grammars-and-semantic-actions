{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  A DIFFERENTIAL TEST HARNESS FOR THE BACKENDS.

  This is TESTING, not proof.  The proofs live in
  `Compile/ClosureConv/Correct.agda`, `Compile/ClosureConv/ARMCorrect.agda`
  and `Compile/LinToRust/Theory.agda`.  What this file does is run three
  observables on the SAME closed linear λ-term and render the answers
  into one `String`, so that a script can print a table.

  The three observables:

    REF   `runP fuel (compileP t)`   -- the IR abstract machine.  At
                                        fuel 64 this is exactly
                                        `Correct.obs`.
    ARM   `answerT fuel depth t`     -- real AArch64 control flow,
                                        `Control.run`, decoded.
    RUST  `valOf (evalRust k (compileRust t))` -- the Rust fragment's
                                        big-step evaluator.

  THE WRINKLE, STATED HONESTLY.  REF and ARM both answer in `Maybe Val`
  -- a closure is a code index plus a captured environment -- so they
  are compared DIRECTLY.  RUST answers in `Maybe RExpr`: its values are
  substituted-into λ-abstractions, with no code table and no
  environment, so there is no cheap decoder between the two.  RUST is
  therefore compared against the SOURCE-LEVEL reference instead:

    valOf (evalRust k (compileRust t))  ==  just (compileRust (evalV t))

  where `evalV` is `Compile.Semantics.CBV`'s call-by-value evaluator.

  ... AND THE `==` IS NOT `≡`.  That display is the
  `Simulation.Simulates` square of `LinToRust/Codegen.agda`, and
  `Compile/Relational/Refutation.agda` PROVES that square false
  (`noNoseSquare`, at `(λf.λx. f x)(λy.y)`): `compileE` names binders by
  ABSOLUTE DEPTH, substitution moves the residual body one binder
  shallower, and the two sides come out α-equivalent but not equal.
  Comparing with `≡` therefore reproduces a KNOWN-FALSE statement, and
  four of the twelve default rows were reporting exactly that.

  The theorem that survives is `Compile/Relational/Square.agda`'s

      squareDet : t ⇓ₛ v → (w : RExpr) → compileRust t ⇓ w
                → Rel (nameOf 0) v w

  whose `Rel` (`Relational/Base.agda`) lets `rlam` pick the binder's
  level FREELY.  So α-equivalence -- `Compile.LinToRust.Alpha.eqAlpha`,
  a de Bruijn erasure in the style of `Instances/LinLam/Check.skel` --
  is the comparison the theory licenses, and it is what the RUST column
  uses by default.  `syn = true` restores the on-the-nose test, and the
  default verdict still SAYS `ALPHA` rather than `AGREE` when the two
  differ, so nothing is hidden either way.

  This does not blunt `--broken`: §3's `bugE` shifts BINDERS and leaves
  OCCURRENCES alone, so it produces DANGLING names, and `Alpha.aDang`
  keeps those in a constructor of their own.  §6 pins that.

  So: ARM is compared to REF directly; RUST is compared up to α to the
  source reference.  Both comparisons pass through the source
  semantics, which is the common vertex.

  PHASE.  Phase 1 throughout, and marked: rendering and structural
  equality match on `Val` and on `RExpr`, because a test harness is a
  thing that LOOKS at values.  Nothing here is imported by any
  `⊢`-term.
-}
open import Cubical.Foundations.Prelude

module Compile.Suite.Compare where

open import Agda.Builtin.String using (String; primStringAppend; primShowNat)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Bool using (Bool; true; false; _and_)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Data.Unit using (Unit; tt)

open import Compile.ClosureConv.Convert
  using ( Tm; tvar; tapp; tlam
        ; unil; uleft; uright
        ; idLin; selfApp; appLin; bigT; applyK; Kterm
        ; Val; clos; runP; compileP )

import Compile.ClosureConv.ARM     as ARM
import Compile.LinToRust.Codegen   as RC
import Compile.Semantics.CBV       as CBV

open import Compile.LinToRust.Syntax
  using ( RExpr; rVar; rClos; rCall; rCtor; rMatch; rLet
        ; Ident; bnd; fre; Ctor; cA; cB; renderExpr )
open import Compile.LinToRust.Eval using (evalRust; valOf)
open import Compile.LinToRust.Alpha using (eqAlpha; eqAlphaM; alpha; aClos; aBnd; aDang)

-- ==================================================================
-- §0  STRING PLUMBING.
-- ==================================================================

infixr 5 _<>_
_<>_ : String → String → String
_<>_ = primStringAppend

showℕ : ℕ → String
showℕ = primShowNat

-- ==================================================================
-- §1  STRUCTURAL EQUALITY, AS A `Bool`.
--
-- Not `Discrete`: the harness wants an answer it can print, and a
-- `Bool` is what a table column is.
-- ==================================================================

eqN : ℕ → ℕ → Bool
eqN zero    zero    = true
eqN zero    (suc _) = false
eqN (suc _) zero    = false
eqN (suc m) (suc n) = eqN m n

eqVal  : Val → Val → Bool
eqVals : List Val → List Val → Bool

eqVal (clos m xs) (clos n ys) = eqN m n and eqVals xs ys

eqVals []       []       = true
eqVals []       (_ ∷ _)  = false
eqVals (_ ∷ _)  []       = false
eqVals (x ∷ xs) (y ∷ ys) = eqVal x y and eqVals xs ys

eqMVal : Maybe Val → Maybe Val → Bool
eqMVal nothing  nothing  = true
eqMVal nothing  (just _) = false
eqMVal (just _) nothing  = false
eqMVal (just x) (just y) = eqVal x y

eqCtor : Ctor → Ctor → Bool
eqCtor cA cA = true
eqCtor cB cB = true
eqCtor _  _  = false

eqId : Ident → Ident → Bool
eqId (bnd m) (bnd n) = eqN m n
eqId (fre m) (fre n) = eqN m n
eqId _       _       = false

eqE : RExpr → RExpr → Bool
eqE (rVar x)        (rVar y)        = eqId x y
eqE (rClos m a)     (rClos n b)     = eqN m n and eqE a b
eqE (rCall f a)     (rCall g b)     = eqE f g and eqE a b
eqE (rCtor c)       (rCtor d)       = eqCtor c d
eqE (rMatch s a b)  (rMatch t c d)  = eqE s t and (eqE a c and eqE b d)
eqE (rLet m e a)    (rLet n f b)    = eqN m n and (eqE e f and eqE a b)
eqE _               _               = false

eqME : Maybe RExpr → Maybe RExpr → Bool
eqME nothing  nothing  = true
eqME nothing  (just _) = false
eqME (just _) nothing  = false
eqME (just x) (just y) = eqE x y

-- ==================================================================
-- §2  RENDERING.
-- ==================================================================

showVal  : Val → String
showVals : List Val → String

showVal (clos n [])       = "c" <> showℕ n
showVal (clos n (v ∷ vs)) = "c" <> showℕ n <> "[" <> showVals (v ∷ vs) <> "]"

showVals []       = ""
showVals (v ∷ []) = showVal v
showVals (v ∷ vs) = showVal v <> "," <> showVals vs

showMVal : Maybe Val → String
showMVal nothing  = "<none>"
showMVal (just v) = showVal v

showME : Maybe RExpr → String
showME nothing  = "<none>"
showME (just e) = renderExpr e

verdict : Bool → String
verdict true  = "AGREE"
verdict false = "DIFFER"

-- ------------------------------------------------------------------
-- THE `RUST/SRC` VERDICT, AND WHY IT IS NOT `verdict`.
--
-- On-the-nose equality is the WRONG comparison here, and that is a
-- theorem, not an opinion.  `Compile/Relational/Refutation.agda` proves
-- `Simulates` -- `t ⇓ₛ v → compileRust t ⇓ compileRust v` -- FALSE, at
-- `(λf.λx. f x)(λy.y)`; the only thing wrong with it is the `≡`, since
-- `compileE` names binders by ABSOLUTE DEPTH and substitution moves the
-- residual body one binder shallower.  What IS true is
-- `Compile/Relational/Square.agda`'s
--
--     squareDet : t ⇓ₛ v → (w : RExpr) → compileRust t ⇓ w
--               → Rel (nameOf 0) v w
--
-- and `Relational/Base.agda`'s `rlam` takes the binder's level as an
-- ARBITRARY natural.  So `w` and `compileRust v` are licensed to differ
-- by a renaming of binders and by nothing else -- which is exactly
-- `Alpha.eqAlpha`.
--
-- The raw difference stays VISIBLE rather than being swallowed:
--
--     AGREE    syntactically equal
--     ALPHA    equal up to a renaming of BOUND levels, not on the nose
--              -- the `squareDet` residue, and not a defect
--     DIFFER   not even α-equivalent -- a genuine divergence
--
-- and `syn = true` (`--syntactic`) collapses `ALPHA` back into
-- `DIFFER`, recovering the old column verbatim.
-- ------------------------------------------------------------------
rustVerdict : Bool → Bool → Bool → String
rustVerdict true  s     _     = verdict s          -- --syntactic
rustVerdict false true  _     = "AGREE"
rustVerdict false false true  = "ALPHA"
rustVerdict false false false = "DIFFER"

-- ==================================================================
-- §3  THE DELIBERATE BUGS.
--
-- `--broken` swaps these in.  A harness that has never reported a
-- failure has not been tested, so the mutations are here, in the
-- harness, and labelled.
--
-- `bugE` is a real codegen mutation: every binder level is shifted by
-- one, so a compiled term's binders no longer match its variables and
-- `evalRust` gets stuck (or, worse, answers something wrong).
--
-- `bugVal` is a real decode mutation: the block index the ARM answer
-- names is off by one.
-- ==================================================================

bugE : RExpr → RExpr
bugE (rVar x)       = rVar x
bugE (rClos n b)    = rClos (suc n) (bugE b)
bugE (rCall f a)    = rCall (bugE f) (bugE a)
bugE (rCtor c)      = rCtor c
bugE (rMatch s a b) = rMatch (bugE s) (bugE a) (bugE b)
bugE (rLet n e b)   = rLet n (bugE e) (bugE b)

bugVal : Val → Val
bugVal (clos n vs) = clos (suc n) vs

bugMVal : Maybe Val → Maybe Val
bugMVal nothing  = nothing
bugMVal (just v) = just (bugVal v)

-- ==================================================================
-- §4  THE THREE OBSERVABLES.
-- ==================================================================

-- the IR abstract machine.  `refObs 64 ≡ Correct.obs`, definitionally.
refObs : ℕ → Tm [] → Maybe Val
refObs fuel t = runP fuel (compileP t)

-- real AArch64: `armObs fuel depth ≡ ARM.answerT fuel depth`.
armObs : ℕ → ℕ → Bool → Tm [] → Maybe Val
armObs fuel depth false t = ARM.answerT fuel depth t
armObs fuel depth true  t = bugMVal (ARM.answerT fuel depth t)

-- the compiled Rust expression, possibly mutated
rustCode : Bool → Tm [] → RExpr
rustCode false t = RC.compileRust t
rustCode true  t = bugE (RC.compileRust t)

-- the Rust evaluator's answer
rustObs : ℕ → Bool → Tm [] → Maybe RExpr
rustObs k bad t = valOf (evalRust k (rustCode bad t))

-- what the SOURCE says the Rust answer should be: compile the
-- call-by-value value of `t`.  NEVER mutated -- a reference that
-- carries the same bug as the thing it judges is not a reference, and
-- `--broken` would then be invisible on exactly the terms whose bug
-- cancels.
rustExpected : Tm [] → RExpr
rustExpected t = RC.compileRust (CBV.evalV t)

-- ==================================================================
-- §5  THE ROW.
--
-- Fields are separated by `;` and rows by a newline; the shell script
-- splits on exactly that.  NOT `|`: `renderExpr` emits Rust closures
-- as `move |xn| e`, so a `|` separator would be ambiguous.  No column
-- ever contains a `;` -- neither `showVal` nor `renderExpr` emits one.
--
-- The columns, in order:
--
--   name ; source ; REF ; ARM ; ARM-vs-REF ; RUST ; RUST-expected ;
--   RUST-vs-source
-- ==================================================================

row : ℕ → ℕ → ℕ → ℕ → Bool → Bool → Bool → String → Tm [] → String
row armFuel armDepth refFuel rustFuel badARM badRust syn nm t =
  let r   = refObs refFuel t
      a   = armObs armFuel armDepth badARM t
      ru  = rustObs rustFuel badRust t
      ex  = rustExpected t
  in nm
     <> ";" <> renderExpr (RC.compileRust t)
     <> ";" <> showMVal r
     <> ";" <> showMVal a
     <> ";" <> verdict (eqMVal a r)
     <> ";" <> showME ru
     <> ";" <> renderExpr ex
     <> ";" <> rustVerdict syn (eqME ru (just ex)) (eqAlphaM ru (just ex))

rows : ℕ → ℕ → ℕ → ℕ → Bool → Bool → Bool
     → List (String × Tm []) → String
rows _  _  _  _  _  _  _  []             = ""
rows af ad rf uf ba br sy ((nm , t) ∷ ts) =
  row af ad rf uf ba br sy nm t <> "\n" <> rows af ad rf uf ba br sy ts

-- THE REPORT.  One `String`; a script pins it against a sentinel and
-- reads the normal form Agda prints back.  The seventh argument is
-- `--syntactic`: `false` (the default) compares the Rust column up to
-- α, `true` compares it on the nose.
report : ℕ → ℕ → ℕ → ℕ → Bool → Bool → Bool → List (String × Tm []) → String
report = rows

-- ==================================================================
-- §6  IT COMPUTES.
--
-- The point of the whole file: these are `refl`, so every observable
-- above really reduces at typecheck time and the script never needs a
-- runtime.
-- ==================================================================

_ : refObs 64 idLin ≡ just (clos 0 [])
_ = refl

_ : armObs 500 8 false idLin ≡ just (clos 0 [])
_ = refl

_ : armObs 500 8 true idLin ≡ just (clos 1 [])
_ = refl

_ : rustObs 20 false idLin ≡ just (rClos 0 (rVar (bnd 0)))
_ = refl

_ : rustObs 20 false selfApp ≡ just (rClos 0 (rVar (bnd 0)))
_ = refl

-- the mutated backend really is stuck: shifting the binder level
-- breaks the substitution, so `(λx.x)(λx.x)` no longer reduces to a
-- value.
_ : rustObs 20 true selfApp ≡ nothing
_ = refl

_ : showVal (clos 1 (clos 2 [] ∷ [])) ≡ "c1[c2]"
_ = refl

_ : row 500 8 64 20 false false false "idLin" idLin
  ≡ "idLin;move |x0| x0;c0;c0;AGREE;move |x0| x0;move |x0| x0;AGREE"
_ = refl

-- ------------------------------------------------------------------
-- THE α COLUMN, PINNED BOTH WAYS.
--
-- `bigT` is the term the README used to point at: the Rust answer and
-- the compilation of the source value differ, and differ ONLY in binder
-- levels.  Syntactically that is a `DIFFER`; up to α it is not.
-- ------------------------------------------------------------------

_ : rustObs 40 false bigT
  ≡ just (rClos 1 (rCall (rClos 0 (rVar (bnd 0))) (rVar (bnd 1))))
_ = refl

_ : rustExpected bigT ≡ rClos 0 (rCall (rClos 1 (rVar (bnd 1))) (rVar (bnd 0)))
_ = refl

_ : eqME    (rustObs 40 false bigT) (just (rustExpected bigT)) ≡ false
_ = refl

_ : eqAlphaM (rustObs 40 false bigT) (just (rustExpected bigT)) ≡ true
_ = refl

-- so the default column says `ALPHA` and `--syntactic` says `DIFFER`
_ : row 500 8 64 40 false false false "bigT" bigT
  ≡ "bigT;(move |x0| move |x1| (x0)(x1))(move |x0| x0);c1[c2];c1[c2];AGREE;move |x1| (move |x0| x0)(x1);move |x0| (move |x1| x1)(x0);ALPHA"
_ = refl

_ : row 500 8 64 40 false false true "bigT" bigT
  ≡ "bigT;(move |x0| move |x1| (x0)(x1))(move |x0| x0);c1[c2];c1[c2];AGREE;move |x1| (move |x0| x0)(x1);move |x0| (move |x1| x1)(x0);DIFFER"
_ = refl

-- ------------------------------------------------------------------
-- ... AND THE CRITICAL ONE: α-INSENSITIVITY DOES NOT BLUNT `--broken`.
--
-- Relaxing a comparison risks MASKING the mutation it is supposed to
-- catch, and `bugE` is precisely a mutation of binder LEVELS, so this
-- is the one that has to be checked rather than assumed.  It does not
-- mask it, because `bugE` shifts the BINDER and leaves the OCCURRENCE
-- alone: `rClos 0 (rVar (bnd 0))` becomes `rClos 1 (rVar (bnd 0))`,
-- whose occurrence is DANGLING, and `Alpha.aDang` is a constructor of
-- its own.  A renaming of binders cannot make a bound occurrence out of
-- an unbound one.
-- ------------------------------------------------------------------

_ : rustObs 20 true idLin ≡ just (rClos 1 (rVar (bnd 0)))
_ = refl

_ : alpha (rClos 1 (rVar (bnd 0))) ≡ aClos (aDang 0)
_ = refl

_ : alpha (rClos 0 (rVar (bnd 0))) ≡ aClos (aBnd 0)
_ = refl

_ : eqAlphaM (rustObs 20 true idLin) (just (rustExpected idLin)) ≡ false
_ = refl

-- the verdict `row` computes, on the mutated backend, in the DEFAULT
-- (α-insensitive) mode
_ : rustVerdict false
      (eqME     (rustObs 20 true idLin) (just (rustExpected idLin)))
      (eqAlphaM (rustObs 20 true idLin) (just (rustExpected idLin)))
  ≡ "DIFFER"
_ = refl

_ : row 500 8 64 20 false true false "idLin" idLin
  ≡ "idLin;move |x0| x0;c0;c0;AGREE;move |x1| x0;move |x0| x0;DIFFER"
_ = refl

-- `--broken=arm` is untouched: the ARM column never goes near α.
_ : row 500 8 64 20 true false false "idLin" idLin
  ≡ "idLin;move |x0| x0;c0;c1;DIFFER;move |x0| x0;move |x0| x0;AGREE"
_ = refl
