{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE DRIVER THE SHELL RUNNERS TALK TO.

  ------------------------------------------------------------------
  WHAT THIS IS FOR
  ------------------------------------------------------------------

  Everything in this development computes at TYPECHECK time, so the way
  a shell script gets a string out of it is `tools/compare.sh`'s: pin
  the string against a sentinel, run `agda`, and read the normal form
  back out of the `UnequalTerms` error.  That mechanism needs a single
  `String`-valued function of a single `String` argument, because the
  argument is what the script interpolates.

  This file is that interface and nothing more.  Every observable it
  exports already existed; what is new is the NAME on the left.

  ------------------------------------------------------------------
  ONE LANGUAGE, `Compile.LinNum.Syntax.NTm`
  ------------------------------------------------------------------

  The table is over `NTm`, the linear λ-calculus WITH NUMBERS, and the
  six pure λ-terms of `Compile.Suite.Terms.corpus` are embedded into it
  by `fromTm`.  That is sound as a presentation because
  `Compile/LinNum/Emit.agda` §3.3 pins

      asmN (fromTm idLin) ≡ ClosureConv.Emit.asmId

  -- the arithmetic backend emits the OLD backend's text, character for
  character, on a term with no arithmetic in it.  So one table can serve
  both without the runner having to know which stack it is in.

  ------------------------------------------------------------------
  THE OBSERVABLE IS A WORD, FOR BOTH KINDS OF VALUE
  ------------------------------------------------------------------

  `Compile/ClosureConv/Emit.agda` §B had to argue that the exit status
  -- field 0 of the answer record -- was the best eight-bit channel
  available, and then restate the four numbers 6/29/33/45 by hand.
  Here `Emit.refWord` computes that word on the MODEL side too

      a number's word is the number
      a closure's word is its block's code address

  so REF and ARM are compared as `Maybe ℕ`, uniformly, and the exit
  status is that word masked.  For an arithmetic answer the channel
  forgets nothing at all.

  PHASE.  Phase 1, and marked: string rendering recurses on a target
  value and the name table is a metalanguage list.  This is a HARNESS
  in the sense of `Compile/Suite/Compare.agda`'s header -- nothing here
  is compiled and nothing here is proved.
-}
open import Cubical.Foundations.Prelude

module Compile.Suite.Run where

open import Agda.Builtin.String
  using (String; primStringAppend; primShowNat; primStringEquality)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Bool using (Bool; true; false; if_then_else_)
open import Cubical.Data.List using (List; []; _∷_; _++_; map)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)

open import Compile.LinNum.Emit
  using (asmN; unitLen; refWord; wordOfVal)
open import Compile.LinNum.ARM
  using ( NTm; fromTm; Val; clos; num; obsN; numN; compileP; armWord
        ; lit41; sum42; inc; incApp; addFn; addApp; applyInc; sum143 )
import Compile.LinNum.Rust as NR

-- the OLD stack, for the two observables that only exist there
import Compile.ClosureConv.ARM      as AM
import Compile.ClosureConv.Correct  as CR
import Compile.LinToRust.Codegen    as RC
import Compile.LinToRust.Run        as RR
import Compile.Suite.Terms          as T
import TheoryGrammar.Instances.LinLam.Syntax as L
open import Compile.ClosureConv.IR using () renaming (Val to Val₀; clos to clos₀)

private
  infixr 5 _<>_
  _<>_ : String → String → String
  _<>_ = primStringAppend

showℕ : ℕ → String
showℕ = primShowNat

showMℕ : Maybe ℕ → String
showMℕ nothing  = "TIMEOUT"
showMℕ (just n) = showℕ n

-- ==================================================================
-- §1  RENDERING A VALUE.  `Compile/Suite/Compare.agda` has the same
-- function at the old `Val`; it is repeated rather than imported so
-- that this file and that one can be edited independently.
-- ==================================================================

showVal  : Val → String
showVals : List Val → String

showVal (num n)           = "num " <> showℕ n
showVal (clos n [])       = "clos " <> showℕ n
showVal (clos n (v ∷ vs)) = "clos " <> showℕ n <> "[" <> showVals (v ∷ vs) <> "]"

showVals []       = ""
showVals (v ∷ []) = showVal v
showVals (v ∷ vs) = showVal v <> "," <> showVals vs

showMVal : Maybe Val → String
showMVal nothing  = "TIMEOUT"
showMVal (just v) = showVal v

-- ... and the OLD `IR.Val`, whose only shape is a closure
showVal₀  : Val₀ → String
showVals₀ : List Val₀ → String

showVal₀ (clos₀ n [])       = "clos " <> showℕ n
showVal₀ (clos₀ n (v ∷ vs)) = "clos " <> showℕ n <> "[" <> showVals₀ (v ∷ vs) <> "]"

showVals₀ []       = ""
showVals₀ (v ∷ []) = showVal₀ v
showVals₀ (v ∷ vs) = showVal₀ v <> "," <> showVals₀ vs

showMVal₀ : Maybe Val₀ → String
showMVal₀ nothing  = "TIMEOUT"
showMVal₀ (just v) = showVal₀ v

-- ==================================================================
-- §2  THE NAME TABLE.
--
-- The arithmetic terms, then `Compile.Suite.Terms.corpus` embedded by
-- `fromTm`.  A name is looked up by `primStringEquality`; an unknown
-- one is a VALUE (`?`), not an error, so the harness never has to
-- distinguish "agda failed" from "you typed the name wrong".
-- ==================================================================

numTable : List (String × NTm [])
numTable =
    ("lit41"    , lit41)
  ∷ ("sum42"    , sum42)
  ∷ ("inc"      , inc)
  ∷ ("incApp"   , incApp)
  ∷ ("addFn"    , addFn)
  ∷ ("addApp"   , addApp)
  ∷ ("applyInc" , applyInc)
  ∷ ("sum143"   , sum143)
  ∷ []

lamTable : List (String × NTm [])
lamTable = map (λ p → p .fst , fromTm (p .snd)) T.corpus

table : List (String × NTm [])
table = numTable ++ lamTable

names : String
names = go table
  where
  go : List (String × NTm []) → String
  go []             = ""
  go ((n , _) ∷ ts) = n <> "\n" <> go ts

lookupN : String → List (String × NTm []) → Maybe (NTm [])
lookupN k []             = nothing
lookupN k ((n , t) ∷ ts) = if primStringEquality k n then just t else lookupN k ts

theTm : String → Maybe (NTm [])
theTm k = lookupN k table

at : (NTm [] → String) → String → String
at f k = go (theTm k)
  where
  go : Maybe (NTm []) → String
  go nothing  = "?"
  go (just t) = f t

-- ... and the OLD table, for the two observables that need an `L.Tm`
lookupL : String → List (String × L.Tm []) → Maybe (L.Tm [])
lookupL k []             = nothing
lookupL k ((n , t) ∷ ts) = if primStringEquality k n then just t else lookupL k ts

atL : (L.Tm [] → String) → String → String
atL f k = go (lookupL k T.corpus)
  where
  go : Maybe (L.Tm []) → String
  go nothing  = "-"          -- an arithmetic term has no `L.Tm`
  go (just t) = f t

-- ==================================================================
-- §3  THE OBSERVABLES, EACH `String → String`.
-- ==================================================================

-- ------------------------------------------------------------------
-- 3.1  ARM.
-- ------------------------------------------------------------------

-- the assembly unit, `Compile.LinNum.Emit.asmN`
armAsm : String → String
armAsm = at asmN

-- its length in instructions, which is `ARM.progLen` and hence the
-- label the halt branches to
armLen : String → String
armLen = at (λ t → showℕ (unitLen t))

-- WHAT THE MACHINE HOLDS: field 0 of the answer record, which is what
-- `finCode`'s `ldr x0, [x9]` loads.  The process masks it to eight
-- bits; that is the runner's business, not this file's.
armExit : String → String
armExit = at (λ t → showMℕ (armWord 2000 t))

-- ... and what the MODEL says that word will be
refExit : String → String
refExit = at (λ t → showMℕ (refWord t))

-- ------------------------------------------------------------------
-- 3.2  THE THREE INTERPRETERS.
-- ------------------------------------------------------------------

-- the IR's own abstract machine, at fuel 64 -- `Convert.obsN`
refAns : String → String
refAns = at (λ t → showMVal (obsN t))

-- the Rust big-step evaluator, i.e. `_⇓_`'s normal form
rustAns : String → String
rustAns = at (λ t → NR.showM (NR.rustAns t))

-- the OLD backend's DECODED ARM answer -- real AArch64 executed by
-- `Control.run`, the heap walked by `ARM.decodeV`.  Only defined on the
-- pure λ-fragment: `decodeV` reads every record as a closure, and
-- `Compile/LinNum/ARM.agda` §B is the argument that it should not be
-- made to guess otherwise.
armDecoded : String → String
armDecoded = atL (λ t → showMVal₀ (AM.answerT 500 8 t))

-- all of it at once, semicolon separated, so one `agda` run answers a
-- whole row
interpRow : String → String
interpRow k =
     refAns k <> ";" <> refExit k <> ";" <> armExit k
  <> ";" <> rustAns k <> ";" <> armDecoded k

-- ------------------------------------------------------------------
-- 3.3  RUST SOURCE.
-- ------------------------------------------------------------------

-- the runnable one: the universal value type, and it PRINTS
rustSrc : String → String
rustSrc = at NR.srcOf

-- what the emitted program will print
rustPred : String → String
rustPred = at (λ t → NR.showPrinted (NR.rustAns t))

-- the ORIGINAL `Codegen.srcTm`, which rustc rejects (E0282).  Only on
-- the pure λ-fragment, which is all that emitter accepts.
rustSrc0 : String → String
rustSrc0 = atL (λ t → RC.runAt RC.srcTm [] t)

-- ... and `LinToRust/Run.agda`'s repair of it, for the same fragment
rustSrc1 : String → String
rustSrc1 = atL (λ t → RC.runAt RR.mainTm [] t)

-- ==================================================================
-- §4  IT COMPUTES.
-- ==================================================================

-- THE TARGET.  `(λx. x + 1) 41`, in all three.
_ : refAns   "incApp" ≡ "num 42"
_ = refl

_ : refExit  "incApp" ≡ "42"
_ = refl

_ : armExit  "incApp" ≡ "42"
_ = refl

_ : rustAns  "incApp" ≡ "42"
_ = refl

_ : rustPred "incApp" ≡ "42"
_ = refl

-- the pure λ-fragment still answers what it answered
_ : refAns     "idLin" ≡ "clos 0"
_ = refl

_ : armExit    "idLin" ≡ "6"
_ = refl

_ : armDecoded "bigT"  ≡ "clos 1[clos 2]"
_ = refl

-- an arithmetic term has no old-backend rendering, and says so
_ : rustSrc0 "incApp" ≡ "-"
_ = refl

-- an unknown name is answered, not raised
_ : armExit "nosuchterm" ≡ "?"
_ = refl
