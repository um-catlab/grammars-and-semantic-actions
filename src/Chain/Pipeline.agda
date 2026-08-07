{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE END-TO-END CHAIN: A UNICODE STRING, COMPILED, WITH A CHECKPOINT AT
  EVERY PASS.

  Everything in this repository below is built and tested; nothing below
  was ever CONNECTED.  This file connects it, on one concrete input, and
  measures each pass against a literal expected value.  Every checkpoint
  is a `refl`, so the claim "the chain runs" is discharged by
  typechecking this file rather than asserted in a comment.

  ==================================================================
  THE INPUT, AND WHY IT IS UNICODE

      src = "λx. x λy. y"

  with the actual U+03BB.  `Agda.Builtin.String.primStringToList` turns
  it into `List Char` and `Chain.Lex` reads it there.  The `λ` is not
  decoration: it is a three-byte character that the lexer must match, and
  it is the reason `Chain.Lex` has to produce a decidable equality on
  Agda's primitive `Char` -- which it does, from
  `primCharToNatInjective`, with NO postulate.  `String.Unicode` in this
  repository postulates the corresponding fact; this chain does not.

  ==================================================================
  THE PASSES, AND WHICH THEORY EACH ONE LIVES IN

    stage    theory                 pass
    -----    ------                 ----
      0      --                     `primStringToList`         (the exit)
      1      strFib Char            LEX      -- `Chain.Lex.scan`
      2      spanFib   (over Tok)   PARSE    -- `Chain.Parse.parses?`
      3      spanFib   (over Tok)   ELABORATE-- `Chain.Elab.elabA`
      3'     --                     ERASE    -- `Chain.Elab.stripL`   [BRIDGE]
      4      dbFib                  LINEARITY-- `LinLam.Check.linear?`
      5      linFib                 CODEGEN  -- ISA / C / Rust

  STAGES 1 AND 2 ARE THE SAME CONSTRUCTION AT TWO ALPHABETS, which is
  the exercise the chain was built to demonstrate.  `Strings.Base` is a
  module in an arbitrary `Char : Type₀`; stage 1 applies it at Unicode
  and stage 2's parser is `Spans.CYK` over `Tok`.  The theory is not
  re-derived at the token level -- it is a module application, and the
  DSL (`⊗ˢ`, `⊕ᴰ`, `Dec⟨_⟩`, `Δ`, `Result`) is literally the same DSL on
  both sides of the lexer.

  ==================================================================
  WHERE THE CHAIN IS PRINCIPLED AND WHERE IT IS HAND-BRIDGED.  Read this
  paragraph before believing any of the rest.

  PRINCIPLED (a term of the calculus, composed with `∘g`):

    stage 1   `scan` is `runAut scanLC scanCoalg scanAlg` -- the SAME
              hylomorphism `Strings.Automata.DFA` runs, at a different
              algebra.  A transducer is a carrier, not a new notion.
    stage 2   `parses?` is `Decide.derives?`, a `löb` over span length.
    stage 3   `elabA` is `Gμ.fold`, and its type `Term Γ ⊢ Δ (LDB
              (length Γ))` has NO error branch: closedness is the
              parser's non-terminal, so there is no scope-check pass at
              all.  That absence is a result, not an omission.
    stage 4   `linear?` is `runAut` again, at `dbFib`.
    stage 5   the three backends, and their three-way agreement, are
              `Compile.Showcase`'s theorems used unchanged.

  HAND-BRIDGED (a metalanguage function, flagged as such):

    stage 3'  `stripL : LDB k → LinLam.DB.DBTm k`.  The parsing theory
              and the linearity theory have de Bruijn carriers of the
              same SHAPE and different SIGNATURES, and `Reindex` -- which
              is a map of promodels over ONE signature -- cannot cross
              that.  `LinLam.Check`'s own header says the same thing
              about `Join`.  So this is a structural recursion in the
              metalanguage, three lines, and it is the seam.
    lex→parse `tapeOf`, which reads a `List LTok` as a function `ℕ → Tok`.
              The string theory's carrier is a LIST and the span theory's
              ambient word is a FUNCTION `ℕ → Tok`; this is the coercion,
              and its `nothing` case is discussed under §2 below.

  Two bridges, both three lines, both named.  Everything else composes.

  ==================================================================
  RETENTION, AND THE BACKWARD PROJECTION

  The user-visible requirement was that data be kept so one can project
  BACK to an earlier pass.  Two mechanisms, at the two places information
  would otherwise be destroyed:

    stage 1   `LTok = Tok × ℕ` -- each token carries the CHARACTER OFFSET
              at which it begins.  Threaded through the automaton's
              state, so `runAut` computes it and the algebra never
              measures a string.  Necessary because `λx.` is ONE token
              spanning THREE characters, so token index ≠ char index.

    stage 3   `LDB` is `DB` with a `Span` at every constructor, so the
              elaborated term knows which piece of the token stream each
              of its nodes came from.

  Composing the two gives §6's `sourceOf : Span → String`, and the
  demonstration is `proj-arg`: navigate to the ARGUMENT of the
  elaborated application, read its span, and recover the substring
  "λy. y" of the original Unicode input.  That is a genuine projection
  from stage 3 back to stage 0, through stages 2 and 1.

  A sibling effort is building the GENERIC version of this -- `Reindex`
  along a signature morphism, in `TheoryGrammar/Reindex/`.  This file
  deliberately does not import it and does not wait for it.  The slot it
  would fill is exactly `Chain.Elab`'s motive: `Δ (LDB k)` is `Δ (DB k)`
  reindexed along the span, done by hand.

  ==================================================================
  WHAT IS *NOT* CLAIMED

  Stage 5's heap backends are usage-directed, so the layout-level
  theorem they satisfy says nothing about computation --
  `Compile.Showcase` §7 refutes the strong square for the whole family
  and this file inherits that limitation verbatim.  In particular the
  chain's closed term compiles to the EMPTY program in all three heap
  backends, and §5.2 below pins that, deliberately.  The term-directed
  Rust backend (§5.3) is the one that distinguishes terms, and it is the
  one whose output is worth reading.

  Nothing here is a performance claim.  `löb` re-descends rather than
  tabulating (see `Spans.Base`), so the parser is exponential in span
  length; four tokens is comfortable, and this file is not evidence that
  forty would be.
-}
open import Cubical.Foundations.Prelude

module Chain.Pipeline where

open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Sigma
open import Cubical.Data.List using (List; []; _∷_; length)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Empty as E using ()
open import Cubical.Data.FinData.Base using (Fin) renaming (zero to fzero; suc to fsuc)
import Cubical.Data.Equality as Eq

open import Agda.Builtin.String
  using (primStringToList; primStringFromList) renaming (String to UString)
open import Agda.Builtin.Char using (Char)

-- stage 1 lives in the STRING theory, so it is imported qualified: its
-- `run`, `⊤G` and `Δ` are the string theory's, not the span theory's,
-- and keeping them apart is the point of the two instantiations.
import Chain.Lex as LX

-- stages 2 and 3 live in the SPAN theory
open import TheoryGrammar.Instances.Spans.CYK
open import TheoryGrammar.Instances.Lambda.Parse
  using (Tok; vx; vy; lx; ly; Nm; Nx; Ny)
import Chain.Elab as CE

-- stages 4 and 5
import TheoryGrammar.Instances.LinLam.DB      as D
import TheoryGrammar.Instances.LinLam.Check   as C
import TheoryGrammar.Instances.LinLam.Codegen as LL
import TheoryGrammar.Instances.Heap.Base      as H
import Compile.LinToISA.Machine        as AM
import Compile.LinToISA.Codegen        as ASM
import Compile.LinToC.Codegen          as CC
import Compile.LinToC.Print            as CP
import Compile.LinToRust.Alloc.Codegen as RS
import Compile.LinToRust.Codegen       as FR
import Compile.Showcase                as SH

-- ==================================================================
-- §0  THE SOURCE.  Stage 0 is `primStringToList`, and it is the only
-- place in the chain where an Agda `String` appears.
-- ==================================================================

src : UString
src = "λx. x λy. y"

srcChars : List Char
srcChars = primStringToList src

-- ELEVEN characters, and the `λ`s really are single `Char`s: this is the
-- Unicode claim, discharged.
_ : length srcChars ≡ 11
_ = refl

_ : srcChars ≡ 'λ' ∷ 'x' ∷ '.' ∷ ' ' ∷ 'x' ∷ ' '
              ∷ 'λ' ∷ 'y' ∷ '.' ∷ ' ' ∷ 'y' ∷ []
_ = refl

-- ==================================================================
-- §1  CHECKPOINT 1 -- LEX.  `strFib` at Unicode `Char`.
--
-- Four tokens, each tagged with the character offset it BEGINS at.  Note
-- `(ly , 6)`: the token was emitted when the `.` at offset 8 was read,
-- and is nonetheless located at the `λ` at offset 6.  That is the whole
-- of the retention mechanism, visible in one number.
-- ==================================================================

lexed : Maybe (List LX.LTok)
lexed = LX.lexS src

_ : lexed ≡ just ((lx , 0) ∷ (vx , 4) ∷ (ly , 6) ∷ (vy , 10) ∷ [])
_ = refl

-- ... and the ERROR BRANCH is real.  `λz.` is not a token of this
-- language, so the scan ends in the absorbing state and `finL` reports
-- it.  The `Maybe` is the error grammar of stage 1.
_ : LX.lexS "λz. z" ≡ nothing
_ = refl

-- a trailing `λx` with no `.` is a lexical error too, and for the OTHER
-- reason: the input ran out at a state that is not a token boundary.
_ : LX.lexS "x λx" ≡ nothing
_ = refl

-- ==================================================================
-- §2  THE FIRST HAND-BRIDGE: a token LIST read as a token FUNCTION.
--
-- The string theory's carrier is a `List Tok`; `Spans.CYK`'s ambient
-- word is a function `ℕ → Tok`.  `tapeOf` is the coercion, and
-- `orEmpty` collapses stage 1's error branch.
--
-- The collapse is safe rather than sloppy, and it is worth saying why:
-- at the EMPTY token list every position reads the default, and the
-- parser is then asked for a derivation of a span of positive length
-- over a word that has none.  A lexical error therefore surfaces as a
-- PARSE REFUTATION -- it is not swallowed.  `no-parse-of-garbage` below
-- is that, as a theorem.
-- ==================================================================

orEmpty : Maybe (List LX.LTok) → List LX.LTok
orEmpty (just ts) = ts
orEmpty nothing   = []

toks : List LX.LTok
toks = orEmpty lexed

-- PRIMITIVE (phase 1): list indexing, with `vy` as the out-of-range
-- default.  The default is never observed: `Spans.Base.allCuts`
-- enumerates only cuts INSIDE the span under decision.
tapeOf : List LX.LTok → ℕ → Tok
tapeOf []             _       = vy
tapeOf ((t , _) ∷ _)  zero    = t
tapeOf (_ ∷ ts)       (suc j) = tapeOf ts j

offOf : List LX.LTok → ℕ → ℕ
offOf []            _       = 0
offOf ((_ , i) ∷ _) zero    = i
offOf (_ ∷ ts)      (suc j) = offOf ts j

tape : ℕ → Tok
tape = tapeOf toks

-- the parser and elaborator, instantiated AT THE LEXER'S OUTPUT.  This
-- one line is the difference between this chain and
-- `Lambda.ParseTests`, whose tape is written by hand.
module M = CE tape

_ : tape 0 ≡ lx
_ = refl

_ : tape 3 ≡ vy
_ = refl

-- ==================================================================
-- §3  CHECKPOINT 2 -- PARSE.  `spanFib` over `Tok`.
--
-- The whole token stream is the span `(0 , 4)`, and it parses as a
-- CLOSED term.  `parses!` is `⊤G ⊢ Δ Bool`; `run` occurs only in the
-- `refl`.
-- ==================================================================

full : Span
full = 0 , 4

_ : run (M.parses! []) full ≡ true
_ = refl

-- the parse TREE, extracted from that `refl` by the generic `witness`.
-- Its TYPE is `M.Term []`, and by `Lambda.Parse.no-free-var` no such
-- tree can contain an occurrence the scope does not bind.
tree : M.Term [] full
tree = witness (M.Term []) (¬G (M.Term [])) (M.parses? []) full refl

-- ... and the negative direction is a THEOREM, not a `false`.  `(0 , 1)`
-- is the bare token `λx.` -- a binder with no body, not a term at all.
noParse : (Γ : M.Scope) (s : Span) → run (M.parses! Γ) s ≡ false → (¬G (M.Term Γ)) s
noParse Γ = refute (M.Term Γ) (¬G (M.Term Γ)) (M.parses? Γ)

no-bare-binder : M.Term [] (0 , 1) → E.⊥* {ℓ-zero}
no-bare-binder = noParse [] (0 , 1) refl

-- THE LEXICAL ERROR, PROPAGATED.  `garbage` is the tape of a source
-- string that does not lex; every span of positive length over it is
-- refuted, so stage 1's failure is recoverable as a stage-2 theorem
-- rather than lost in the `orEmpty`.
module Garbage = CE (tapeOf (orEmpty (LX.lexS "λz. z")))

no-parse-of-garbage : Garbage.Term [] (0 , 2) → E.⊥* {ℓ-zero}
no-parse-of-garbage =
  refute (Garbage.Term []) (¬G (Garbage.Term [])) (Garbage.parses? []) (0 , 2) refl

-- ==================================================================
-- §4  CHECKPOINT 3 -- ELABORATE.  The LOCATED de Bruijn term.
--
-- `M.elabClosed : M.Term [] ⊢ Δ (LDB 0)` has no error branch, so this
-- checkpoint cannot fail; what it measures is WHICH term came out.  The
-- grammar is ambiguous -- `λx. x λy. y` reads both as `(λx.x)(λy.y)` and
-- as `λx.(x (λy.y))` -- and the search returns the first, which is what
-- the expected value below pins.
--
-- Every node carries its SPAN.  Read the expected value as a table:
--
--     (0,4)  the application         "λx. x λy. y"
--     (0,2)  its function            "λx. x"
--     (1,1)  that binder's body      "x"
--     (2,2)  its argument            "λy. y"
--     (3,1)  that binder's body      "y"
-- ==================================================================

elabTree : M.LDB 0
elabTree = M.elabClosed full tree .fst

_ : elabTree
  ≡ M.lapp (0 , 4)
      (M.llam (0 , 2) (M.lvar (1 , 1) fzero))
      (M.llam (2 , 2) (M.lvar (3 , 1) fzero))
_ = refl

-- ... and the whole of stages 2+3 as ONE term of the calculus, run
-- through the generic observer: the only failure mode is the parse.
_ : runΔ (M.LDB 0) (¬G (M.Term [])) (M.elab []) full
  ≡ just (M.lapp (0 , 4)
           (M.llam (0 , 2) (M.lvar (1 , 1) fzero))
           (M.llam (2 , 2) (M.lvar (3 , 1) fzero)))
_ = refl

-- ------------------------------------------------------------------
-- CHECKPOINT 3' -- ERASE.  THE HAND-BRIDGE.  `stripL` throws away the
-- retention data and lands in the linearity theory's carrier.
-- ------------------------------------------------------------------

dbTree : D.DBTm 0
dbTree = M.stripL elabTree

_ : dbTree ≡ D.dapp (D.dlam (D.dvar fzero)) (D.dlam (D.dvar fzero))
_ = refl

-- ==================================================================
-- §5  CHECKPOINT 4 -- LINEARITY.  `dbFib`.
--
-- `C.linear? : ⊤G ⊢ Dec⟨ Lin ⟩`, unchanged from `LinLam.Check`.  The
-- positive answer CARRIES THE LINEAR TERM: `Lin m` is
--
--     Σ[ u ∈ Usage ] (length u ≡ n) × Σ[ e ∈ Tm u ] (eraseS e ≡ skel t)
--
-- so `witness` hands back a `Tm u` whose erasure is `dbTree`, and stage
-- 5 has something to compile.
-- ==================================================================

_ : D.run C.linearB (0 , dbTree) ≡ true
_ = refl

linRes : C.Lin (0 , dbTree)
linRes = D.witness C.Lin (D.¬G C.Lin) C.linear? (0 , dbTree) refl

-- THE USAGE COMPUTES TO `[]`, definitionally -- which is why the next
-- line typechecks with no `subst`.  Had it not reduced, `Tm (linRes
-- .fst)` would have needed a transport along `length u ≡ 0`, and by the
-- repository's own rule that transport would have frozen every `refl`
-- downstream.
_ : linRes .fst ≡ []
_ = refl

linTm : LL.Tm []
linTm = linRes .snd .snd .fst

-- ... and it is the term one expects: `(λx.x)(λx.x)`, i.e. `selfApp`.
_ : linTm ≡ LL.selfApp
_ = refl

-- ------------------------------------------------------------------
-- THE NEGATIVE CASE, as a THEOREM.  `λx. x x` lexes, parses, and
-- elaborates -- and then FAILS stage 4, because it duplicates.  The
-- failure is a refutation `Lin m → ⊥*`, supplied by `Dec⟨_⟩`'s
-- exclusion; nothing was re-proved to get it.
-- ------------------------------------------------------------------

module Dup = CE (tapeOf (orEmpty (LX.lexS "λx. x x")))

_ : LX.lexS "λx. x x" ≡ just ((lx , 0) ∷ (vx , 4) ∷ (vx , 6) ∷ [])
_ = refl

_ : run (Dup.parses! []) (0 , 3) ≡ true
_ = refl

dupTree : Dup.LDB 0
dupTree =
  Dup.elabClosed (0 , 3)
    (witness (Dup.Term []) (¬G (Dup.Term [])) (Dup.parses? []) (0 , 3) refl) .fst

dupDB : D.DBTm 0
dupDB = Dup.stripL dupTree

_ : dupDB ≡ D.dlam (D.dapp (D.dvar fzero) (D.dvar fzero))
_ = refl

_ : D.run C.linearB (0 , dupDB) ≡ false
_ = refl

noLin : (m : D.Term•) → D.run C.linearB m ≡ false → (D.¬G C.Lin) m
noLin = D.refute C.Lin (D.¬G C.Lin) C.linear?

-- THEOREM: the source text "λx. x x" has no linear reading.
no-linear-dup : (D.¬G C.Lin) (0 , dupDB)
no-linear-dup = noLin (0 , dupDB) refl

-- ==================================================================
-- §6  RETENTION, AND THE BACKWARD PROJECTION.
--
-- From stage 3's output, back through stage 2's spans and stage 1's
-- offsets, to stage 0's characters.
-- ==================================================================

-- how many CHARACTERS a token occupies.  `λx.` is three, `x` is one --
-- the lexical fact that makes token index ≠ character index, and the
-- only thing the projection needs beyond the offsets themselves.
tokWidth : Tok → ℕ
tokWidth vx = 1
tokWidth vy = 1
tokWidth lx = 3
tokWidth ly = 3

-- PRIMITIVE (phase 1): the half-open CHARACTER interval of a token span.
-- It begins where token `i` begins and ends where token `i+n-1` ends.
charRange : Span → ℕ × ℕ
charRange (i , zero)  = offOf toks i , offOf toks i
charRange (i , suc n) =
  offOf toks i
  , offOf toks (i + n) + tokWidth (tapeOf toks (i + n))

takeC : ℕ → List Char → List Char
takeC zero    _        = []
takeC (suc n) []       = []
takeC (suc n) (c ∷ cs) = c ∷ takeC n cs

dropC : ℕ → List Char → List Char
dropC zero    cs       = cs
dropC (suc n) []       = []
dropC (suc n) (c ∷ cs) = dropC n cs

sub : ℕ → ℕ → ℕ
sub a       zero    = a
sub zero    _       = 0
sub (suc a) (suc b) = sub a b

-- THE PROJECTION: a span of the TOKEN stream, read back as a substring
-- of the original UNICODE input.  `primStringFromList` is the mirror of
-- stage 0's `primStringToList`, and it is the only other place an Agda
-- `String` appears.
sourceOf : Span → UString
sourceOf s = primStringFromList (takeC len (dropC lo srcChars))
  where lo  = charRange s .fst
        len = sub (charRange s .snd) (charRange s .fst)

-- the whole input, recovered from the root's span
_ : sourceOf (0 , 4) ≡ "λx. x λy. y"
_ = refl

-- ------------------------------------------------------------------
-- THE DEMONSTRATION.  Navigate the ELABORATED term -- stage 3's output,
-- two theories away from the source -- to its argument, read the span
-- the elaborator retained there, and recover the text.
-- ------------------------------------------------------------------

-- PRIMITIVE (phase 1): navigation on the located term.  `argOf` and
-- `funOf` preserve the index, so they are total with the identity as
-- their default; `bodySpan` cannot return the BODY (its index is
-- `suc k`) so it returns the body's span, which is all the projection
-- needs.
argOf : {k : ℕ} → M.LDB k → M.LDB k
argOf (M.lapp _ _ a) = a
argOf t              = t

funOf : {k : ℕ} → M.LDB k → M.LDB k
funOf (M.lapp _ f _) = f
funOf t              = t

bodySpan : {k : ℕ} → M.LDB k → Span
bodySpan (M.llam _ b) = M.spanOf b
bodySpan t            = M.spanOf t

-- the argument of the application is the token span `(2,2)` ...
_ : M.spanOf (argOf elabTree) ≡ (2 , 2)
_ = refl

-- ... and that span is the SOURCE TEXT `λy. y`.  Stage 3 → stage 2 →
-- stage 1 → stage 0, and every arrow is data the chain kept on purpose.
proj-arg : sourceOf (M.spanOf (argOf elabTree)) ≡ "λy. y"
proj-arg = refl

proj-fun : sourceOf (M.spanOf (funOf elabTree)) ≡ "λx. x"
proj-fun = refl

-- ONE LEVEL DEEPER, and this is the case that needs the offsets.  The
-- body of the argument's binder is token index 3; its CHARACTER index
-- is 10, and the two differ by 7 precisely because `λx.` and `λy.` are
-- three characters each.  A chain that had kept only token indices
-- could not produce this string.
proj-inner : sourceOf (bodySpan (argOf elabTree)) ≡ "y"
proj-inner = refl

proj-inner-fun : sourceOf (bodySpan (funOf elabTree)) ≡ "x"
proj-inner-fun = refl

-- ==================================================================
-- §7  CHECKPOINT 5 -- CODEGEN.  `linFib`, three backends.
-- ==================================================================

-- ------------------------------------------------------------------
-- 5.1  A NON-TRIVIAL USAGE.  The chain's closed term allocates nothing
-- (see §5.2), so the heap backends are exercised on the OPEN sub-span
-- `(1,1)` -- the token `x` at scope `[x]`, which is the body of the
-- first binder.  Same tape, same parser, different non-terminal: this
-- is `Lambda.ParseTests` (iii)'s point, reused.
-- ------------------------------------------------------------------

openTree : M.LDB 1
openTree =
  M.elabA (Nx ∷ []) (1 , 1)
    (witness (M.Term (Nx ∷ [])) (¬G (M.Term (Nx ∷ [])))
             (M.parses? (Nx ∷ [])) (1 , 1) refl) .fst

_ : openTree ≡ M.lvar (1 , 1) fzero
_ = refl

openDB : D.DBTm 1
openDB = M.stripL openTree

_ : D.run C.linearB (1 , openDB) ≡ true
_ = refl

openLin : C.Lin (1 , openDB)
openLin = D.witness C.Lin (D.¬G C.Lin) C.linear? (1 , openDB) refl

-- ONE live variable
uOpen : LL.Usage
uOpen = openLin .fst

_ : uOpen ≡ true ∷ []
_ = refl

-- ------------------------------------------------------------------
-- 5.2  THE THREE HEAP BACKENDS, on that usage -- and they AGREE, by
-- `Compile.Showcase`'s theorem, unchanged.
-- ------------------------------------------------------------------

_ : LL.layout uOpen ≡ (0 , H.v1) ∷ []
_ = refl

_ : ASM.exec (ASM.compileU uOpen) [] ≡ (0 , H.v1) ∷ []
_ = refl

_ : CC.evalC (CC.compileC uOpen) [] ≡ (0 , H.v1) ∷ []
_ = refl

_ : RS.evalRust (RS.compileRust uOpen) [] ≡ (0 , H.v1) ∷ []
_ = refl

-- the three-way agreement, and its proofs REDUCE
_ : SH.agreeᴬᶜ uOpen ≡ Eq.refl
_ = refl

_ : SH.agreeᶜᴿ uOpen ≡ Eq.refl
_ = refl

_ : SH.agreeᴬᴿ uOpen ≡ Eq.refl
_ = refl

-- THE EMITTED CODE, for the source token `x`:
_ : ASM.compileU uOpen ≡ AM.putI 0 H.v1 ∷ []
_ = refl

_ : CP.body (CC.compileC uOpen) ≡ "  val_t x0 = V1;\n"
_ = refl

-- ... and THE LIMITATION, inherited verbatim from `Showcase` §7: the
-- chain's CLOSED term allocates nothing, so every heap backend emits the
-- empty program.  This is a fact about the observable, not about the
-- chain.
_ : ASM.compileTm [] linTm .fst ≡ []
_ = refl

_ : LL.layout [] ≡ []
_ = refl

-- ------------------------------------------------------------------
-- 5.3  THE TERM-DIRECTED BACKEND -- the one whose output is worth
-- reading, and the LAST CHECKPOINT OF THE CHAIN.  This string is the
-- compilation of the eleven Unicode characters at the top of the file.
-- ------------------------------------------------------------------

emitted : UString
emitted = FR.runAt FR.exprTextTm [] linTm

_ : emitted ≡ "(move |x0| x0)(move |x0| x0)"
_ = refl

-- ... and as a whole Rust source file
_ : FR.runAt FR.srcTm [] linTm
  ≡ "enum U { A, B }\n\nfn main() {\n    let _ = (move |x0| x0)(move |x0| x0);\n}\n"
_ = refl

-- ==================================================================
-- §8  THE CHECKPOINT TABLE.
--
-- Every line below is pinned by a `refl` above.  This is the whole
-- chain, on one input, in one place.
--
--   stage  pass         output
--   -----  ----         ------
--     0    read         'λ'∷'x'∷'.'∷' '∷'x'∷' '∷'λ'∷'y'∷'.'∷' '∷'y'∷[]
--     1    LEX          just ((lx,0) ∷ (vx,4) ∷ (ly,6) ∷ (vy,10) ∷ [])
--     2    PARSE        run (parses! []) (0,4)  =  true
--     3    ELABORATE    lapp (0,4) (llam (0,2) (lvar (1,1) 0))
--                                 (llam (2,2) (lvar (3,1) 0))
--     3'   ERASE        dapp (dlam (dvar 0)) (dlam (dvar 0))     [BRIDGE]
--     4    LINEARITY    true;  usage = [];  term = selfApp
--     5    CODEGEN      "(move |x0| x0)(move |x0| x0)"
--
--   backward projection (stage 3 -> stage 0)
--     spanOf (argOf elabTree)      = (2,2)   ->  "λy. y"
--     spanOf (funOf elabTree)      = (0,2)   ->  "λx. x"
--     bodySpan (argOf elabTree)    = (3,1)   ->  "y"
--
--   the same chain at the OPEN sub-span (1,1), scope [x], where the
--   heap backends have something to do
--     3    ELABORATE    lvar (1,1) 0
--     4    LINEARITY    true;  usage = true ∷ []
--     5    CODEGEN      layout = (0,v1) ∷ []
--                       ISA    = putI 0 v1 ∷ []
--                       C      = "  val_t x0 = V1;\n"
--                       and ISA = C = Rust, by `Showcase.agree*`
--
--   negative checkpoints, each a THEOREM rather than an observation
--     "λz. z"   fails stage 1  (nothing)
--     "x λx"    fails stage 1  (nothing -- ended off a token boundary)
--     (0,1)     fails stage 2  `no-bare-binder`
--     garbage   fails stage 2  `no-parse-of-garbage`
--     "λx. x x" fails stage 4  `no-linear-dup`
--
-- Three of the five negative cases are refutations carried by the error
-- grammar (`¬G`), and two are the lexer's `nothing`.  That asymmetry is
-- honest and is exactly `TheoryGrammar.Result`'s point: stage 1's error
-- grammar is `⊤G`-like (a `Maybe` says only "no"), stages 2 and 4 have
-- error grammar `¬G A` and so their failures carry proofs.  Upgrading
-- stage 1 to a decision would mean deciding the token grammar rather
-- than running a transducer, and the machinery for it exists
-- (`Strings.Decidable`); it is simply not what a lexer is normally
-- asked to do.
-- ==================================================================
