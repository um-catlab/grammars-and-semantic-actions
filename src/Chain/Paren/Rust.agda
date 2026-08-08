{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE WHOLE COMPILER, FROM SOURCE TEXT, WITH THE FAILURES CARRYING
  THEIR REFUTATIONS.

      String --lex--> [Tok] --parse--> Trm --resolve--> Raw
             --typecheck--> Ty --erase--> Skel --linear?--> Tm u
             --compileRust--> RExpr --render--> Rust

  `Chain.Rust` did this from a `Raw` written by hand in Agda, and glued
  the stages with `Maybe`.  Both are fixed here: the source is a string
  (`Chain.Paren`), and the error type KEEPS WHAT EACH STAGE PROVED.

  ==================================================================
  WHY `Maybe` WAS THE WRONG GLUE, concretely.

  Three of the five stages are DECISIONS -- `parseTrm`, `closed-infer?`,
  `linear?` -- so their failure branch is a `¬G`, i.e. a function into
  `⊥`: a proof that the input is not a term / has no type / is not
  linear.  A `Maybe` throws all three away and reports `nothing`.

  `Err` below keeps them:

      parseErr  ts r    r : (¬G Trm) ts            -- REFUTATION
      typeErr   e  r    r : (¬G (Syn [])) e        -- REFUTATION
      linErr    m  r    r : (¬G Lin) m             -- REFUTATION
      scopeErr  n       the unbound NAME
      lexErr            the scanner's `nothing`, which says only "no"

  That asymmetry is `TheoryGrammar.Result`'s point and `Chain.Pipeline`
  §8's, arriving with the right error type: a stage that DECIDES can
  hand back a theorem, and a stage that merely fails cannot.  Two of the
  five here are of the second kind and are marked.

  ==================================================================
  THE SCOPE ERROR IS A NEW ALGEBRA, AND THAT IS THE POINT OF `SynAlg`.

  `Chain.Paren.Elab.dbAlg` reports a free name as `nothing`.  Wanting
  the NAME instead is a different consumer of the same fold, so it is a
  different `SynAlg` (`dbAlgE`) and not a change to the parser, the
  elaborator, or anything upstream.  Nothing was modified to get a
  better diagnostic; something was supplied.
-}
open import Cubical.Foundations.Prelude

module Chain.Paren.Rust where

open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.FinData.Base using (Fin) renaming (zero to fzero; suc to fsuc)

open import Agda.Builtin.String
  using (primStringAppend; primStringFromList) renaming (String to UString)

open import Chain.Paren.Tokens
open import Chain.Paren.Grammar
open import Chain.Paren.Elab

open import TheoryGrammar.SemanticAction
open ActFib strFib using (Δ)

import TheoryGrammar.Instances.LinTyped         as LT
import TheoryGrammar.Instances.LinLam.Syntax    as L
import TheoryGrammar.Instances.LinLam.DB        as D
import TheoryGrammar.Instances.LinLam.Check     as C
import Compile.LinToRust.Codegen                as FR
import Chain.TypeLocate                         as TL

-- ==================================================================
-- §1  SCOPE RESOLUTION THAT NAMES THE OFFENDER.  A new `SynAlg`.
-- ==================================================================

data ScopeRes : Type₀ where
  unbound : Name → ScopeRes
  scoped  : LT.Raw → ScopeRes

ResE : Type₀
ResE = Env → ScopeRes

private
  onScoped : (LT.Raw → ScopeRes) → ScopeRes → ScopeRes
  onScoped f (scoped r)  = f r
  onScoped f (unbound n) = unbound n

  bothScoped : (LT.Raw → LT.Raw → ScopeRes) → ScopeRes → ScopeRes → ScopeRes
  bothScoped f (scoped u) (scoped v) = f u v
  bothScoped f (unbound n) _         = unbound n
  bothScoped f _          (unbound n) = unbound n

dbAlgE : SynAlg ResE LT.Ty
dbAlgE .varA n   = λ e → look (lookupN e n)
  where look : Maybe ℕ → ScopeRes
        look (just i) = scoped (LT.var i)
        look nothing  = unbound n
dbAlgE .lamA n b = λ e → onScoped (λ r → scoped (LT.lam r)) (b (n ∷ e))
dbAlgE .appA f a = λ e → bothScoped (λ u v → scoped (LT.app u v)) (f e) (a e)
dbAlgE .annA t T = λ e → onScoped (λ r → scoped (LT.ann r T)) (t e)
dbAlgE .baseA    = LT.base
dbAlgE .arrA a b = a LT.⊸ᵗ b

toRawE : Trm ⊢ Δ ResE
toRawE = readWith dbAlgE

-- ==================================================================
-- §2  THE ERROR TYPE.  Three constructors carry a REFUTATION.
-- ==================================================================

data Err : Type₀ where
  -- the scanner says only "no" -- its error grammar is `⊤G`-like
  lexErr   : Err
  -- ... the parser hands back a proof that the tokens are not a term
  parseErr : (ts : List Tok) → (¬G Trm) ts → Err
  -- ... the resolver hands back the offending NAME
  scopeErr : Name → Err
  -- ... the typechecker a proof that nothing is synthesised
  typeErr  : (e : LT.Raw) → (LT.¬G (LT.Syn [])) e → Err
  -- ... and the linearity checker a proof that the term is not linear
  linErr   : (m : D.Term•) → (D.¬G C.Lin) m → Err
  -- ... and one that says only "no", for the arrow §3 cannot yet prove
  -- total: `Skel → DBTm 0`.  Named rather than folded into `scopeErr`,
  -- because pretending an internal gap is a user error is how a
  -- diagnostic starts lying.
  rangeErr : C.Skel → Err

-- ==================================================================
-- §3  THE PIPELINE.  Each `with` scrutinises a DECISION, so the `inr`
-- branch is a refutation and is kept rather than dropped.
-- ==================================================================

-- PRIMITIVE (phase 1): drop the annotations for the linearity stage.
stripAnn : LT.Raw → C.Skel
stripAnn (LT.var i)   = C.svar i
stripAnn (LT.app f a) = C.sapp (stripAnn f) (stripAnn a)
stripAnn (LT.lam b)   = C.slam (stripAnn b)
stripAnn (LT.ann t _) = stripAnn t

mapMb' : {A B : Type₀} → (A → B) → Maybe A → Maybe B
mapMb' f (just a) = just (f a)
mapMb' f nothing  = nothing

fin? : (n i : ℕ) → Maybe (Fin n)
fin? zero    _       = nothing
fin? (suc n) zero    = just fzero
fin? (suc n) (suc i) = mapMb' fsuc (fin? n i)

toDB? : (n : ℕ) → C.Skel → Maybe (D.DBTm n)
toDB? n (C.svar i)   = mapMb' D.dvar (fin? n i)
toDB? n (C.sapp f a) with toDB? n f | toDB? n a
... | just u | just v = just (D.dapp u v)
... | _      | _      = nothing
toDB? n (C.slam b)   = mapMb' D.dlam (toDB? (suc n) b)

-- what a successful compilation produces
record Out : Type₀ where
  constructor mkOut
  field
    ty    : LT.Ty
    usage : L.Usage
    term  : L.Tm usage
    rust  : UString

open Out public

-- PRIMITIVE (phase 1): the composite.  Every `with` here scrutinises a
-- decision of the calculus; nothing invents a failure.
compileToks : List Tok → Err ⊎ Out
compileToks ts with parseTrm ts tt
... | inr k = inl (parseErr ts k)
... | inl d with toRawE ts d .fst []
...   | unbound n = inl (scopeErr n)
...   | scoped e with LT.closed-infer? e tt
...     | inr k = inl (typeErr e k)
...     | inl syn with toDB? 0 (stripAnn e)
...       | nothing = inl (rangeErr (stripAnn e))
...       | just db with C.linear? (0 , db) tt
...         | inr k = inl (linErr (0 , db) k)
...         | inl lin =
                inr (mkOut (syn .fst) (lin .fst) (lin .snd .snd .fst)
                           (FR.runAt FR.srcTm (lin .fst) (lin .snd .snd .fst)))

compile : UString → Err ⊎ Out
compile s with lexS s
... | nothing = inl lexErr
... | just ts = compileToks ts

-- ==================================================================
-- §4  THE MESSAGES.  The refutations are the CONTENT; these are the
-- sentences, and the type error's site comes from `Chain.TypeLocate`.
-- ==================================================================

_++s_ : UString → UString → UString
_++s_ = primStringAppend

infixr 5 _++s_

report : Err → UString
report lexErr           = "lexical error: not a token of this language"
report (parseErr _ _)   = "parse error: these tokens are not a term"
report (scopeErr n)     = "unbound variable: " ++s primStringFromList n
-- the type stage is SYNTHESIS, so there is no goal type to blame
-- against; fabricating one (`TL.report` needs one) would name the wrong
-- fault.  The sentence says what the stage actually decided.
report (typeErr e _)    = "type error: this term does not synthesise a type"
report (linErr _ _)     =
  "linearity error: a variable is used more than once, or not at all"
report (rangeErr _)     = "internal: a resolved index was out of range"

-- ==================================================================
-- §5  IT RUNS, AND THE FAILURES ARE THEOREMS.
-- ==================================================================

okOf : Err ⊎ Out → Bool
okOf (inl _) = false
okOf (inr _) = true

srcId srcSelf srcApp : UString
srcId   = "((\\x. x) : (o -o o))"
srcSelf = "(((\\x. x) : ((o -o o) -o (o -o o))) (\\y. y))"
srcApp  = "((\\f. \\a. (f a)) : ((o -o o) -o (o -o o)))"

_ : okOf (compile srcId) ≡ true
_ = refl

_ : okOf (compile srcSelf) ≡ true
_ = refl

_ : okOf (compile srcApp) ≡ true
_ = refl

-- ---- the identity, all the way to Rust -----------------------------
outId : Err ⊎ Out
outId = compile srcId

_ : outId ≡ inr (mkOut (LT.base LT.⊸ᵗ LT.base) [] L.idLin
                       "enum U { A, B }\n\nfn main() {\n    let _ = move |x0| x0;\n}\n")
_ = refl

-- ---- the flagship: from a STRING, with one annotation --------------
_ : compile srcSelf
  ≡ inr (mkOut (LT.base LT.⊸ᵗ LT.base) [] L.selfApp
               "enum U { A, B }\n\nfn main() {\n    let _ = (move |x0| x0)(move |x0| x0);\n}\n")
_ = refl

-- ==================================================================
-- §6  EACH FAILURE CLASS, AND WHAT IT CARRIES.
-- ==================================================================

_ : okOf (compile "x @ y")            ≡ false        -- lexical
_ = refl

_ : okOf (compile "(\\x. x")          ≡ false        -- parse
_ = refl

_ : okOf (compile "\\x. y")           ≡ false        -- scope
_ = refl

_ : okOf (compile "(\\x. x)")         ≡ false        -- no annotation: TYPE
_ = refl

-- `\x. \y. x` DISCARDS `y`, and it is rejected -- but by the TYPE
-- stage, not the linearity stage: `LinTyped`'s context is itself
-- linear, so a term that drops a variable has no type to synthesise.
-- The two notions agree, and the type stage sees it first.
_ : okOf (compile "((\\x. \\y. x) : (o -o (o -o o)))") ≡ false
_ = refl

-- ---- and the messages ----------------------------------------------
msgOf : Err ⊎ Out → UString
msgOf (inl e) = report e
msgOf (inr _) = "ok"

_ : msgOf (compile "\\x. y") ≡ "unbound variable: y"
_ = refl

_ : msgOf (compile "x @ y") ≡ "lexical error: not a token of this language"
_ = refl

_ : msgOf (compile "(\\x. x") ≡ "parse error: these tokens are not a term"
_ = refl

_ : msgOf (compile "((\\x. \\y. x) : (o -o (o -o o)))")
  ≡ "type error: this term does not synthesise a type"
_ = refl

-- ... and the same for a term that USES a variable twice
_ : msgOf (compile "((\\x. (x x)) : ((o -o o) -o o))")
  ≡ "type error: this term does not synthesise a type"
_ = refl

-- CONSEQUENCE, worth stating: `linErr` is not reachable from a term the
-- type stage accepted, because `LinTyped` already enforces linearity.
-- The linearity stage is kept as an INDEPENDENT check of the same fact
-- over a different theory (`dbFib`), which is what makes the agreement
-- of the two a result rather than a definition.
