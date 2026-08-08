{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  TASK 3: A TYPE ERROR THAT POINTS AT A SUBTERM.

  `Chain.Locate` does this for LINEARITY failures: it consults
  `LinLam.Check.linear?` at the subterms of a LOCATED de Bruijn term,
  descends to the smallest one that fails on its own, and builds a
  `Diagnostic S3ˡ` which `Chain.Diagnostic.along` carries down to a
  character range.  This file is the same shape for TYPE failures, with
  `LinTyped.typecheck` as the oracle.

  ------------------------------------------------------------------
  AND ONE HONEST SCOPE NOTE, WHICH IS THE HANDOFF'S WARNING ARRIVING
  FROM THE OTHER SIDE.

  The handoff says: use the RETAINED SPAN, not the reprint cascade,
  because `unSkel` reprints `"λx. x"` for `"λy. x"`.  That is right, and
  for TYPE errors the span is not available at all -- for a reason worth
  stating rather than working around:

      the span-indexed front end produces ANNOTATION-FREE terms
      (`Chain.Typing.tmNoAnn`), and an annotation-free term does not
      typecheck (`Chain.Typing.selfAppNoSyn`).

  So there is no term that both carries a span and reaches the type
  checker, and a type diagnostic cannot be located in the source until
  annotations reach the parser.  Rather than fabricate a span, the site
  here is the SUBTERM ITSELF, which is what `Chain.Diagnostic` wanted
  anyway -- its §1 says the site is an `Ir` and NOT a span, "because
  spans are one stage's way of locating and the cascade has six stages".

  ------------------------------------------------------------------
  AND THE PROJECTION IS *NOT* AVAILABLE EITHER, WHICH IS A RESULT.

  One would like `RawStage ↘ Sˢ` along `stripAnn`, so a type diagnostic
  could travel the cascade like a linearity one.  It does not exist:
  `↘` demands `faith`, "the projection prints the same program", and
  `stripAnn` DELETES TEXT.  `notFaithful` below is that, with a witness.

  This is not a defect in `↘`.  It is `↘` correctly refusing a
  projection that loses what the message is about: a diagnostic saying
  "expected `o`, got `o ⊸ o`" is precisely a statement about an
  annotation, and carrying it to a stage with no annotations would point
  it at something else.  Compare `Chain.PrintTests` §5, where the same
  `faith` obligation refuted `Section` for the elaboration link.

  PHASE.  §1 (printing) and §3 (the descent) are phase-1 primitives, as
  `Chain.Locate`'s §4 is and for the same reason: they choose where to
  point and decide nothing.  §2 is the oracle, and it is `typecheck`
  used unchanged.
-}
open import Cubical.Foundations.Prelude

module Chain.TypeLocate where

open import Cubical.Data.Bool using (Bool; true; false; if_then_else_; true≢false)
open import Cubical.Data.Empty as E using ()
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma using (_×_; _,_)

open import Agda.Builtin.String
  using (primStringAppend; primShowNat; primStringToList) renaming (String to UString)
open import Agda.Builtin.Char using (Char)

open import TheoryGrammar.Instances.LinTyped

open import Chain.Project
open import Chain.Diagnostic

-- ==================================================================
-- §1  PRINTING AN ANNOTATED TERM.  PRIMITIVE (phase 1): a stage needs
-- a `says`, and the annotated syntax has no printer yet.
-- ==================================================================

_++s_ : UString → UString → UString
_++s_ = primStringAppend

infixr 5 _++s_

showTy : Ty → UString
showTy base      = "o"
showTy (A ⊸ᵗ B) = "(" ++s showTy A ++s " -o " ++s showTy B ++s ")"

showRaw : Raw → UString
showRaw (var i)   = primShowNat i
showRaw (app f a) = "(" ++s showRaw f ++s " " ++s showRaw a ++s ")"
showRaw (lam b)   = "\\. " ++s showRaw b
showRaw (ann t T) = "(" ++s showRaw t ++s " : " ++s showTy T ++s ")"

-- the stage of annotated terms
RawStage : Stage
RawStage .Ir   = Raw
RawStage .says = showRaw

-- ------------------------------------------------------------------
-- ... and the projection one would want DOES NOT EXIST.  `stripAnn`
-- would be the map; `faith` refutes it, because erasing an annotation
-- changes the text.  Two terms, one erasure, two printed forms.
-- ------------------------------------------------------------------

stripAnn : Raw → Raw                      -- PRIMITIVE (phase 1)
stripAnn (var i)   = var i
stripAnn (app f a) = app (stripAnn f) (stripAnn a)
stripAnn (lam b)   = lam (stripAnn b)
stripAnn (ann t _) = stripAnn t

annotated bare : Raw
annotated = ann (lam (var 0)) (base ⊸ᵗ base)
bare      = lam (var 0)

sameErasure : stripAnn annotated ≡ stripAnn bare
sameErasure = refl

-- so a `↘` along `stripAnn` would have to make these print alike ...
-- PRIMITIVE (phase 1): a computable observation that separates them --
-- the annotated form is parenthesised and the bare one is not.
firstIsParen : UString → Bool
firstIsParen s with primStringToList s
... | ('(' ∷ _) = true
... | _         = false

notFaithful : showRaw annotated ≡ showRaw bare → E.⊥
notFaithful p = true≢false (cong firstIsParen p)

-- ==================================================================
-- §2  THE ORACLE.  `LinTyped.typecheck`, at an arbitrary context, used
-- unchanged.  This file re-implements no typing rule.
-- ==================================================================

checksIn : Ctx → Ty → ⊤G ⊢ Δ Bool
checksIn Γ T =
  okA (Check Γ T) (¬G (Check Γ T)) ∘g (&ᴰ-E (Ctx × Ty) (Γ , T) ∘g check?)

synthsIn : Ctx → ⊤G ⊢ Δ Bool
synthsIn Γ = okA (Syn Γ) (¬G (Syn Γ)) ∘g (&ᴰ-E Ctx Γ ∘g infer?)

-- ==================================================================
-- §3  THE DESCENT.  PRIMITIVE (phase 1), exactly as `Chain.Locate`'s
-- `blameAt`: descend while the failure is INHERITED, stop at the first
-- node that fails on its own, and name why.
-- ==================================================================

-- Only faults the descent below can actually EMIT.  A constructor for
-- "applied but not a function" is deliberately absent: distinguishing
-- it from an argument mismatch needs the synthesised type, which this
-- descent does not extract, and a fault the code never produces would
-- claim more than the file does.
data Fault : Type₀ where
  needsAnn  : Fault        -- synthesis has no rule here; annotate it
  mismatch  : Ty → Fault   -- checked against this and failed
  badVar    : Fault        -- unbound, OR the context is not consumed

faultMsg : Fault → UString
faultMsg needsAnn     = "cannot synthesise a type here -- add an annotation"
faultMsg (mismatch T) = "does not have the expected type " ++s showTy T
faultMsg badVar       =
  "this variable does not consume the context (unbound, or others unused)"

-- PRIMITIVE (phase 1): the smallest subterm that fails to CHECK at the
-- given type.  `lam` descends into the body at the codomain; an `app`
-- cannot check at all -- it must synthesise -- so the blame moves to
-- its head, which `nonSyn` walks.  The `if` at each node is exactly the
-- test "is this node's failure INHERITED?", so a node whose child
-- already fails is never blamed.
blameChk : ℕ → Ctx → Ty → Raw → Raw × Fault
blameChk zero    Γ T t = t , mismatch T
blameChk (suc n) Γ T t = go T t
  where
  -- why a term failed SYNTHESIS.  `lam` is the only former with no
  -- synthesis rule, so it is the only one that can be blamed outright.
  nonSyn : Raw → Raw × Fault
  nonSyn (lam b)   = lam b , needsAnn
  nonSyn (var i)   = var i , badVar
  nonSyn (app f a) = nonSyn f
  nonSyn (ann u A) = if run (checksIn Γ A) u
                       then (ann u A , mismatch A)
                       else blameChk n Γ A u

  go : Ty → Raw → Raw × Fault
  go S (var i)    = if run (synthsIn Γ) (var i)
                      then (var i , mismatch S) else (var i , badVar)
  go S (app f a)  = if run (synthsIn Γ) f
                      then (app f a , mismatch S) else nonSyn f
  go S (ann u A)  = if run (checksIn Γ A) u
                      then (ann u A , mismatch S) else blameChk n Γ A u
  go base    (lam b) = lam b , mismatch base
  go (A ⊸ᵗ B) (lam b) = if run (checksIn (just A ∷ Γ) B) b
                           then (lam b , mismatch (A ⊸ᵗ B))
                           else blameChk n (just A ∷ Γ) B b

-- the sentence, and the site, as a `Diagnostic`
typeBlame : Ctx → Ty → Raw → Diagnostic RawStage
typeBlame Γ T t = mkDiag (faultMsg (b .snd)) (b .fst)
  where b = blameChk 64 Γ T t

-- ... and the whole report, as text
report : Ctx → Ty → Raw → UString
report Γ T t =
  d .msg ++s "\n  in:  " ++s saysSite RawStage d
  where d = typeBlame Γ T t

-- ==================================================================
-- §4  IT COMPUTES, AND IT POINTS AT THE RIGHT SUBTERM.
-- ==================================================================

o oo : Ty
o  = base
oo = o ⊸ᵗ o

-- 4.1  a well-typed term produces no descent: the whole term is
-- reported, which is the degenerate case
_ : run (checksIn [] oo) (lam (var 0)) ≡ true
_ = refl

-- 4.2  THE BARE LAMBDA IN AN APPLICATION -- `Chain.Typing`'s
-- obstruction, located.  The blame is on the FUNCTION, not on the
-- application, and the message says what to do about it.
selfBare : Raw
selfBare = app (lam (var 0)) (lam (var 0))

_ : typeBlame [] oo selfBare .site ≡ lam (var 0)
_ = refl

_ : report [] oo selfBare
  ≡ "cannot synthesise a type here -- add an annotation\n  in:  \\. 0"
_ = refl

-- 4.3  A NESTED MISMATCH.  The body of the binder is at the wrong type,
-- and the blame descends past the binder rather than stopping at it.
nested : Raw
nested = lam (lam (var 1))

_ : typeBlame [] (o ⊸ᵗ (o ⊸ᵗ (o ⊸ᵗ o))) nested .site ≡ var 1
_ = refl

-- 4.4  AN ANNOTATION THAT LIES.  The blame lands inside the `ann`, at
-- the term the annotation is wrong about.
liar : Raw
liar = ann (lam (var 0)) o

_ : typeBlame [] o liar .site ≡ lam (var 0)
_ = refl

_ : report [] o liar
  ≡ "does not have the expected type o\n  in:  \\. 0"
_ = refl

-- 4.5  THE SITE PRINTS, and `Chain.Diagnostic.saysSite` is what prints
-- it -- so when a span-carrying annotated source exists, `along` moves
-- this diagnostic without a line of new code.  §1's `notFaithful` says
-- the move cannot be along `stripAnn`.
_ : saysSite RawStage (typeBlame [] oo selfBare) ≡ "\\. 0"
_ = refl
