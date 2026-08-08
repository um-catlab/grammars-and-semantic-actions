{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  TASK 4: END TO END.  AN ANNOTATED TERM, TYPED, CHECKED LINEAR, AND
  COMPILED TO RUST SOURCE TEXT -- EVERY STAGE PINNED BY `refl`.

  `Chain.Typing` found that `LinTyped` cannot type the front end's
  output because that output is annotation-free and a bare lambda does
  not synthesise.  The resolution taken here is the one a proof of
  concept should take: REQUIRE THE ANNOTATIONS.  The type universe is
  already small -- `Ty = base | _⊸ᵗ_` -- and `LinTyped` types annotated
  terms today, so nothing has to be inferred and no inference pass has
  to be written.

  What that costs is one honest scope note, and it is the only one:
  the SOURCE of this pipeline is an annotated `Raw`, not a string.
  `Lambda.Parse`'s alphabet is `{x, y, λx., λy.}` and has no type
  syntax, so a string front end would need annotation tokens.  The
  parser is independently verified for the UNANNOTATED language
  (`Chain.Pipeline`), and this file starts one stage later.

  ------------------------------------------------------------------
  THE TWO VERDICTS ARE INDEPENDENT, AND THAT IS THE DESIGN.

      TYPE       `LinTyped.closed-infer?`   over the three-sorted theory
      LINEARITY  `LinLam.Check.linear?`     over `dbFib`

  Neither implies the other -- `LinTyped.Tests` pins `kAnn` and `dupAnn`
  as simply typeable and NOT linear -- and they meet only at the
  skeleton, which is what `stripAnn` produces and what `Lin` is already
  stated up to.  So the wiring is one erasure and one scope check, and
  every theorem on either side is used unchanged.

  ------------------------------------------------------------------
  THE PIPELINE.

      Raw (annotated)  --closed-infer?-->  Ty            [LinTyped]
                       --stripAnn------->  Skel          §1
                       --toDB?---------->  DBTm 0        §1
                       --linear?-------->  Tm u          [LinLam]
                       --compileRust---->  RExpr
                       --srcTm---------->  Rust source   [verified square]

  Only §1 is new; every other arrow is a theorem someone already proved.

  PHASE.  `stripAnn`, `fin?` and `toDB?` are PRIMITIVES -- carrier maps
  between theories over different signatures, the same escape
  `Chain.Elab.stripL` is.  Everything else is a term, and `run`/`runAt`
  occur only in the `refl` lines of §3.
-}
open import Cubical.Foundations.Prelude

module Chain.Rust where

open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma
open import Cubical.Data.FinData.Base using (Fin) renaming (zero to fzero; suc to fsuc)

open import Agda.Builtin.String using () renaming (String to UString)

open import TheoryGrammar.SemanticAction using (passes; _↦_; _at_)
open import TheoryGrammar.Instances.LinTyped

import TheoryGrammar.Instances.LinLam.Syntax as L
import TheoryGrammar.Instances.LinLam.DB     as D
import TheoryGrammar.Instances.LinLam.Check  as C
import Compile.LinToRust.Codegen             as FR

-- ==================================================================
-- §1  THE TWO MISSING CONVERSIONS.  Both PRIMITIVE, both total or
-- explicitly partial, and both about ten lines.  This is the entire
-- new code in the file.
-- ==================================================================

mapMb : {X Y : Type₀} → (X → Y) → Maybe X → Maybe Y
mapMb f (just x) = just (f x)
mapMb f nothing  = nothing

-- PRIMITIVE (phase 1): drop the annotations.  They were consumed by the
-- typechecker and carry nothing the linearity checker or the code
-- generator can read -- `Lin` is stated up to `skel`, so `Skel` is
-- exactly the right target.
stripAnn : Raw → C.Skel
stripAnn (var i)   = C.svar i
stripAnn (app f a) = C.sapp (stripAnn f) (stripAnn a)
stripAnn (lam b)   = C.slam (stripAnn b)
stripAnn (ann t _) = stripAnn t

-- PRIMITIVE (phase 1): the scope check.  `Skel` has `ℕ` indices and
-- `DBTm n` has `Fin n`, so this is where an out-of-scope index is
-- rejected -- the one partial arrow in the file.
fin? : (n i : ℕ) → Maybe (Fin n)
fin? zero    _       = nothing
fin? (suc n) zero    = just fzero
fin? (suc n) (suc i) = mapMb fsuc (fin? n i)

toDB? : (n : ℕ) → C.Skel → Maybe (D.DBTm n)
toDB? n (C.svar i)   = mapMb D.dvar (fin? n i)
toDB? n (C.sapp f a) with toDB? n f | toDB? n a
... | just u | just v = just (D.dapp u v)
... | _      | _      = nothing
toDB? n (C.slam b)   = mapMb D.dlam (toDB? (suc n) b)

-- ==================================================================
-- §2  THE TWO VERDICTS, AS TERMS.  Both are decisions, so both failure
-- branches carry refutations rather than a `nothing`.
-- ==================================================================

o oo : Ty
o  = base
oo = o ⊸ᵗ o

-- TYPE, over `LinTyped`'s three-sorted theory
typeOf : ⊤G ⊢ Result (¬G (Syn [])) (Δ Ty)
typeOf = mapR (¬G (Syn [])) (Δ Ty) (tagA Ty) ∘g closed-infer?

typed! : ⊤G ⊢ Δ Bool
typed! = okA (Syn []) (¬G (Syn [])) ∘g closed-infer?

noType : (t : Raw) → run typed! t ≡ false → (¬G (Syn [])) t
noType = refute (Syn []) (¬G (Syn [])) closed-infer?

-- LINEARITY, over `dbFib` -- `LinLam.Check`, used verbatim
linear! : D.⊤G D.⊢ D.Δ Bool
linear! = C.linearB

noLinear : (m : D.Term•) → D.run linear! m ≡ false → (D.¬G C.Lin) m
noLinear = D.refute C.Lin (D.¬G C.Lin) C.linear?

-- ==================================================================
-- §3  THE PIPELINE, ON THREE ANNOTATED TERMS.
--
-- For each: the synthesised type, the skeleton, the de Bruijn term, the
-- usage, the intrinsically linear term, and the Rust.  Every line is a
-- `refl`, so the chain is discharged by typechecking this file.
-- ==================================================================

-- ------------------------------------------------------------------
-- 3.1  THE IDENTITY.  `λx. x` at `o ⊸ o`.
-- ------------------------------------------------------------------

srcId : Raw
srcId = ann (lam (var 0)) oo

_ : passes (runΔ Ty (¬G (Syn [])) typeOf at (srcId ↦ just oo ∷ []))
_ = refl

_ : stripAnn srcId ≡ C.slam (C.svar 0)
_ = refl

_ : toDB? 0 (stripAnn srcId) ≡ just (D.dlam (D.dvar fzero))
_ = refl

dbId : D.DBTm 0
dbId = D.dlam (D.dvar fzero)

_ : D.run linear! (0 , dbId) ≡ true
_ = refl

linId : C.Lin (0 , dbId)
linId = D.witness C.Lin (D.¬G C.Lin) C.linear? (0 , dbId) refl

-- the usage is empty -- the term is closed -- so no `subst` is needed
_ : linId .fst ≡ []
_ = refl

tmId : L.Tm []
tmId = linId .snd .snd .fst

_ : tmId ≡ L.idLin
_ = refl

-- THE RUST.  `runAt` is the exit and it occurs only here.
rustId : UString
rustId = FR.runAt FR.srcTm [] tmId

_ : rustId ≡ "enum U { A, B }\n\nfn main() {\n    let _ = move |x0| x0;\n}\n"
_ = refl

-- ------------------------------------------------------------------
-- 3.2  THE FLAGSHIP.  `(λx.x)(λx.x)` -- the term `Chain.Typing` proved
-- is REJECTED annotation-free.  With one annotation, at the function of
-- the application and nowhere else, it types.
-- ------------------------------------------------------------------

srcSelf : Raw
srcSelf = app (ann (lam (var 0)) (oo ⊸ᵗ oo)) (lam (var 0))

_ : passes (runΔ Ty (¬G (Syn [])) typeOf at (srcSelf ↦ just oo ∷ []))
_ = refl

-- ... and the annotation vanishes at the skeleton, so the linearity
-- checker and the code generator see exactly what they saw before
_ : stripAnn srcSelf ≡ C.sapp (C.slam (C.svar 0)) (C.slam (C.svar 0))
_ = refl

dbSelf : D.DBTm 0
dbSelf = D.dapp (D.dlam (D.dvar fzero)) (D.dlam (D.dvar fzero))

_ : toDB? 0 (stripAnn srcSelf) ≡ just dbSelf
_ = refl

_ : D.run linear! (0 , dbSelf) ≡ true
_ = refl

linSelf : C.Lin (0 , dbSelf)
linSelf = D.witness C.Lin (D.¬G C.Lin) C.linear? (0 , dbSelf) refl

tmSelf : L.Tm []
tmSelf = linSelf .snd .snd .fst

_ : tmSelf ≡ L.selfApp
_ = refl

rustSelf : UString
rustSelf = FR.runAt FR.srcTm [] tmSelf

_ : rustSelf
  ≡ "enum U { A, B }\n\nfn main() {\n    let _ = (move |x0| x0)(move |x0| x0);\n}\n"
_ = refl

-- ------------------------------------------------------------------
-- 3.3  TWO BINDERS.  `λf. λx. f x` at `(o ⊸ o) ⊸ (o ⊸ o)`.
-- ------------------------------------------------------------------

srcApp : Raw
srcApp = ann (lam (lam (app (var 1) (var 0)))) (oo ⊸ᵗ oo)

_ : passes (runΔ Ty (¬G (Syn [])) typeOf at (srcApp ↦ just (oo ⊸ᵗ oo) ∷ []))
_ = refl

dbApp : D.DBTm 0
dbApp = D.dlam (D.dlam (D.dapp (D.dvar (fsuc fzero)) (D.dvar fzero)))

_ : toDB? 0 (stripAnn srcApp) ≡ just dbApp
_ = refl

_ : D.run linear! (0 , dbApp) ≡ true
_ = refl

linApp : C.Lin (0 , dbApp)
linApp = D.witness C.Lin (D.¬G C.Lin) C.linear? (0 , dbApp) refl

rustApp : UString
rustApp = FR.runAt FR.srcTm [] (linApp .snd .snd .fst)

_ : rustApp
  ≡ "enum U { A, B }\n\nfn main() {\n    let _ = move |x0| move |x1| (x0)(x1);\n}\n"
_ = refl

-- ==================================================================
-- §4  THE TWO VERDICTS ARE GENUINELY INDEPENDENT.
--
-- `LinTyped.Tests` pins `kAnn`/`dupAnn` as simply typeable and not
-- linear; here is the same fact ON THIS PIPELINE, as refutations.  A
-- term can pass the type stage and fail the linearity stage, which is
-- why both stages exist.
-- ==================================================================

-- `λx. λy. x` -- discards `y`
srcK : Raw
srcK = ann (lam (lam (var 1))) (o ⊸ᵗ (o ⊸ᵗ o))

dbK : D.DBTm 0
dbK = D.dlam (D.dlam (D.dvar (fsuc fzero)))

_ : toDB? 0 (stripAnn srcK) ≡ just dbK
_ = refl

-- it FAILS linearity, and the failure is a refutation
_ : D.run linear! (0 , dbK) ≡ false
_ = refl

kNotLinear : (D.¬G C.Lin) (0 , dbK)
kNotLinear = noLinear (0 , dbK) refl

-- ... and a term can fail the TYPE stage while its skeleton is
-- perfectly linear: drop the annotation and `srcId` stops synthesising,
-- which is `Chain.Typing`'s obstruction restated on this pipeline.
idNoType : (¬G (Syn [])) (lam (var 0))
idNoType = noType (lam (var 0)) refl

-- the scope check is real too: an index past the binders is rejected
_ : toDB? 0 (C.slam (C.svar 3)) ≡ nothing
_ = refl

-- ==================================================================
-- §5  AND WHEN THE TYPE STAGE FAILS, IT SAYS WHERE.
--
-- `Chain.TypeLocate` descends to the smallest failing subterm and
-- builds a `Chain.Diagnostic.Diagnostic`, the same record
-- `Chain.Locate` uses for linearity.  Here it is on this pipeline's
-- own rejected input: `srcSelf` with the annotation removed, which is
-- exactly the term `Chain.Typing.selfAppNoSyn` refutes.
-- ==================================================================

import Chain.TypeLocate as TL
import Chain.Diagnostic

srcSelfBare : Raw
srcSelfBare = app (lam (var 0)) (lam (var 0))

-- the pipeline rejects it ...
_ : run typed! srcSelfBare ≡ false
_ = refl

bareNoType : (¬G (Syn [])) srcSelfBare
bareNoType = noType srcSelfBare refl

-- ... and the diagnostic points at the FUNCTION, with the repair
_ : Chain.Diagnostic.site (TL.typeBlame [] oo srcSelfBare) ≡ lam (var 0)
_ = refl

_ : TL.report [] oo srcSelfBare
  ≡ "cannot synthesise a type here -- add an annotation\n  in:  \\. 0"
_ = refl

-- ... which is precisely the one annotation §3.2 adds.  The diagnostic
-- and the repair agree, and neither was written with the other in view.
_ : srcSelf ≡ app (ann (lam (var 0)) (oo ⊸ᵗ oo)) (lam (var 0))
_ = refl
