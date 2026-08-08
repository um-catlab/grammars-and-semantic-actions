{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE FRONT END, ONCE.  Three stages, each a term of its own theory:

      parse : ⊤G ⊢ Result (¬G Trm)      (Δ ScopeRes)   strFib
      infer : ⊤G ⊢ Result (¬G (Syn [])) (Δ Ty)         linFib
      linB  : ⊤G ⊢ Δ Bool                              dbFib

  and between them three CROSSINGS, which is where `runΔ` belongs and
  the only place it does.  Stage 0 is `Grammar.parseTrm` -- `decμ` over
  `strFib`, no chart, no span.

  `LinTyped`'s context is itself linear, so a term that duplicates or
  drops a variable is refused by `closed-infer?` before `linear?` sees
  it; `noType` is the refutation, and `noLin` is unreachable from a
  term it accepted.
-}
open import Cubical.Foundations.Prelude

module Chain.Paren.Front where

open import Cubical.Data.Bool using (Bool; false)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.FinData.Base using (Fin)
  renaming (zero to fzero; suc to fsuc)

open import Agda.Builtin.String using () renaming (String to UString)

open import Chain.Paren.Tokens
open import Chain.Paren.Grammar
open import Chain.Paren.Elab

open import TheoryGrammar.SemanticAction
open import TheoryGrammar.RulesFib using (module RulesF)

open ActFib strFib using (Δ; Δ-E; mapA; pureA; okA; refute; run; runΔ)
open RulesF strFib
  using (_∘g_; _⊕_; ⊕-I₁; ⊕-I₂; Result; ok; err; caseR; mapR; joinR)

import TheoryGrammar.Instances.LinTyped      as LT
import TheoryGrammar.Instances.LinLam.Syntax as L
import TheoryGrammar.Instances.LinLam.DB     as D
import TheoryGrammar.Instances.LinLam.Check  as C
import TheoryGrammar.Instances.LinLam.IR     as LIR

-- §1  SCOPE RESOLUTION THAT NAMES THE OFFENDER.  `Elab.dbAlg` reports a
-- free name as `nothing`; wanting the NAME is a different consumer of
-- the same fold.  The carrier is constant, so this is a semantic action
-- and "resolution invents no variable" is a separate obligation.

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

-- §2  STAGE 1: THE PARSE.

resolve : Trm ⊢ Δ ScopeRes
resolve = mapA (λ f → f []) (readWith dbAlgE)

parse : ⊤G ⊢ Result (¬G Trm) (Δ ScopeRes)
parse = mapR (¬G Trm) (Δ ScopeRes) resolve ∘g parseTrm

parseB : ⊤G ⊢ Δ Bool
parseB = okA Trm (¬G Trm) ∘g parseTrm

noParse : (ts : List Tok) → run parseB ts ≡ false → (¬G Trm) ts
noParse = refute Trm (¬G Trm) parseTrm

-- §3  STAGE 2: TYPE SYNTHESIS.  `Syn Γ = ⊕ᴰ Ty (Infer Γ)`, so reading
-- the type off is `⊕ᴰ-E`; `Unique.synUnique` is what makes the tag well
-- defined.

synTy : LT.Syn [] LT.⊢ LT.Δ LT.Ty
synTy = LT.⊕ᴰ-E λ T → LT.pureA LT.Ty T

infer : LT.⊤G LT.⊢ LT.Result (LT.¬G (LT.Syn [])) (LT.Δ LT.Ty)
infer = LT.mapR (LT.¬G (LT.Syn [])) (LT.Δ LT.Ty) synTy LT.∘g LT.closed-infer?

inferB : LT.⊤G LT.⊢ LT.Δ Bool
inferB = LT.okA (LT.Syn []) (LT.¬G (LT.Syn [])) LT.∘g LT.closed-infer?

noType : (e : LT.Raw) → LT.run inferB e ≡ false → (LT.¬G (LT.Syn [])) e
noType = LT.refute (LT.Syn []) (LT.¬G (LT.Syn [])) LT.closed-infer?

-- §4  STAGE 3: LINEARITY.  `IR.compile` is `checkLin` post-composed
-- with `liftPass optimise`; both are terms, so the pass cannot change
-- the usage -- that is the type of `Pass`.

linB : D.⊤G D.⊢ D.Δ Bool
linB = D.okA C.Lin (D.¬G C.Lin) D.∘g C.linear?

noLin : (m : D.Term•) → D.run linB m ≡ false → (D.¬G C.Lin) m
noLin = D.refute C.Lin (D.¬G C.Lin) C.linear?

-- §5  THE CROSSINGS.  Three theories, three exits.

-- strFib → linFib.  The `ScopeRes` split is read here because
-- `unbound` is the ACTION's failure, not the grammar's: the tokens
-- did parse.
crossParse : List Tok → Maybe LT.Raw
crossParse ts = pick (runΔ ScopeRes (¬G Trm) parse ts)
  where pick : Maybe ScopeRes → Maybe LT.Raw
        pick (just (scoped e))  = just e
        pick (just (unbound _)) = nothing
        pick nothing            = nothing

-- linFib → dbFib.  PRIMITIVE (phase 1): `LinTyped`'s `Raw` is
-- annotated and ℕ-indexed, `DB`'s `DBTm` is `Fin`-bounded.
-- `LinLam.Pipeline.stripDB` was the same bridge.
stripAnn : LT.Raw → C.Skel
stripAnn (LT.var i)   = C.svar i
stripAnn (LT.app f a) = C.sapp (stripAnn f) (stripAnn a)
stripAnn (LT.lam b)   = C.slam (stripAnn b)
stripAnn (LT.ann t _) = stripAnn t

fin? : (n i : ℕ) → Maybe (Fin n)
fin? zero    _       = nothing
fin? (suc n) zero    = just fzero
fin? (suc n) (suc i) = mapMb fsuc (fin? n i)

-- the `nothing` branch is unreachable after §2 resolved every name, and
-- is kept distinct from a scope error rather than merged into it.
toDB? : (n : ℕ) → C.Skel → Maybe (D.DBTm n)
toDB? n (C.svar i)   = mapMb D.dvar (fin? n i)
toDB? n (C.sapp f a) with toDB? n f | toDB? n a
... | just u | just v = just (D.dapp u v)
... | _      | _      = nothing
toDB? n (C.slam b)   = mapMb D.dlam (toDB? (suc n) b)

crossType : LT.Raw → Maybe (D.DBTm 0)
crossType e = pick (LT.runΔ LT.Ty (LT.¬G (LT.Syn [])) infer e)
  where pick : Maybe LT.Ty → Maybe (D.DBTm 0)
        pick (just _) = toDB? 0 (stripAnn e)
        pick nothing  = nothing

-- §6  THE FRONT END AS ONE TERM OF `strFib`.
--
-- Only the PARSE boundary needs an exit: a `Link` needs a TOTAL carrier
-- map (`Reindex.FrontEnd` builds one for every other boundary) and
-- parsing is a decision.  So the later stages ride in the payload of a
-- `Δ`, which is a constant family and may therefore hold metalanguage
-- --  and each carries the refutation ITS OWN theory produced, so
-- nothing is downgraded to "it said no".

data StageErr : Type₀ where
  eUnbound : Name → StageErr
  eType    : (e : LT.Raw) → (LT.¬G (LT.Syn [])) e → StageErr
  eRange   : C.Skel → StageErr
  eLin     : (m : D.Term•) → (D.¬G C.Lin) m → StageErr

Err : Gr
Err = ¬G Trm ⊕ Δ StageErr

private
  -- stage 3.  `LinIR` carries `length u Eq.≡ m .fst` and the pipeline
  -- enters at `m .fst = 0`, so the term IS closed and the backend needs
  -- no `crossClosed`: the equation is used here instead of discarded.
  linOf : (t : D.DBTm 0)
        → (LIR.LinIR (0 , t) ⊎ (D.¬G C.Lin) (0 , t)) → StageErr ⊎ L.Tm []
  linOf t (inr k)                = inl (eLin (0 , t) k)
  linOf t (inl ([]        , _ , e)) = inr e
  linOf t (inl ((_ ∷ _) , () , _))

  -- stage 2, on a resolved term
  typeOf : (e : LT.Raw)
         → (LT.Syn [] e ⊎ (LT.¬G (LT.Syn [])) e)
         → StageErr ⊎ D.DBTm 0
  typeOf e (inr k) = inl (eType e k)
  typeOf e (inl _) = pick (toDB? 0 (stripAnn e))
    where pick : Maybe (D.DBTm 0) → StageErr ⊎ D.DBTm 0
          pick (just t) = inr t
          pick nothing  = inl (eRange (stripAnn e))

  -- the three later stages, composed on the payload.  `p` selects the
  -- optimised (`IR.compile`) or plain (`IR.checkLin`) stage 3.
  backOf : (D.⊤G D.⊢ D.Result (D.¬G C.Lin) LIR.LinIR)
         → ScopeRes → StageErr ⊎ L.Tm []
  backOf p (unbound n) = inl (eUnbound n)
  backOf p (scoped e)  = step (typeOf e (LT.closed-infer? e tt))
    where step : StageErr ⊎ D.DBTm 0 → StageErr ⊎ L.Tm []
          step (inl k) = inl k
          step (inr t) = linOf t (p (0 , t) tt)

-- the sum, as a term: a `StageErr` payload goes to the error branch.
sumR : Δ (StageErr ⊎ L.Tm []) ⊢ Result Err (Δ (L.Tm []))
sumR = Δ-E λ { (inl k) → err Err (Δ (L.Tm [])) ∘g ⊕-I₂ ∘g pureA StageErr k
             ; (inr v) → ok  Err (Δ (L.Tm [])) ∘g pureA (L.Tm []) v }

-- `Result` has no error-side map, so widening `¬G Trm` into `Err` goes
-- through the eliminator.  (caseR's argument order: success then error.)
widen : Result (¬G Trm) Trm ⊢ Result Err Trm
widen = caseR (ok Err Trm) (err Err Trm ∘g ⊕-I₁)

-- THE FRONT END.  `frontWith IR.compile` is the optimised chain and
-- `frontWith IR.checkLin` the same without the pass, so a backend test
-- can measure what stage 3 changed.
frontWith : (D.⊤G D.⊢ D.Result (D.¬G C.Lin) LIR.LinIR)
          → ⊤G ⊢ Result Err (Δ (L.Tm []))
frontWith p = joinR Err (Δ (L.Tm []))
      ∘g mapR Err (Result Err (Δ (L.Tm [])))
           (sumR ∘g mapA (backOf p) resolve)
      ∘g widen ∘g parseTrm

front frontRaw : ⊤G ⊢ Result Err (Δ (L.Tm []))
front    = frontWith LIR.compile
frontRaw = frontWith LIR.checkLin
