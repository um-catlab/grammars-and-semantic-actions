{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  STAGE 3 OF THE CHAIN: PARSE TREE -> LOCATED DE BRUIJN TERM.

  This is `Lambda.ParseElab` with the tape as a parameter and ONE
  addition, which is the point of the file: the target carries a SPAN AT
  EVERY NODE.

      data LDB : ℕ → Type₀ where
        lvar : Span → Fin k       → LDB k
        lapp : Span → LDB k → LDB k → LDB k
        llam : Span → LDB (suc k) → LDB k

  `Lambda.ParseElab` elaborates into `DB`, which forgets where the term
  came from.  That is fine for a demonstration and fatal for a compiler:
  every diagnostic a later pass wants to emit is about a piece of SOURCE
  TEXT, and by stage 4 the source text is three theories away.  So the
  elaborator here keeps the span, and `Chain.Pipeline` closes the loop by
  turning a span back into the substring of the original Unicode input
  that produced it.

  THIS IS THE CONCRETE FORM OF A GENERIC CONSTRUCTION.  The general
  statement is that a pass is a map of promodels along a signature
  morphism, and that such a map can be REINDEXED so that its output
  remembers its input's index.  `TheoryGrammar/Reindex/` is where that
  machinery belongs; nothing here imports it, deliberately, because the
  chain must run today.  What `LDB` does by hand is what `Reindex` would
  do by construction, and the seam is exactly the motive:

      Mot (trm Γ , s) = Δ (LDB (length Γ)) s        -- concrete
                        ^^^^^^^^^^^^^^^^^^
                        would be `Δ (DB (length Γ))` reindexed along the
                        span, with the span supplied by the fold rather
                        than written into the constructors

  Read `elabRule` below with that in mind: every clause's `s` is the
  span the fold is already at, and every constructor is `ParseElab`'s
  with `s` in front.  Nothing else changed, which is the evidence that
  the addition is mechanical and therefore automatable.

  ------------------------------------------------------------------
  THE ELABORATION IS STILL TOTAL, AND STILL FOR THE SAME REASON.

      elabA Γ : Term Γ ⊢ Δ (LDB (length Γ))

  No `Maybe`, no error grammar.  A closed parse tree yields a de Bruijn
  term with ZERO free indices because `Term []` has no rule that could
  produce an unbound occurrence (`Lambda.Parse.no-free-var`), so
  `tokIx` -- which has no clause at the empty scope -- is total.  The
  chain therefore has NO scope-checking stage: it was absorbed into the
  parser's non-terminal, and stage 3 is a fold rather than a check.

  PHASE.  `tokIx`, `elabRule` and the two erasures are PRIMITIVES: they
  are the container encoding of the CYK description respelled as an
  algebra.  `elabA` is a term.
-}
open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ; zero; suc)

open import TheoryGrammar.Instances.Lambda.Parse using (Tok; vx; vy; lx; ly)

module Chain.Elab (tape : ℕ → Tok) where

open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.List using (List; []; _∷_; length)
open import Cubical.Data.FinData.Base using (Fin) renaming (zero to fzero; suc to fsuc)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Instances.Spans.CYK
open import Chain.Parse tape public

-- the LINEAR side's de Bruijn carrier -- the erasure below is the
-- bridge from the parsing theory to the linearity-checking theory
import TheoryGrammar.Instances.LinLam.DB as L

-- the description's own `Ind`, at this file's non-terminals
module Gμ = CYK.G NT unitR BinR

-- ==================================================================
-- §1  THE LOCATED TARGET.
--
-- `DB` with a `Span` glued to every constructor.  It is deliberately a
-- new type rather than a pair `DB k × Tree Span`: the span has to sit at
-- each NODE, and the only way to say that without a second traversal is
-- to put it in the constructor.
-- ==================================================================

data LDB : ℕ → Type₀ where
  lvar : ∀ {k} → Span → Fin k                → LDB k
  lapp : ∀ {k} → Span → LDB k     → LDB k    → LDB k
  llam : ∀ {k} → Span → LDB (suc k)          → LDB k

-- the span of a node -- the accessor the backward projection is built
-- from.  PRIMITIVE (phase 1): a projection out of the carrier.
spanOf : {k : ℕ} → LDB k → Span
spanOf (lvar s _)   = s
spanOf (lapp s _ _) = s
spanOf (llam s _)   = s

-- ==================================================================
-- §2  THE TWO ERASURES.
--
-- `stripL` throws the retention data away and lands in the LINEAR
-- theory's `DBTm`.  It is the bridge between two promodels that share a
-- carrier shape but not a signature, and it is a HAND-WRITTEN BRIDGE:
-- see `Chain.Pipeline`'s header, which flags it as such.  `Lin`'s own
-- statement is up to `skel`, so it is precisely this erasure that the
-- linearity checker is checking against.
-- ==================================================================

stripL : {k : ℕ} → LDB k → L.DBTm k
stripL (lvar _ i)   = L.dvar i
stripL (lapp _ u v) = L.dapp (stripL u) (stripL v)
stripL (llam _ b)   = L.dlam (stripL b)

-- ==================================================================
-- §3  THE MOTIVE.  A term non-terminal at scope Γ elaborates to a
-- located de Bruijn term with `length Γ` indices; a binder token
-- elaborates to nothing.  The scope index of the GRAMMAR becomes the
-- index bound of the TARGET.
-- ==================================================================

Mot : Gμ.Ix → Type₀
Mot (trm Γ    , s) = Δ (LDB (length Γ)) s
Mot (binder n , s) = ⊤G s

-- PRIMITIVE (phase 1).  A scope-membership witness IS a de Bruijn
-- index: the position is read off the SHAPE of the witness and not
-- recomputed.  There is no clause at `[]` because `TokIn t [] = ⊥` --
-- the same fact that makes `Term []` closed makes this total.
tokIx : (t : Tok) (Γ : Scope) → TokIn t Γ → Fin (length Γ)
tokIx t (n ∷ Γ) (inl _) = fzero
tokIx t (n ∷ Γ) (inr q) = fsuc (tokIx t Γ q)

-- PRIMITIVE (phase 1).  ONE RULE, elaborated, with its span retained.
-- Compare `Lambda.ParseElab.elabRule`: identical, save that each
-- constructor now takes the `s` the fold is standing at.
elabRule : (P : NT) (r : Rule P) (s : Span)
         → Gμ.⟦ ruleF P r ⟧c Mot s → Mot (P , s)
elabRule (trm Γ)    (inl _) s (lift (j , _ , v)) =
  lvar s (tokIx (tape j) Γ v) , tt
elabRule (binder n) (inl _) s _ = tt
elabRule (trm Γ) (inr (_ , _ , rApp _))   s (c , h) =
  lapp s (h true true .fst) (h false true .fst) , tt
elabRule (trm Γ) (inr (_ , _ , rLam _ n)) s (c , h) =
  llam s (h false true .fst) , tt
elabRule (binder n) (inr (_ , _ , ())) s _

elabLayer : (P : NT) (s : Span) → Gμ.⟦ CYKF P ⟧c Mot s → Mot (P , s)
elabLayer P s (r , t) = elabRule P r s t

-- ==================================================================
-- §4  THE ELABORATOR, as a SEMANTIC ACTION.
-- ==================================================================

elabA : (Γ : Scope) → Action (Term Γ) (LDB (length Γ))
elabA Γ s d = Gμ.fold Mot (λ x m sh rc → elabLayer x m (Gμ.toC (CYKF x) m (sh , rc)))
                      (trm Γ , s) d

-- THE CLAIM, at the empty scope: a closed parse tree yields a CLOSED
-- located de Bruijn term, totally.
elabClosed : Action (Term []) (LDB 0)
elabClosed = elabA []

-- ... and the whole of stages 2+3, still inside the calculus:
-- parse-or-refute, then elaborate on the success branch.  The only
-- failure is the PARSE, and it carries a refutation.
elab : (Γ : Scope) → ⊤G ⊢ Result (¬G (Term Γ)) (Δ (LDB (length Γ)))
elab Γ = mapR (¬G (Term Γ)) (Δ (LDB (length Γ))) (elabA Γ) ∘g parses? Γ
