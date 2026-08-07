{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE PARSE TREE, ELABORATED -- and the payoff of intrinsic scoping.

  The target is `Lambda.DeBruijn.DB`, the SAME nameless representation
  `Lambda.Scoped`'s derivations elaborate into, and the statement is

      elabA Γ : Term Γ ⊢ Δ (DB (length Γ))

  with `elabA [] : Term [] ⊢ Δ (DB 0)`.  READ THE TYPE: there is no
  `Maybe`, no `Result`, no error grammar.  A closed parse tree elaborates
  to a de Bruijn term with ZERO free indices, TOTALLY -- and that is not
  a theorem proved about the elaborator, it is the type it already has,
  because the grammar `Term []` has no rule that could produce an
  unbound occurrence (`Parse.no-free-var`).

  Compare the failure mode this replaces.  A parser that produced an
  untyped AST would have to be followed by `scopeCheck : AST → Maybe
  (DB 0)`, and the `nothing` branch would be an obligation forever after.
  Here the `Maybe` appears exactly once, at the very outside, in `elab`
  -- and it is the PARSER's `Maybe`, i.e. "this span has no closed
  reading at all", carrying a refutation.  Nothing downstream of a
  successful parse can fail.

  `Lambda.DeBruijn` proves the same thing over the AST theory, with
  motive `(Γ , t) ↦ DB (length Γ)`; this is that construction moved onto
  spans, so the two files elaborate into the same `DB` from two
  different substrates and neither needs a `Maybe`.

  PHASE.  `tokIx` and `elabRule` are PRIMITIVES: they are the container
  encoding of the CYK description respelled as an algebra, the exact
  analogue of `Scoped.⟦Sc⟧`, and they are the only pointful code here.
  `elabA` / `elab` are terms.
-}
module TheoryGrammar.Instances.Lambda.ParseElab where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.List using (List; []; _∷_; length)
open import Cubical.Data.FinData.Base using (Fin) renaming (zero to fzero; suc to fsuc)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Instances.Spans.CYK
open import TheoryGrammar.Instances.Lambda.Parse
open import TheoryGrammar.Instances.Lambda.DeBruijn

-- the SAME target `Lambda.Scoped`'s derivations elaborate into
open DeBruijn Nm using (DB; dvar; dapp; dlam) public

-- the description's own `Ind`, at this file's non-terminals.  `Deriv`,
-- `Layer` and `Rule` are already the corresponding notions of `CYK.G`,
-- definitionally.
module Gμ = CYK.G NT unitR BinR

-- ==================================================================
-- THE MOTIVE.  A term non-terminal at scope Γ elaborates to a de Bruijn
-- term with `length Γ` indices; a binder token elaborates to nothing.
-- The scope index of the GRAMMAR becomes the index bound of the TARGET,
-- which is the whole content of "well-scoped by construction".
-- ==================================================================

Mot : Gμ.Ix → Type₀
Mot (trm Γ    , s) = Δ (DB (length Γ)) s
Mot (binder n , s) = ⊤G s

-- PRIMITIVE (phase 1).  A scope-membership witness IS a de Bruijn
-- index: the position is read off the SHAPE of the witness and not
-- recomputed, exactly as `DeBruijn.toIxA` reads it off `In Γ`.  There is
-- no clause at `[]` because `TokIn t [] = ⊥` -- the same fact that makes
-- `Term []` closed makes this function total.
tokIx : (t : Tok) (Γ : Scope) → TokIn t Γ → Fin (length Γ)
tokIx t (n ∷ Γ) (inl _) = fzero
tokIx t (n ∷ Γ) (inr q) = fsuc (tokIx t Γ q)

-- PRIMITIVE (phase 1).  ONE RULE, elaborated.  This is the container
-- encoding respelled -- `⟦_⟧c` is the description in the connectives, so
-- `inl`/`inr` here IS `⊕ᴰ`'s tag, `(c , h)` IS `⊗ˢ`'s splitting and
-- slots, and `h a true` IS `&ᴰ-E true`, i.e. `CYK.derOf`.  Nothing is
-- decided and no span is measured.
--
-- The three interesting lines are the three rules:
--   variable    -- `tokIx` turns the scope witness into the index
--   rApp        -- both slots at the SAME scope, so `dapp` typechecks
--   rLam        -- the body slot is at `n ∷ Γ`, so its elaboration has
--                  `suc (length Γ)` indices and `dlam` binds exactly one
elabRule : (P : NT) (r : Rule P) (s : Span)
         → Gμ.⟦ ruleF P r ⟧c Mot s → Mot (P , s)
elabRule (trm Γ)    (inl _) s (lift (j , _ , v)) =
  dvar (tokIx (tape j) Γ v) , tt
elabRule (binder n) (inl _) s _ = tt
elabRule (trm Γ) (inr (_ , _ , rApp _))   s (c , h) =
  dapp (h true true .fst) (h false true .fst) , tt
elabRule (trm Γ) (inr (_ , _ , rLam _ n)) s (c , h) =
  dlam (h false true .fst) , tt
elabRule (binder n) (inr (_ , _ , ())) s _

-- ... and from here down, nothing matches a rule either.
elabLayer : (P : NT) (s : Span) → Gμ.⟦ CYKF P ⟧c Mot s → Mot (P , s)
elabLayer P s (r , t) = elabRule P r s t

-- ==================================================================
-- THE ELABORATOR, as a SEMANTIC ACTION.
--
-- `Action A X = A ⊢ Δ X` (TheoryGrammar.SemanticAction): a map of the
-- calculus into the discrete grammar on `DB k`, not a function
-- `Deriv → DB k`.  So it composes with the parser by the generic
-- `mapR`, and `runΔ` is the single place anything leaves.
-- ==================================================================

elabA : (Γ : Scope) → Action (Term Γ) (DB (length Γ))
elabA Γ s d = Gμ.fold Mot (λ x m sh rc → elabLayer x m (Gμ.toC (CYKF x) m (sh , rc)))
                     (trm Γ , s) d

-- THE CLAIM, at the empty scope.  `Term [] ⊢ Δ (DB 0)`: a closed parse
-- tree yields a CLOSED de Bruijn term, totally.  If the grammar admitted
-- a free occurrence this type would be uninhabitable, because `Fin 0` is.
elabClosed : Action (Term []) (DB 0)
elabClosed = elabA []

-- ... and the whole pipeline, still inside the calculus: parse-or-refute,
-- then elaborate on the success branch.  The `Maybe` that `runΔ` reads
-- off is the PARSER's, and the refutation survives in the other branch.
elab : (Γ : Scope) → ⊤G ⊢ Result (¬G (Term Γ)) (Δ (DB (length Γ)))
elab Γ = mapR (¬G (Term Γ)) (Δ (DB (length Γ))) (elabA Γ) ∘g parses? Γ
