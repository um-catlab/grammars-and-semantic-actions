{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE SCOPED PARSER, RUN -- and both halves of the claim, as theorems.

  The tape is fixed in `Lambda.Parse`:

      pos     0     1     2     3     4     5     6     7     8
      token   λx.   x     λx.   x     y     λx.   x     λy.   y

  so every test below is the SAME decision procedure at a different span
  of one word.  `run` appears only in the `refl` lines; everything named
  is a term `⊤G ⊢ Δ Bool` or `⊤G ⊢ Deriv P ⊕ ¬G (Deriv P)`.

  WHAT IS BEING DEMONSTRATED.

  (i)   a closed term parses -- and `witness` hands back the parse TREE,
        an inhabitant of `Term []`, which by `Parse.no-free-var` cannot
        mention an unbound name.

  (ii)  a term with a free variable is REFUTED, and `refute` turns the
        `refl` into a theorem `Term [] s → ⊥*`.  This is the half that a
        parser (error grammar `⊤G`) could not supply: it would return
        `tt`.

  (iii) the free variable is RECOVERED, by running the same term at
        different scopes.  `λx. x y` has no closed reading and no reading
        in scope `x`, but does have one in scope `y` -- so the missing
        name is exactly `y`, and all three facts are `refl`.
-}
module TheoryGrammar.Instances.Lambda.ParseTests where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.List using ([]; _∷_)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as E using ()
open import Cubical.Data.Nat
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.FinData.Base renaming (zero to fzero; suc to fsuc)

open import TheoryGrammar.SemanticAction using (passes; _↦_; _at_)
open import TheoryGrammar.Instances.Spans.CYK
open import TheoryGrammar.Instances.Lambda.Parse
open import TheoryGrammar.Instances.Lambda.ParseElab

-- ==================================================================
-- THE LEXICAL LAYER: the binder tokens are non-terminals like any other
-- ==================================================================

_ : passes (run (binder! Nx) at
             ( (0 , 1) ↦ true   -- `λx.`
             ∷ (7 , 1) ↦ false  -- `λy.`
             ∷ (1 , 1) ↦ false  -- `x`
             ∷ [] ))
_ = refl

_ : passes (run (binder! Ny) at ( (7 , 1) ↦ true ∷ (0 , 1) ↦ false ∷ [] ))
_ = refl

-- ==================================================================
-- (i) CLOSED TERMS PARSE.
--
-- `(0,2)` and `(2,2)` and `(5,2)` and `(7,2)` are `λx.x` / `λy.y`;
-- `(5,4)` is the application `(λx.x)(λy.y)`, which is where the chart
-- actually recurses -- deciding it consults both halves at length 2 and
-- also the reading `λx.(x (λy.y))`, whose body sits at length 3.
-- ==================================================================

_ : passes (run (parses! []) at
             ( (0 , 2) ↦ true    -- λx. x
             ∷ (2 , 2) ↦ true    -- λx. x
             ∷ (5 , 2) ↦ true    -- λx. x
             ∷ (7 , 2) ↦ true    -- λy. y
             ∷ (5 , 4) ↦ true    -- (λx.x)(λy.y)
             ∷ [] ))
_ = refl

-- ==================================================================
-- (ii) EVERYTHING THAT IS NOT CLOSED IS REFUTED.
--
-- Three different reasons, all reported the same way:
--   (1,1) `x`     -- a free variable
--   (8,1) `y`     -- a free variable
--   (0,1) `λx.`   -- a binder with no body: not a term at all
--   (2,3) `λx.x y`-- closed prefix, free `y` inside
--   (3,2) `x y`   -- both free
-- ==================================================================

_ : passes (run (parses! []) at
             ( (1 , 1) ↦ false
             ∷ (8 , 1) ↦ false
             ∷ (0 , 1) ↦ false
             ∷ (3 , 2) ↦ false
             ∷ (2 , 3) ↦ false
             ∷ [] ))
_ = refl

-- ==================================================================
-- (iii) THE SCOPE INDEX IS NOT DECORATION: move it, and the answers
-- move with it.  The SAME span is refuted at one scope and derivable at
-- another, which is what "the type carries the scoping discipline"
-- means operationally.
-- ==================================================================

-- `x` is derivable exactly in the scopes containing x
_ : passes (run (parses! (Nx ∷ [])) at ( (1 , 1) ↦ true ∷ (8 , 1) ↦ false ∷ [] ))
_ = refl

_ : passes (run (parses! (Ny ∷ [])) at ( (8 , 1) ↦ true ∷ (1 , 1) ↦ false ∷ [] ))
_ = refl

-- `x y` needs BOTH
_ : passes (run (parses! (Nx ∷ Ny ∷ [])) at ( (3 , 2) ↦ true ∷ [] ))
_ = refl

_ : passes (run (parses! (Nx ∷ [])) at ( (3 , 2) ↦ false ∷ [] ))
_ = refl

-- `λx. x y` -- under EITHER reading (`(λx.x) y` or `λx.(x y)`) the `x`
-- is bound by the λ, so the span needs `y` and ONLY `y`
_ : passes (run (parses! (Ny ∷ [])) at ( (2 , 3) ↦ true  ∷ [] ))
_ = refl

_ : passes (run (parses! (Nx ∷ [])) at ( (2 , 3) ↦ false ∷ [] ))
_ = refl

-- ==================================================================
-- ... AND THE ANSWERS ARE THEOREMS.
--
-- `derives?` is a `Result (¬G _) _`, so a `false` is a REFUTATION and a
-- `true` is a parse tree.  Both are extracted from the `refl`s above by
-- the generic `refute` / `witness`, uniformly in the error grammar.
-- ==================================================================

noParse : (Γ : Scope) (s : Span) → run (parses! Γ) s ≡ false → (¬G (Term Γ)) s
noParse Γ = refute (Term Γ) (¬G (Term Γ)) (parses? Γ)

yesParse : (Γ : Scope) (s : Span) → run (parses! Γ) s ≡ true → Term Γ s
yesParse Γ = witness (Term Γ) (¬G (Term Γ)) (parses? Γ)

-- (i) THE PARSE TREE of `λx. x`, at the empty scope.  Its TYPE is
-- `Term []`; by `Parse.no-free-var` no such tree can contain a variable
-- leaf that the scope does not bind, so "this is a closed term" is not
-- a further check but the type it already has.
idTree : Term [] (0 , 2)
idTree = yesParse [] (0 , 2) refl

appTree : Term [] (5 , 4)
appTree = yesParse [] (5 , 4) refl

-- (ii) THE REFUTATION.  `λx. x y` has NO closed reading -- a proof, not
-- a `false`.
no-closed-λxxy : Term [] (2 , 3) → E.⊥* {ℓ-zero}
no-closed-λxxy = noParse [] (2 , 3) refl

-- a bare variable, and a binder with no body, the same way
no-closed-y : Term [] (8 , 1) → E.⊥* {ℓ-zero}
no-closed-y = noParse [] (8 , 1) refl

no-closed-λx : Term [] (0 , 1) → E.⊥* {ℓ-zero}
no-closed-λx = noParse [] (0 , 1) refl

-- ==================================================================
-- (iii) THE FREE VARIABLE, RECOVERED.
--
-- `FreeIn n s` says: `s` has no closed reading, but adding `n` to the
-- scope gives one.  That IS "n is free in s", stated with the grammar
-- and nothing else, and it is inhabited by two of the `refl`s above.
-- ==================================================================

FreeIn : Nm → Span → Type₀
FreeIn n s = (Term [] s → E.⊥* {ℓ-zero}) × Term (n ∷ []) s

-- `λx. x y` -- the free name is `y`
y-free-in-λxxy : FreeIn Ny (2 , 3)
y-free-in-λxxy = no-closed-λxxy , yesParse (Ny ∷ []) (2 , 3) refl

-- ... and it is `y` and not `x`: opening the scope at `x` instead does
-- not help, which is the second half of "the free variable is `y`".
x-does-not-help : Term (Nx ∷ []) (2 , 3) → E.⊥* {ℓ-zero}
x-does-not-help = noParse (Nx ∷ []) (2 , 3) refl

-- the bare `y` at (8,1), the same way
y-free-in-y : FreeIn Ny (8 , 1)
y-free-in-y = no-closed-y , yesParse (Ny ∷ []) (8 , 1) refl

-- ==================================================================
-- ... AND THE TREE ELABORATES, TOTALLY.
--
-- `elabClosed : Term [] ⊢ Δ (DB 0)` (Lambda.ParseElab) has NO error
-- branch: a closed parse tree yields a closed de Bruijn term because
-- that is its type.  So the `Maybe` below is the PARSER's -- "no closed
-- reading exists" -- and nothing after a successful parse can fail.
-- ==================================================================

-- applied directly to the tree from (i): no `run`, no `Maybe`
_ : elabClosed (0 , 2) idTree .fst ≡ dlam (dvar fzero)
_ = refl

_ : elabClosed (5 , 4) appTree .fst
  ≡ dapp (dlam (dvar fzero)) (dlam (dvar fzero))
_ = refl

-- ... and through the parser, where the only failure is the parse
_ : passes (runΔ (DB 0) (¬G (Term [])) (elab []) at
             ( (0 , 2) ↦ just (dlam (dvar fzero))
             ∷ (7 , 2) ↦ just (dlam (dvar fzero))
             ∷ (5 , 4) ↦ just (dapp (dlam (dvar fzero)) (dlam (dvar fzero)))
             ∷ (2 , 3) ↦ nothing          -- `λx. x y` -- `y` is free
             ∷ (8 , 1) ↦ nothing          -- `y`
             ∷ [] ))
_ = refl

-- At a NON-EMPTY scope the free names become free INDICES.  `(2,3)` is
-- `λx. x y`, and juxtaposition is ambiguous, so the search returns A
-- parse -- here `(λx.x) y`, the first cut of the first rule.  Either
-- reading elaborates at the same type; what is pinned is that the
-- outer `y` is index 0 of the scope `[y]` while the `x` under the
-- binder is index 0 of the EXTENDED scope, which is the whole point of
-- carrying the scope in the index.
_ : passes (runΔ (DB 1) (¬G (Term (Ny ∷ []))) (elab (Ny ∷ [])) at
             ( (2 , 3) ↦ just (dapp (dlam (dvar fzero)) (dvar fzero))
             ∷ (8 , 1) ↦ just (dvar fzero)
             ∷ [] ))
_ = refl
