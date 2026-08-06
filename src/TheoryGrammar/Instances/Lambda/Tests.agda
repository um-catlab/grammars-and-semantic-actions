{-
  The pipeline computes.  Each `refl` holds only if `check`, the generic
  μ's `sup`, `fold` and `toIx` all reduce.

  EVERY NAME BELOW IS A TERM OF THE CALCULUS -- a `⊤G ⊢ Δ Bool` or a
  `⊤G ⊢ Result E (Δ X)` -- and `run` / `runΔ` appear only inside the
  `refl` lines.  That is the point: externalising is the OBSERVATION, not
  part of the pipeline, so a name of type `Raw → Maybe (DB 0)` would
  already have left the calculus one step too early.

  Nothing here defines a reader or a constant grammar; see
  TheoryGrammar.SemanticAction.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Tests where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Unit
open import Cubical.Data.List using ([]; _∷_; length)
open import Cubical.Data.Nat using (ℕ; discreteℕ)
open import Cubical.Data.FinData.Base renaming (zero to fzero; suc to fsuc)

open import TheoryGrammar.SemanticAction using (passes; _↦_; _at_)
open import TheoryGrammar.Instances.Lambda
open import TheoryGrammar.Instances.Lambda.Passes.Decide
open import TheoryGrammar.Instances.Lambda.Initial
open Lambda ℕ discreteℕ
open Decide ℕ discreteℕ
open Initial ℕ using (size!)

idT open' bigger shadow : Raw
idT    = lam 0 (var 0)                                -- λx. x
open'  = lam 0 (var 1)                                -- λx. y
bigger = app (lam 0 (var 0)) (lam 1 (lam 2 (var 1)))  -- (λx.x)(λy.λz.y)
shadow = lam 0 (lam 0 (var 0))                        -- λx. λx. x

-- ==================================================================
-- THE SCOPE CHECKER, and elaboration through it.
--
-- `closed?` is a decision, i.e. a `Result (¬G _) _`.  Composing it with
-- the generic observer `okA` gives a term `⊤G ⊢ Δ Bool`; composing it
-- with `mapR` and the semantic action `toDB` gives a term
-- `⊤G ⊢ Result (¬G _) (Δ (DB 0))` -- a decision whose success branch
-- already carries the elaborated term, and whose failure branch still
-- carries the refutation.  Both are still inside the calculus.
-- ==================================================================

DecCl : TmG
DecCl = ¬G (Scoped [])

closed! : ⊤G ⊢ Δ Bool
closed! = okA (Scoped []) DecCl ∘g closed?

elab : ⊤G ⊢ Result DecCl (Δ (DB 0))
elab = mapR DecCl (Δ (DB 0)) (toDB []) ∘g closed?

-- The cases are batched: `passes (f at (w ↦ v ∷ …))` says every case
-- holds, and one `refl` proves it exactly when each does definitionally.
-- The term under test is then written once, not once per case.

_ : passes (run closed! at ( idT    ↦ true
                           ∷ open'  ↦ false
                           ∷ bigger ↦ true
                           ∷ shadow ↦ true
                           ∷ [] ))
_ = refl

-- ... and the elaborated term itself, not just acceptance

_ : passes (runΔ (DB 0) DecCl elab at
             ( idT    ↦ just (dlam (dvar fzero))
             ∷ shadow ↦ just (dlam (dlam (dvar fzero)))
             ∷ bigger ↦ just (dapp (dlam (dvar fzero))
                                   (dlam (dlam (dvar (fsuc fzero)))))
             ∷ open'  ↦ nothing
             ∷ [] ))
_ = refl

-- ==================================================================
-- EVERY OTHER MAP OUT OF `⊤` IN THIS INSTANCE, the same way.  Each is a
-- `Result` at some error grammar, so `okA` observes acceptance and
-- `mapR` carries a witness -- no matter which SORT the map lives at.
-- ==================================================================

-- ---- `dec-⌈⌉` : the representable at a NAME.  Sort `nm`, so the world
-- ---- this term is run at is a Name, not a Raw.
isName? : (m : ℕ) → ⊤G ⊢ Δ Bool
isName? m = okA (⌈_⌉ {s = nm} m) (¬G (⌈_⌉ {s = nm} m)) ∘g dec-⌈⌉ m

_ : passes (run (isName? 3) at (3 ↦ true ∷ 4 ↦ false ∷ []))
_ = refl

-- ---- `dec-In` : scope membership, decided.  The WITNESS is the de
-- ---- Bruijn index, and `toIxA` is exactly the action that reads it --
-- ---- the same action `toDB` is built from.
inScope? : (Γ : Scope) → ⊤G ⊢ Δ Bool
inScope? Γ = okA (In Γ) (¬G (In Γ)) ∘g dec-In Γ

indexOf : (Γ : Scope) → ⊤G ⊢ Result (¬G (In Γ)) (Δ (Fin (length Γ)))
indexOf Γ = mapR (¬G (In Γ)) (Δ (Fin (length Γ))) (toIxA Γ) ∘g dec-In Γ

_ : passes (run (inScope? (7 ∷ 8 ∷ [])) at (8 ↦ true ∷ 9 ↦ false ∷ []))
_ = refl

_ : passes (run (inScope? []) at (0 ↦ false ∷ []))
_ = refl

_ : passes (runΔ _ _ (indexOf (7 ∷ 8 ∷ [])) at
             ( 7 ↦ just fzero
             ∷ 8 ↦ just (fsuc fzero)
             ∷ 9 ↦ nothing
             ∷ [] ))
_ = refl

-- shadowing: the INNERMOST binding wins, and the index says so
_ : passes (runΔ _ _ (indexOf (7 ∷ 7 ∷ [])) at (7 ↦ just fzero ∷ []))
_ = refl

-- ---- `scoped?` : the scope checker at a NON-EMPTY scope.  `closed?`
-- ---- is this at `[]`; nothing above tested the general case.
scoped! : (Γ : Scope) → ⊤G ⊢ Δ Bool
scoped! Γ = okA (Scoped Γ) (¬G (Scoped Γ)) ∘g scoped? Γ

elabIn : (Γ : Scope) → ⊤G ⊢ Result (¬G (Scoped Γ)) (Δ (DB (length Γ)))
elabIn Γ = mapR (¬G (Scoped Γ)) (Δ (DB (length Γ))) (toDB Γ) ∘g scoped? Γ

_ : passes (run (scoped! []) at ((var 1) ↦ false ∷ []))
_ = refl

-- `open' = λx. y` is not closed, but IS scoped once `y` is in scope
_ : passes (run (scoped! (1 ∷ [])) at
             ( (var 1) ↦ true
             ∷ (var 2) ↦ false
             ∷ open'   ↦ true
             ∷ bigger  ↦ true
             ∷ [] ))
_ = refl

-- ... and elaboration under that scope produces the right index
_ : passes (runΔ _ _ (elabIn (1 ∷ [])) at
             (open' ↦ just (dlam (dvar (fsuc fzero))) ∷ []))
_ = refl

-- ---- `isVar?` : "is this term the variable n?"
isVar! : (n : ℕ) → ⊤G ⊢ Δ Bool
isVar! n = okA (VarG ⌈ n ⌉) (¬G (VarG ⌈ n ⌉)) ∘g isVar? n

_ : passes (run (isVar! 0) at
             ((var 0) ↦ true ∷ (var 1) ↦ false ∷ idT ↦ false ∷ []))
_ = refl

-- ---- `⊗-decSplit` : "is this term built by this operation?"  Unique
-- ---- readability, observed.
isOp! : (o : LOp) → ⊤G ⊢ Δ Bool
isOp! o = okA (⊗ˢ o (λ _ → ⊤G)) (¬G (⊗ˢ o (λ _ → ⊤G))) ∘g ⊗-decSplit o

_ : passes (run (isOp! varOp) at ((var 0) ↦ true  ∷ idT ↦ false ∷ []))
_ = refl

_ : passes (run (isOp! appOp) at
             ((var 0) ↦ false ∷ (app idT idT) ↦ true ∷ []))
_ = refl

_ : passes (run (isOp! lamOp) at
             (idT ↦ true ∷ (app idT idT) ↦ false ∷ []))
_ = refl

-- ---- `readback` : the initial-algebra map, `⊤G ⊢ Everything Γ`.  It
-- ---- cannot fail (shape `Result ⊥G`), so the observation is just a
-- ---- semantic action -- `size!` is `recA` at a `Δ ℕ`-valued algebra,
-- ---- and is itself a term `⊤G ⊢ Δ ℕ` (defined in `Lambda.Initial`).
_ : passes (run (size! []) at
             ( (var 0)           ↦ 1
             ∷ idT               ↦ 2
             ∷ (app idT (var 1)) ↦ 4
             ∷ bigger            ↦ 6
             ∷ [] ))
_ = refl
