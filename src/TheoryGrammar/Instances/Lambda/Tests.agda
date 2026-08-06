{-
  The pipeline computes.  Each `refl` holds only if `check`, the generic
  μ's `sup`, `fold` and `toIx` all reduce.

  The tests are stated internally too: a decision is OBSERVED with `⊕-E`
  into a constant grammar, never by matching a `Dec`.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Tests where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Unit
open import Cubical.Data.List using ([])
open import Cubical.Data.Nat using (ℕ; discreteℕ)
open import Cubical.Data.FinData.Base renaming (zero to fzero; suc to fsuc)

open import TheoryGrammar.Instances.Lambda
open Lambda ℕ discreteℕ

idT open' bigger shadow : Raw
idT    = lam 0 (var 0)                                -- λx. x
open'  = lam 0 (var 1)                                -- λx. y
bigger = app (lam 0 (var 0)) (lam 1 (lam 2 (var 1)))  -- (λx.x)(λy.λz.y)
shadow = lam 0 (lam 0 (var 0))                        -- λx. λx. x

closed! : ⊤G ⊢ (λ _ → Bool)
closed! = ⊕-E {A = Scoped []} {C = λ _ → Bool} {B = ¬G (Scoped [])}
              (λ _ _ → true) (λ _ _ → false) ∘g closed?

_ : closed! idT    tt ≡ true
_ = refl

_ : closed! open'  tt ≡ false
_ = refl

_ : closed! bigger tt ≡ true
_ = refl

_ : closed! shadow tt ≡ true
_ = refl

-- `Maybe` spelled internally: the target is `DBG ⊕ ⊤G`, and the two
-- branches are `⊕-I₁ ∘ toDB` and `⊕-I₂ ∘ ⊤-I`.  The whole pipeline is
-- one composite morphism.
DBG : TmG
DBG _ = DB 0

elab : ⊤G ⊢ (DBG ⊕ ⊤G)
elab = ⊕-E (⊕-I₁ ∘g toDB []) (⊕-I₂ ∘g ⊤-I) ∘g closed?

some : (t : Raw) → DB 0 → (DBG ⊕ ⊤G) t
some = ⊕-I₁ {A = DBG} {B = ⊤G}

none : (t : Raw) → (DBG ⊕ ⊤G) t
none t = ⊕-I₂ {B = ⊤G} {A = DBG} t tt

_ : elab idT tt ≡ some idT (dlam (dvar fzero))
_ = refl

_ : elab shadow tt ≡ some shadow (dlam (dlam (dvar fzero)))
_ = refl

_ : elab bigger tt
      ≡ some bigger (dapp (dlam (dvar fzero))
                          (dlam (dlam (dvar (fsuc fzero)))))
_ = refl

_ : elab open' tt ≡ none open'
_ = refl
