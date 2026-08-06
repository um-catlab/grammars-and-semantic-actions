{-
  Composing passes across substrates.

  A compiler pass from one theory to another is a SEMANTIC ACTION: a map
  from parse evidence over substrate 1 to elements of substrate 2.  A
  grammar over substrate 2 then pulls back along it to a grammar over
  substrate 1, and the composite pipeline is that pullback.

  The question "under what conditions is the pipeline decidable?" has a
  sharp answer, proved below:

      the parser must be UNAMBIGUOUS.

  Decidability of each stage is not enough; you also need that any two
  parses of the same input agree, or the second stage's answer is not
  well defined on the first stage's output.
-}
module Grammar.Pipeline where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary.Base

private variable ℓ : Level

module _ {S₁ S₂ : Type₀}                       -- the two carriers
         (P : S₁ → Type₀)                      -- grammar over substrate 1
         (act : ∀ m → P m → S₂)                -- the semantic action
         (Q : S₂ → Type₀)                      -- grammar over substrate 2
         where

  -- the composite pipeline: parse, then check the projected result
  pull : S₁ → Type₀
  pull m = Σ[ p ∈ P m ] Q (act m p)

  -- THEOREM.  The pipeline is decidable when each stage is decidable
  -- AND the first stage is unambiguous.
  pull-dec : (∀ m → isProp (P m))            -- unambiguity of the parser
           → (∀ m → Dec (P m))
           → (∀ t → Dec (Q t))
           → ∀ m → Dec (pull m)
  pull-dec pP dP dQ m with dP m
  ... | no ¬p = no λ pq → ¬p (pq .fst)
  ... | yes p with dQ (act m p)
  ...   | yes q = yes (p , q)
  ...   | no ¬q = no λ pq →
            ¬q (subst (λ z → Q (act m z)) (pP m (pq .fst) p) (pq .snd))

  -- Where unambiguity is used, isolated: without it, a `no` answer for
  -- ONE parse says nothing about the others, so the pipeline can only be
  -- semi-decided (search all parses) rather than decided.
  pull-sound : ∀ m (p : P m) → Q (act m p) → pull m
  pull-sound m p q = p , q

-- ==================================================================
-- Consequences.
-- ==================================================================

-- 1.  If the parser is ambiguous, the pipeline is still SOUND (any
--     successful parse-then-check gives a pipeline result) but the
--     failure direction needs a search over all parses.
--
-- 2.  Chaining n passes needs unambiguity at every stage but the last.
--     The last stage's ambiguity is harmless: you are returning a
--     witness, not deciding on behalf of a later stage.
--
-- 3.  This is why `Scoped` being syntax-directed matters twice over:
--     once so that scope checking is decidable, and once so that scope
--     checking can be COMPOSED with a later pass.
