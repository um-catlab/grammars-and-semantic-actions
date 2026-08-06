{-
  The pipeline computes.  Each `refl` holds only if `typecheck`, the
  generic μ's `sup`/`fold`, `dec-⌈⌉ᵗ` (which is `dec-⊗` at the `ty`
  sort) and `dec-Look` all reduce.

  The tests are stated internally: a decision is OBSERVED with `⊕-E`
  into a constant grammar, never by matching a `Dec`, and the
  synthesised type is read out with `⊕ᴰ-E`.

  The mode discipline shows up as a pair of tests on the SAME term:
  `lam 0 (var 0)` does not synthesise, and does check at `base ⇒ base`.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.SimplyTyped.Tests where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.List using ([])
open import Cubical.Data.Nat using (ℕ; discreteℕ)
open import Cubical.Data.Unit

open import TheoryGrammar.Instances.SimplyTyped
open SimplyTyped ℕ discreteℕ

-- ==================================================================
-- Terms.  With no constants at `base`, every closed term is built from
-- annotated lambdas -- which is exactly the point of `ann`.
-- ==================================================================

o : Ty
o = base

idAnn                                     : Raw
idAnn = ann (lam 0 (var 0)) (o ⇒ᵗ o)                  -- (λx. x) : o → o

idHi : Raw
idHi = ann (lam 0 (var 0)) ((o ⇒ᵗ o) ⇒ᵗ (o ⇒ᵗ o))     -- (λx. x) : (o→o)→(o→o)

kAnn : Raw
kAnn = ann (lam 0 (lam 1 (var 0))) (o ⇒ᵗ (o ⇒ᵗ o))    -- K : o → o → o

selfApp : Raw
selfApp = app idHi idAnn                              -- well typed, gives o → o

bare : Raw
bare = lam 0 (var 0)                                  -- NOT annotated

badArg : Raw
badArg = app idAnn idAnn                              -- o expected, o→o given

badAnn : Raw
badAnn = ann (lam 0 (var 0)) o                        -- a lambda at a base type

freeVar : Raw
freeVar = var 0                                       -- unbound

shadow : Raw
shadow = ann (lam 0 (lam 0 (var 0))) (o ⇒ᵗ (o ⇒ᵗ o))  -- λx. λx. x

-- ==================================================================
-- The two observations, internally.
-- ==================================================================

infers! : ⊤G ⊢ (λ _ → Bool)
infers! = ⊕-E {A = Syn []} {C = λ _ → Bool} {B = ¬G (Syn [])}
              (λ _ _ → true) (λ _ _ → false)
          ∘g closed-infer?

checks! : (C : Ty) → ⊤G ⊢ (λ _ → Bool)
checks! C = ⊕-E {A = Check [] C} {C = λ _ → Bool} {B = ¬G (Check [] C)}
                (λ _ _ → true) (λ _ _ → false)
            ∘g closed-check? C

-- the synthesised type itself, read out of the ⊕ᴰ with its own rule
synth : ⊤G ⊢ ((λ _ → Ty) ⊕ ⊤G)
synth = ⊕-E (⊕-I₁ ∘g ⊕ᴰ-E (λ A _ _ → A)) (⊕-I₂ ∘g ⊤-I) ∘g closed-infer?

some : (t : Raw) → Ty → ((λ _ → Ty) ⊕ ⊤G) t
some = ⊕-I₁ {A = λ _ → Ty} {B = ⊤G}

none : (t : Raw) → ((λ _ → Ty) ⊕ ⊤G) t
none t = ⊕-I₂ {B = ⊤G} {A = λ _ → Ty} t tt

-- ==================================================================
-- Synthesis.
-- ==================================================================

_ : infers! idAnn   tt ≡ true
_ = refl

_ : infers! kAnn    tt ≡ true
_ = refl

_ : infers! selfApp tt ≡ true
_ = refl

_ : infers! shadow  tt ≡ true
_ = refl

-- MODE DISCIPLINE: a bare lambda synthesises nothing ...
_ : infers! bare tt ≡ false
_ = refl

-- ... but checks at the right type, and only at the right type
_ : checks! (o ⇒ᵗ o) bare tt ≡ true
_ = refl

_ : checks! o bare tt ≡ false
_ = refl

_ : checks! ((o ⇒ᵗ o) ⇒ᵗ o) bare tt ≡ false
_ = refl

-- ==================================================================
-- Rejection: well scoped, ill typed.
-- ==================================================================

_ : infers! badArg  tt ≡ false
_ = refl

_ : infers! badAnn  tt ≡ false
_ = refl

_ : infers! freeVar tt ≡ false
_ = refl

-- checking mode agrees
_ : checks! (o ⇒ᵗ o) badArg tt ≡ false
_ = refl

_ : checks! (o ⇒ᵗ o) selfApp tt ≡ true
_ = refl

-- the switch rule really does compare types
_ : checks! o selfApp tt ≡ false
_ = refl

-- ==================================================================
-- The synthesised types are the expected ones.
-- ==================================================================

_ : synth idAnn tt ≡ some idAnn (o ⇒ᵗ o)
_ = refl

_ : synth kAnn tt ≡ some kAnn (o ⇒ᵗ (o ⇒ᵗ o))
_ = refl

_ : synth selfApp tt ≡ some selfApp (o ⇒ᵗ o)
_ = refl

_ : synth bare tt ≡ none bare
_ = refl

_ : synth badArg tt ≡ none badArg
_ = refl
