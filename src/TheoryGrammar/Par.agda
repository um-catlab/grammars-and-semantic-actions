{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The product over decompositions -- AUW's `G` -- and the currying law
   that lets enumerability be stated internally.

   NOT the linear-logic par.  The LL par is DISJUNCTIVE,
   `∀ (u,v). uv=w → (A u ⊎ B v)`, and it is not associative
   intuitionistically, because `⊎` does not commute with `∀`:
   `(∀i. P i) ⊎ Q` does not follow from `∀i. (P i ⊎ Q)`.  What is
   defined here is the CONJUNCTIVE product, `∀ (sp). ∏ slots`, which has
   no `⊎` in it at all. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Par where

open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥*)

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Rules
open import TheoryGrammar.RulesFib

private variable ℓS ℓ ℓ' ℓX ℓP ℓA : Level

module ParS {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (Fib : Fibered σ ℓX ℓP) where

  open RulesF Fib public

  private variable s : S

  -- internal negation
  ¬G_ : TheoryTy ℓA s → TheoryTy ℓA s
  ¬G A = A ⇒ ⊥G

  infix 32 ¬G_

  -- The product over decompositions, where ⊗ is the sum.  AUW's `G` at
  -- an arbitrary theory; needs no hypotheses.  See the header for why
  -- this is not called `⅋`.
  Allˢ : (o : σ .ops)
     → ((a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
     → TheoryTy (ℓ-max ℓP (ℓ-max ℓ' ℓA)) (σ .resultSort o)
  Allˢ o A m = (sp : Fib .Split o m)
           → ((a : σ .arities o) → A a (Fib .parts o m sp a))

  module _ (o : σ .ops)
           (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a)) where

    -- the slotwise refutation at one decomposition
    Miss : TheoryTy (ℓ-max ℓP (ℓ-max ℓ' ℓA)) (σ .resultSort o)
    Miss m = (sp : Fib .Split o m)
           → ((a : σ .arities o) → A a (Fib .parts o m sp a)) → ⊥* {ℓ-zero}

    -- ================================================================
    -- Refuting a tensor is a PRODUCT of refutations, one per
    -- decomposition.  No hypotheses; both round trips `refl`.
    --
    -- This is currying, `(Σ x, B x) → C ≅ (x : _) → B x → C`, NOT the
    -- classical De Morgan `¬(A ⊗ B) = ¬A ⅋ ¬B` -- that would need the
    -- disjunctive par and is intuitionistically false.  `Miss` is
    -- `∀sp. ¬(P × Q)`, never `∀sp. (¬P ⊎ ¬Q)`.
    -- ================================================================

    ¬⊗-curry : (m : Fib .carrier (σ .resultSort o)) → Iso ((¬G (⊗ˢ o A)) m) (Miss m)
    ¬⊗-curry m .Iso.fun f sp h = f (sp , h)
    ¬⊗-curry m .Iso.inv g (sp , h) = g sp h
    ¬⊗-curry m .Iso.sec _ = refl
    ¬⊗-curry m .Iso.ret _ = refl

  -- ================================================================
  -- ENUMERABILITY, STATED INTERNALLY.  Note this does NOT depend on the
  -- product above being well behaved: the refuting side is
  -- `∀sp. ¬(∏ slots)`, which is fine whatever happens to associativity.
  --
  -- The list-and-completeness formulation is external: a metalanguage
  -- `List` and a metalanguage membership proof.  But by `deMorgan⊗`,
  -- what a refutation of `⊗` IS, is a product of refutations -- and THAT
  -- needs no finiteness.  Finiteness is not what the statement says; it
  -- is one way to CONSTRUCT the refuting side.
  --
  -- So the internal content of "the splittings are enumerable" is
  -- excluded middle for the multiplicative:
  --
  --     ⊤ ⊢ (⊗ˢ o A) ⊕ ¬G (⊗ˢ o A)
  --          witness      product of refutations
  --
  -- i.e. ⊗ and ⅋ are complementary.  A `List` with a completeness proof
  -- is one witness for this; `splitProp` (unique readability) is
  -- another; a derivative law is a third.  None of them is the
  -- statement.
  -- ================================================================

  ⊗-EM : (o : σ .ops)
       → ((a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
       → Type (ℓ-max ℓX (ℓ-max ℓP (ℓ-max ℓ' ℓA)))
  ⊗-EM o A = ⊤G ⊢ ((⊗ˢ o A) ⊕ (¬G (⊗ˢ o A)))

  -- the same, with the refuting side displayed as the product
  ⊗-EM' : (o : σ .ops)
        → ((a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
        → Type (ℓ-max ℓX (ℓ-max ℓP (ℓ-max ℓ' ℓA)))
  ⊗-EM' o A = ⊤G ⊢ ((⊗ˢ o A) ⊕ Miss o A)

  -- the two are interchangeable, by De Morgan
  EM→EM' : (o : σ .ops) (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
         → ⊗-EM o A → ⊗-EM' o A
  EM→EM' o A e m t = shift (e m t)
    where shift : ((⊗ˢ o A) ⊕ (¬G (⊗ˢ o A))) m → ((⊗ˢ o A) ⊕ Miss o A) m
          shift (inl x) = inl x
          shift (inr k) = inr (¬⊗-curry o A m .Iso.fun k)

  EM'→EM : (o : σ .ops) (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
         → ⊗-EM' o A → ⊗-EM o A
  EM'→EM o A e m t = shift (e m t)
    where shift : ((⊗ˢ o A) ⊕ Miss o A) m → ((⊗ˢ o A) ⊕ (¬G (⊗ˢ o A))) m
          shift (inl x) = inl x
          shift (inr g) = inr (¬⊗-curry o A m .Iso.inv g)
