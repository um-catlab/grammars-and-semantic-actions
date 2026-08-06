{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The par: the product over decompositions (AUW's `G`), the De Morgan
   dual of `⊗`.  Refuting a tensor IS a par of refutations, and that
   holds unconditionally -- which is what lets enumerability be stated
   internally, as excluded middle for the multiplicative. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Par where

open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥*)

open import TheoryGrammar.Base
open import TheoryGrammar.Substrate
open import TheoryGrammar.Rules
open import TheoryGrammar.RulesSub

private variable ℓS ℓ ℓ' ℓX ℓP ℓA : Level

module ParS {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (Sub : Substrate σ ℓX ℓP) where

  open RulesS Sub public

  private variable s : S

  -- internal negation
  ¬G_ : TheoryTy ℓA s → TheoryTy ℓA s
  ¬G A = A ⇒ ⊥G

  infix 32 ¬G_

  -- THE PAR: a product over decompositions where ⊗ is a sum.  This is
  -- AUW's `G` at an arbitrary theory, and it needs no hypotheses.
  ⅋ˢ : (o : σ .ops)
     → ((a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
     → TheoryTy (ℓ-max ℓP (ℓ-max ℓ' ℓA)) (σ .resultSort o)
  ⅋ˢ o A m = (sp : Sub .Split o m)
           → ((a : σ .arities o) → A a (Sub .parts o m sp a))

  module _ (o : σ .ops)
           (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a)) where

    -- the slotwise refutation at one decomposition
    Miss : TheoryTy (ℓ-max ℓP (ℓ-max ℓ' ℓA)) (σ .resultSort o)
    Miss m = (sp : Sub .Split o m)
           → ((a : σ .arities o) → A a (Sub .parts o m sp a)) → ⊥* {ℓ-zero}

    -- ================================================================
    -- DE MORGAN.  Refuting a tensor IS a par of refutations.  No
    -- hypotheses, and both round trips are `refl` -- it is currying,
    -- `(Σ x, B x) → C  ≅  (x : _) → B x → C`.
    -- ================================================================

    deMorgan⊗ : (m : Sub .carrier (σ .resultSort o)) → Iso ((¬G (⊗ˢ o A)) m) (Miss m)
    deMorgan⊗ m .Iso.fun f sp h = f (sp , h)
    deMorgan⊗ m .Iso.inv g (sp , h) = g sp h
    deMorgan⊗ m .Iso.sec _ = refl
    deMorgan⊗ m .Iso.ret _ = refl

  -- ================================================================
  -- ENUMERABILITY, STATED INTERNALLY.
  --
  -- The list-and-completeness formulation is external: a metalanguage
  -- `List` and a metalanguage membership proof.  But by `deMorgan⊗`,
  -- what a refutation of `⊗` IS, is a par of refutations -- and THAT
  -- needs no finiteness.  Finiteness is not what the statement says; it
  -- is one way to CONSTRUCT the refuting side.
  --
  -- So the internal content of "the splittings are enumerable" is
  -- excluded middle for the multiplicative:
  --
  --     ⊤ ⊢ (⊗ˢ o A) ⊕ ¬G (⊗ˢ o A)
  --          witness      par of refutations
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

  -- and the same statement with the refuting side displayed as a par
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
          shift (inr k) = inr (deMorgan⊗ o A m .Iso.fun k)

  EM'→EM : (o : σ .ops) (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
         → ⊗-EM' o A → ⊗-EM o A
  EM'→EM o A e m t = shift (e m t)
    where shift : ((⊗ˢ o A) ⊕ Miss o A) m → ((⊗ˢ o A) ⊕ (¬G (⊗ˢ o A))) m
          shift (inl x) = inl x
          shift (inr g) = inr (deMorgan⊗ o A m .Iso.inv g)
