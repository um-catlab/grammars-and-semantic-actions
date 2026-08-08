{- THE COMBINATOR LAYER over a `Fibered`: intro and elim for EVERY
   connective, in one place, so instances compose rather than re-derive. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.RulesFib where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥*)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Rules
open import TheoryGrammar.Result

private variable ℓS ℓ ℓ' ℓX ℓP ℓA ℓB ℓC ℓY : Level

module RulesF {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (Fib : Fibered σ ℓX ℓP) where

  -- the connectives, and the additive rules, inherited
  open FibNotation Fib public
  open RulesCarrier (Fib .carrier) public
    hiding (Liftg; liftg; lowerg)
    -- (the Model-level ⊗ rules are simply absent now: RulesCarrier has
    -- none; the three hidden names are RE-EXPORTED below, specialised to
    -- the level a description's constant former actually uses)

  -- a private handle on the same module, for the specialisations below
  private module C = RulesCarrier (Fib .carrier)

  private variable s : S

  -- Composition.

  idg : {A : TheoryTy ℓA s} → A ⊢ A
  idg _ x = x

  _∘g_ : {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} {C : TheoryTy ℓC s}
       → B ⊢ C → A ⊢ B → A ⊢ C
  (g ∘g f) m x = g m (f m x)

  infixr 9 _∘g_

  -- ⊗ˢ  --  intro and elim at the SUBSTRATE's splittings.

  module _ (o : σ .ops)
           {A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a)} where

    -- intro: a splitting, plus a payload at every slot
    ⊗ˢ-I : (m : Fib .carrier (σ .resultSort o)) (sp : Fib .Split o m)
         → ((a : σ .arities o) → A a (Fib .parts o m sp a))
         → ⊗ˢ o A m
    ⊗ˢ-I m sp h = sp , h

    ⊗ˢ-E : {B : TheoryTy ℓB (σ .resultSort o)}
         → MultiHomˢ o A B → ⊗ˢ o A ⊢ B
    ⊗ˢ-E {B = B} = uncurryˢ o {A = A} {B = B}

    -- (⊗ˢ-UP, the β/η package, comes from FibNotation already)

    -- functorial action, slotwise
    ⊗ˢ-map : {B : (a : σ .arities o) → TheoryTy ℓB (σ .sortOf o a)}
           → ((a : σ .arities o) → A a ⊢ B a) → ⊗ˢ o A ⊢ ⊗ˢ o B
    ⊗ˢ-map f m (sp , h) = sp , λ a → f a _ (h a)

  -- A `⊕ᴰ` AT EVERY SLOT DISTRIBUTES OUT.  `⊗ˢ` is a Σ over the
  -- splitting and a Π over the arity, and Π distributes over Σ, so the
  -- slots' tags come out as ONE function of the arity.  Both directions
  -- are `refl`.  Instances that branch on a subterm inside a tensor slot
  -- were each proving a binary special case of this.
  module _ (o : σ .ops) (Y : σ .arities o → Type ℓY)
           (P : (a : σ .arities o) → Y a → TheoryTy ℓA (σ .sortOf o a)) where

    ⊗ˢ-⊕ᴰ-out : ⊗ˢ o (λ a → ⊕ᴰ (Y a) (P a))
              ⊢ ⊕ᴰ ((a : σ .arities o) → Y a) (λ f → ⊗ˢ o (λ a → P a (f a)))
    ⊗ˢ-⊕ᴰ-out m (sp , h) = (λ a → h a .fst) , sp , λ a → h a .snd

    ⊗ˢ-⊕ᴰ-in : ⊕ᴰ ((a : σ .arities o) → Y a) (λ f → ⊗ˢ o (λ a → P a (f a)))
             ⊢ ⊗ˢ o (λ a → ⊕ᴰ (Y a) (P a))
    ⊗ˢ-⊕ᴰ-in m (f , sp , h) = sp , λ a → f a , h a

  -- Derived connectives, so instances never reach for Agda's.

  -- The option type is `Result` at the error grammar `⊤G`, and every other
  -- parser shape is `Result` at a different one -- so it is DEFINED in
  -- `TheoryGrammar.Result` (additively; it never mentioned the operations)
  -- and only re-exported here, where instances look.
  open Res (Fib .carrier) public
    using (Result; ok; err; caseR; caseR-at; bindR; mapR; mapE; joinR; catchR;
           orElseR; altR; altList; altList-⊕ᴰ; bothR;
           MaybeG; just-I; nothing-I; MaybeG-E;
           orElseM; altM; altListM; maybe-⊕ᴰ; runCover; toMaybe)

  -- the empty and singleton branches of a decomposition, as a grammar:
  -- `⊕ᴰ` over the carrier is how you say "for some element".
  Some : (Y : Type ℓY) → (Y → TheoryTy ℓA s) → TheoryTy (ℓ-max ℓY ℓA) s
  Some = ⊕ᴰ

  -- Liftg AT THE DESCRIPTION'S OWN LEVEL. `RulesCarrier.Liftg` takes the
  -- lift level explicitly, because a bare carrier gives no reason to
  -- prefer one.

  Liftg : TheoryTy ℓA s → TheoryTy (ℓ-max ℓA (ℓ-max ℓ' ℓP)) s
  Liftg = C.Liftg (ℓ-max ℓ' ℓP)

  liftg : {A : TheoryTy ℓA s} → A ⊢ Liftg A
  liftg = C.liftg

  lowerg : {A : TheoryTy ℓA s} → Liftg A ⊢ A
  lowerg = C.lowerg

  -- Sanity: the additive rules really are available here.

  private
    _ : {A : TheoryTy ℓA s} → A ⊢ ⊤G
    _ = ⊤-I

    _ : {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} {C : TheoryTy ℓC s}
      → A ⊢ C → B ⊢ C → (A ⊕ B) ⊢ C
    _ = ⊕-E

    _ : {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} {C : TheoryTy ℓC s}
      → A ⊢ B → A ⊢ C → A ⊢ (B & C)
    _ = &-I
