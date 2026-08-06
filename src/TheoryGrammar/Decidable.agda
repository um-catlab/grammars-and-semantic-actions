{-
  DECIDABILITY, INTERNALLY -- and generic in the theory.

  A decision is not a metalanguage `Dec`.  It is a MAP OF THE CALCULUS

      ⊤ ⊢ A ⊕ A'

  together with the reason the two halves exclude each other,

      (A & A') ⊢ ⊥

  -- without which `⊕-I₂ ∘ ⊤-I` would "decide" everything at A' = ⊤.
  `A'` need not be `¬G A = A ⇒ ⊥`: any grammar disjoint from `A` will do,
  and a sharper complement carries more information (the difference
  between "not derivable" and "the token at this position is wrong").
  `¬G A` is proved below to be the LARGEST complement -- every other one
  factors through it (`largest`) -- so normalising a decision to the
  default `Dec⟨ A ⟩ = A ⊕ ¬G A` loses nothing, and `toDec` does it.

  The file splits along exactly the line the calculus does.

    §1  ADDITIVE -- needs only a `Model`.  Negation, decisions, the
        distributivity of `&` over `⊕`, de Morgan, and closure of
        decidability under `⊕`, `&`, `⊤`, `⊥`, `⇒` and `⊕ᴰ`/`&ᴰ` at a
        decidable index.  Every proof is a composite of `Rules`'
        intro/elim; there is no `⊎`, no `Dec`, no `yes`/`no`, and not one
        case split on a sum.

    §2  MULTIPLICATIVE -- needs a `Substrate`, plus the hypothesis that
        it is DECIDABLY UNIQUELY READABLE (`DecReadable`).  The half of
        the tensor rule that is purely internal is the refutation:

            ¬(m is an o-node)  ⟹  ¬(m carries an o-tensor)

        which is contravariance of `¬G` along the functorial action that
        forgets every slot -- one line, no hypotheses at all.  The other
        half genuinely needs a side condition, and `DecReadable` is
        exactly it; see the comment there for why it cannot be derived.

  Instances supply a `DecReadable` and get `dec-⊗` and everything in §1
  for free.  See `TheoryGrammar.Instances.Lambda`.
-}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Decidable where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥*)

open import TheoryGrammar.Base
open import TheoryGrammar.Substrate
open import TheoryGrammar.Rules
open import TheoryGrammar.RulesSub

private variable ℓS ℓ ℓ' ℓX ℓP ℓA ℓB ℓC ℓY : Level

-- ==================================================================
-- 1.  THE ADDITIVE THEORY OF DECISIONS.  Only a `Model` is needed --
--     none of this ever mentions the operations.
-- ==================================================================

module DecAdd {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (M : Model σ ℓX) where

  open Notation M public
  open Rules M public

  private variable
    s : S
    A : TheoryTy ℓA s
    B : TheoryTy ℓB s
    C : TheoryTy ℓC s

  -- internal negation
  ¬G_ : TheoryTy ℓA s → TheoryTy ℓA s
  ¬G A = A ⇒ ⊥G

  infix 32 ¬G_

  -- the default complement: internal negation
  Dec⟨_⟩ : TheoryTy ℓA s → TheoryTy ℓA s
  Dec⟨ A ⟩ = A ⊕ ¬G A

  -- The introduction rules, with the grammar NAMED.  Naming it is not
  -- optional: `Dec⟨ A ⟩` unfolds to `A ⊕ ¬G A`, and a grammar-valued
  -- implicit cannot be recovered from `?A m ⊎ ?B m` once `m` is already
  -- in the metavariable's context.
  dec-yes : (A : TheoryTy ℓA s) → A ⊢ Dec⟨ A ⟩
  dec-yes A = ⊕-I₁ {A = A} {B = ¬G A}

  dec-no : (A : TheoryTy ℓA s) → ¬G A ⊢ Dec⟨ A ⟩
  dec-no A = ⊕-I₂ {B = ¬G A} {A = A}

  -- ================================================================
  -- The additive lemmas the decision combinators are built from.
  -- ================================================================

  &-swap : (A & B) ⊢ (B & A)
  &-swap = &-I &-E₂ &-E₁

  -- ex falso: a grammar and its negation are jointly empty
  contra : (A & ¬G A) ⊢ ⊥G
  contra {A = A} = ⇒-app ∘⊢ &-swap

  -- `&` distributes over `⊕`.  `⊕-E` under a `⇒`, then uncurry: proved
  -- from intro/elim alone, with no case split on the sum.
  dist& : ((A ⊕ B) & C) ⊢ ((A & C) ⊕ (B & C))
  dist& = Iso.inv ⇒-UP (⊕-E (⇒-I ⊕-I₁) (⇒-I ⊕-I₂))

  -- contravariance of negation
  ¬G-map : B ⊢ A → ¬G A ⊢ ¬G B
  ¬G-map g = ⇒-I (contra ∘⊢ &-I (g ∘⊢ &-E₂) &-E₁)

  -- de Morgan, the constructive direction: what refuting a sum needs
  deMorgan : (A : TheoryTy ℓA s) (B : TheoryTy ℓB s)
           → (¬G A & ¬G B) ⊢ ¬G (A ⊕ B)
  deMorgan A B =
    ⇒-I (⊕-E (contra ∘⊢ &-I &-E₁ (&-E₁ ∘⊢ &-E₂))
             (contra ∘⊢ &-I &-E₁ (&-E₂ ∘⊢ &-E₂))
         ∘⊢ (dist& ∘⊢ &-swap))

  -- ================================================================
  -- COMPLEMENTS.  A decision is only informative if its two halves
  -- exclude each other -- without that, `⊕-I₂ ∘⊢ ⊤-I` "decides" every
  -- A at A' = ⊤G and says nothing at all.  So a decision carries the
  -- exclusion, and `¬G A` is characterised as the LARGEST complement:
  -- every other one factors through it, which is why nothing is lost by
  -- normalising to `Dec⟨ A ⟩`.
  -- ================================================================

  Complement : TheoryTy ℓA s → TheoryTy ℓB s → Type (ℓ-max ℓX (ℓ-max ℓA ℓB))
  Complement A A' = (A & A') ⊢ ⊥G

  record Decision (A : TheoryTy ℓA s) (A' : TheoryTy ℓB s)
    : Type (ℓ-max ℓX (ℓ-max ℓA ℓB)) where
    field
      decide  : ⊤G ⊢ (A ⊕ A')
      exclude : Complement A A'

  open Decision public

  -- `¬G A` is a complement ...
  ¬G-excludes : (A : TheoryTy ℓA s) → Complement A (¬G A)
  ¬G-excludes A = contra {A = A}

  -- ... and the largest one: any complement embeds into it
  largest : {A : TheoryTy ℓA s} {A' : TheoryTy ℓB s}
          → Complement A A' → A' ⊢ ¬G A
  largest d = ⇒-I (d ∘⊢ &-swap)

  -- so every decision, at whatever complement, yields the default one
  toDec : {A : TheoryTy ℓA s} {A' : TheoryTy ℓB s}
        → Decision A A' → ⊤G ⊢ Dec⟨ A ⟩
  toDec {A = A} D = ⊕-E (dec-yes A) (dec-no A ∘⊢ largest (D .exclude)) ∘⊢ D .decide

  -- and the default one is a decision
  decDefault : (A : TheoryTy ℓA s) → ⊤G ⊢ Dec⟨ A ⟩ → Decision A (¬G A)
  decDefault A f .decide  = f
  decDefault A f .exclude = ¬G-excludes A

  -- ================================================================
  -- Closure properties of decidability.
  -- ================================================================

  -- along an internal logical equivalence
  dec-map : (A : TheoryTy ℓA s) (B : TheoryTy ℓB s)
          → A ⊢ B → B ⊢ A → Dec⟨ A ⟩ ⊢ Dec⟨ B ⟩
  dec-map A B f g = ⊕-E (dec-yes B ∘⊢ f) (dec-no B ∘⊢ ¬G-map g)

  -- under `⊕`: two distributions and a de Morgan
  dec-⊕ : (A : TheoryTy ℓA s) (B : TheoryTy ℓB s)
        → (Dec⟨ A ⟩ & Dec⟨ B ⟩) ⊢ Dec⟨ A ⊕ B ⟩
  dec-⊕ A B =
    ⊕-E (dec-yes (A ⊕ B) ∘⊢ (⊕-I₁ ∘⊢ &-E₁))
        (⊕-E (dec-yes (A ⊕ B) ∘⊢ (⊕-I₂ ∘⊢ &-E₁))
             (dec-no (A ⊕ B) ∘⊢ (deMorgan A B ∘⊢ &-swap))
         ∘⊢ (dist& ∘⊢ &-swap))
    ∘⊢ dist&

  -- under `&`
  dec-& : (A : TheoryTy ℓA s) (B : TheoryTy ℓB s)
        → (Dec⟨ A ⟩ & Dec⟨ B ⟩) ⊢ Dec⟨ A & B ⟩
  dec-& A B =
    ⊕-E (⊕-E (dec-yes (A & B) ∘⊢ &-swap)
             (dec-no (A & B) ∘⊢ (¬G-map &-E₂ ∘⊢ &-E₁))
         ∘⊢ (dist& ∘⊢ &-swap))
        (dec-no (A & B) ∘⊢ (¬G-map &-E₁ ∘⊢ &-E₁))
    ∘⊢ dist&

  -- the units decide themselves
  dec-⊤ : ⊤G {s} ⊢ Dec⟨ ⊤G {s} ⟩
  dec-⊤ = dec-yes ⊤G

  dec-⊥ : ⊤G {s} ⊢ Dec⟨ ⊥G {s} ⟩
  dec-⊥ = dec-no ⊥G ∘⊢ ⇒-I &-E₂

-- ==================================================================
-- 2.  THE MULTIPLICATIVE SIDE.
-- ==================================================================

module DecSub {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
              (Sub : Substrate σ ℓX ℓP) where

  -- the connectives and the additive rules come from `RulesSub`; only
  -- the decision layer is taken from §1, so nothing is defined twice
  open RulesS Sub public
  open DecAdd ⌊ Sub ⌋ public
    using (¬G_; Dec⟨_⟩; dec-yes; dec-no;
           Complement; Decision; decide; exclude;
           ¬G-excludes; largest; toDec; decDefault;
           &-swap; contra; dist&; ¬G-map; deMorgan;
           dec-map; dec-⊕; dec-&; dec-⊤; dec-⊥)

  -- ----------------------------------------------------------------
  -- The internal half, with NO hypotheses: a term that is not an
  -- o-composite at all carries no o-tensor, whatever the slots say.
  -- This is just `¬G` applied to the functorial action that forgets
  -- every slot -- the tensor's own map, from `RulesSub`.
  -- ----------------------------------------------------------------

  module _ (o : σ .ops)
           (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a)) where

    ⊗-miss : ¬G (⊗ˢ o (λ _ → ⊤G)) ⊢ ¬G (⊗ˢ o A)
    ⊗-miss = ¬G-map (⊗ˢ-map o {A = A} {B = λ _ → ⊤G} (λ _ → ⊤-I))

    -- the same, one level up: decided slots still forget to `⊤`
    ⊗-thin : ¬G (⊗ˢ o (λ a → Dec⟨ A a ⟩)) ⊢ ¬G (⊗ˢ o A)
    ⊗-thin = ¬G-map (⊗ˢ-map o {A = A} {B = λ a → Dec⟨ A a ⟩}
                             (λ a → dec-yes (A a)))

  -- ----------------------------------------------------------------
  -- The half that needs a hypothesis, and precisely why.
  --
  -- To decide `⊗ˢ o A` at `m` one must eliminate a sum sitting at a
  -- SLOT (index `parts o m sp a`) and land at the WHOLE (index `m`).
  -- The internal `⊕-E` preserves the index, so it cannot do that on its
  -- own; the connective that moves between a slot and the whole is the
  -- residual `⊸ᶠ`, and even with it the combination over all slots
  -- needs the arity to be finite.  For an infinite arity the statement
  -- is simply false.  So it is a hypothesis on the substrate:
  --
  --   splitProp  -- there is at most one o-splitting of any m
  --   decSplit   -- and it is decidable whether there is one
  --   decSlots   -- and the arity supports combining slotwise decisions
  --
  -- `splitProp` is what makes a refutation at ONE slot refute the whole
  -- tensor (`⊗-refute`), because any competing splitting IS the one you
  -- refuted.  It is unique readability, and for a syntax substrate it
  -- holds by construction.
  -- ----------------------------------------------------------------

  -- derived from uniqueness alone
  module Precise (splitProp : (o : σ .ops) (m : Sub .carrier (σ .resultSort o))
                              (p q : Sub .Split o m) → p ≡ q) where

    ⊗-refute : (o : σ .ops) (i : σ .arities o)
               (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
               (m : Sub .carrier (σ .resultSort o)) (sp : Sub .Split o m)
             → (¬G (A i)) (Sub .parts o m sp i) → (¬G (⊗ˢ o A)) m
    ⊗-refute o i A m sp k x =
      k (subst (λ z → A i (Sub .parts o m z i))
               (splitProp o m (x .fst) sp) (x .snd i))

record DecReadable {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
                   (Sub : Substrate σ ℓX ℓP) ℓA
  : Type (ℓ-max ℓS (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓX (ℓ-max ℓP (ℓ-suc ℓA)))))) where
  open DecSub Sub
  field
    -- at most one splitting: unique readability
    splitProp : (o : σ .ops) (m : Sub .carrier (σ .resultSort o))
                (p q : Sub .Split o m) → p ≡ q
    -- and it is decidable whether there is one, internally
    decSplit  : (o : σ .ops) → ⊤G ⊢ Dec⟨ ⊗ˢ o (λ _ → ⊤G) ⟩
    -- slotwise decisions combine.  This is where finiteness of the
    -- arity is used, and it is why the field cannot be dropped.
    decSlots  : (o : σ .ops)
                (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
                (m : Sub .carrier (σ .resultSort o)) (sp : Sub .Split o m)
              → ((a : σ .arities o) → Dec⟨ A a ⟩ (Sub .parts o m sp a))
              → Dec⟨ ⊗ˢ o A ⟩ m

open DecReadable public

-- ==================================================================
-- Given all that, the tensor rule for decisions.
-- ==================================================================

module DecTensor {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
                 {Sub : Substrate σ ℓX ℓP} (DR : DecReadable Sub ℓA) where

  open DecSub Sub public
  open Precise (DR .splitProp) public

  dec-⊗ : (o : σ .ops)
          (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
          (m : Sub .carrier (σ .resultSort o))
        → ((sp : Sub .Split o m) (a : σ .arities o)
           → Dec⟨ A a ⟩ (Sub .parts o m sp a))
        → Dec⟨ ⊗ˢ o A ⟩ m
  -- THE ONE PLACE the generic layer consumes a decision at a FIXED
  -- index rather than by `⊕-E`.  `⊕-E` eliminates uniformly in the
  -- index, and `d` supplies decisions only for splittings of THIS `m`,
  -- so no uniform motive exists -- not even the constant one, since its
  -- branches still quantify over the index.  The connective that moves
  -- between a slot and the whole is the residual `⊸ᶠ`, and the deciders
  -- being available only at the parts is what `▷` (TheoryGrammar.Graded)
  -- internalises; rebuilding this on `Guard.löb` is what would remove
  -- the match.  Confined to these three lines, once, for all instances.
  dec-⊗ o A m d with DR .decSplit o m tt
  ... | inl x = DR .decSlots o A m (x .fst) (d (x .fst))
  ... | inr k = dec-no (⊗ˢ o A) m (⊗-miss o A m k)
