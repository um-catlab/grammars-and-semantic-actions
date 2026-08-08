{- Decidability through a tensor. Needs a `Fibered`. -}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Decidable.Tensor where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool; true; false)
import Cubical.Data.Bool.Properties as B
open import Cubical.Data.Unit

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib
open import TheoryGrammar.SemanticAction
open import TheoryGrammar.Precision using (module Prec)
open import TheoryGrammar.Decidable.Additive
open import TheoryGrammar.Decidable.Listable

private variable ℓS ℓ ℓ' ℓX ℓP ℓA ℓB ℓC ℓY : Level

-- `Bool`'s own dependent eliminator, under the name it earns here:
-- assemble a two-slot family from its two slots.

decSlotsBool : {P : Bool → Type ℓA} → P true → P false → (b : Bool) → P b
decSlotsBool = B.elim

module DecFib {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
              (Fib : Fibered σ ℓX ℓP) where

  -- The connectives and the additive rules come from `RulesFib`; from
  -- `Decidable.Additive` only the decision layer is taken, so nothing is
  -- defined twice.
  open RulesF Fib public
  -- ... and the semantic actions, which are how a decision gets
  -- OBSERVED: `accepts?` / `runResult` are uniform in the error
  -- grammar, so they read a `Dec⟨_⟩` and a `MaybeG` alike
  open ActFib Fib public
  open DecAdd (Fib .carrier) public
    using (¬G_; Dec⟨_⟩; dec-yes; dec-no;
           ⊕-E-at; ⊕-E-atᴰ; ⊕-E-at-factors; dec-elim; dec-elimᴰ;
           Complement; Decision; decide; exclude;
           ¬G-excludes; largest; toDec; decDefault;
           &-swap; contra; dist&; ¬G-map; deMorgan;
           dec-map; dec-⊕; dec-&; dec-⊤; dec-⊥; ¬G¬G-I; dni; dec-¬)
  -- ... and the INDEXED additives, whose decision needs the tag type to be
  -- listable.
  open DecList (Fib .carrier) public using (dec-⊕ᴰ; dec-&ᴰ)

  -- The internal half, with NO hypotheses: a term that is not an
  -- o-composite at all carries no o-tensor, whatever the slots say.

  module _ (o : σ .ops)
           (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a)) where

    -- THE SLOT-FORGETTING MAP, named once. `⊗ˢ o ⊤` is the image of o
    -- (`Domain.DomainOf.Imgˢ`), and this is the map onto it: keep the
    -- splitting, throw the payload away.
    ⊗-erase : ⊗ˢ o A ⊢ ⊗ˢ o (λ _ → ⊤G)
    ⊗-erase = ⊗ˢ-map o {A = A} {B = λ _ → ⊤G} (λ _ → ⊤-I)

    ⊗-miss : ¬G (⊗ˢ o (λ _ → ⊤G)) ⊢ ¬G (⊗ˢ o A)
    ⊗-miss = ¬G-map ⊗-erase

    -- the same, one level up: `⊗-erase` forgets the payload, this one only
    -- forgets that the payload was DECIDED -- decided slots still map to
    -- plain ones, so a refutation of the decided tensor refutes the plain
    -- one.
    ⊗-thin : ¬G (⊗ˢ o (λ a → Dec⟨ A a ⟩)) ⊢ ¬G (⊗ˢ o A)
    ⊗-thin = ¬G-map (⊗ˢ-map o {A = A} {B = λ a → Dec⟨ A a ⟩}
                             (λ a → dec-yes (A a)))

  -- The half that needs a hypothesis, and precisely why.

  -- Derived from uniqueness alone. The hypothesis is `Precision`'s
  -- `SplitProp`, named once there alongside the weaker uniqueness notions
  -- (`PartsProp`, `SlotDet`) it is compared against.
  module UniqueSplit (splitProp : Prec.SplitProp Fib) where

    ⊗-refute : (o : σ .ops) (i : σ .arities o)
               (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
               (m : Fib .carrier (σ .resultSort o)) (sp : Fib .Split o m)
             → (¬G (A i)) (Fib .parts o m sp i) → (¬G (⊗ˢ o A)) m
    ⊗-refute o i A m sp k x =
      k (subst (λ z → A i (Fib .parts o m z i))
               (splitProp o m (x .fst) sp) (x .snd i))

    -- The positive twin of `⊗-refute`, from the same hypothesis: two
    -- o-views of the same `m` ARE the same view, so their payloads combine
    -- slotwise.
    ⊗-merge : (o : σ .ops)
              (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
              (B : (a : σ .arities o) → TheoryTy ℓB (σ .sortOf o a))
            → (⊗ˢ o A & ⊗ˢ o B) ⊢ ⊗ˢ o (λ a → A a & B a)
    ⊗-merge o A B m (x , y) =
      x .fst , λ a → x .snd a
                   , subst (λ z → B a (Fib .parts o m z a))
                           (splitProp o m (y .fst) (x .fst)) (y .snd a)

    -- Merge two tensors at the same operation and eliminate, in one step:
    -- `⊗-merge` followed by the tensor's own elimination rule.
    merge2 : (o : σ .ops)
             (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
             (B : (a : σ .arities o) → TheoryTy ℓB (σ .sortOf o a))
             (C : TheoryTy ℓC (σ .resultSort o))
           → MultiHomˢ o (λ a → A a & B a) C
           → (⊗ˢ o A & ⊗ˢ o B) ⊢ C
    merge2 o A B C body =
      ⊗ˢ-E o {A = λ a → A a & B a} {B = C} body ∘g ⊗-merge o A B

    -- `decSlots` for the two arity shapes a syntax signature ever has.

    module _ (o : σ .ops)
             (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
             (m : Fib .carrier (σ .resultSort o)) (sp : Fib .Split o m) where

      private
        Slot : σ .arities o → Type ℓA
        Slot a = A a (Fib .parts o m sp a)

      decSlots¹ : (i : σ .arities o)
                → (Slot i → (a : σ .arities o) → Slot a)
                → Dec⟨ A i ⟩ (Fib .parts o m sp i)
                → Dec⟨ ⊗ˢ o A ⟩ m
      decSlots¹ i mk =
        dec-elim (A i) (Fib .parts o m sp i)
                 (λ x → dec-yes (⊗ˢ o A) m (sp , mk x))
                 (λ k → dec-no  (⊗ˢ o A) m (⊗-refute o i A m sp k))

      decSlots² : (i j : σ .arities o)
                → (Slot i → Slot j → (a : σ .arities o) → Slot a)
                → Dec⟨ A i ⟩ (Fib .parts o m sp i)
                → Dec⟨ A j ⟩ (Fib .parts o m sp j)
                → Dec⟨ ⊗ˢ o A ⟩ m
      decSlots² i j mk di dj =
        dec-elim (A i) (Fib .parts o m sp i)
                 (λ x → decSlots¹ j (mk x) dj)
                 (λ k → dec-no (⊗ˢ o A) m (⊗-refute o i A m sp k))
                 di

  -- DEPRECATED NAME, kept so that nothing downstream has to move at once.
  module Precise (splitProp : Prec.SplitProp Fib) = UniqueSplit splitProp

record DecReadable {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
                   (Fib : Fibered σ ℓX ℓP) ℓA
  : Type (ℓ-max ℓS (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓX (ℓ-max ℓP (ℓ-suc ℓA)))))) where
  open DecFib Fib
  field
    -- at most one splitting: unique readability (`Precision.SplitProp`)
    splitProp : Prec.SplitProp Fib
    -- and it is decidable whether there is one, internally
    decSplit  : (o : σ .ops) → ⊤G ⊢ Dec⟨ ⊗ˢ o (λ _ → ⊤G) ⟩
    -- slotwise decisions combine.  This is where finiteness of the
    -- arity is used, and it is why the field cannot be dropped.
    decSlots  : (o : σ .ops)
                (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
                (m : Fib .carrier (σ .resultSort o)) (sp : Fib .Split o m)
              → ((a : σ .arities o) → Dec⟨ A a ⟩ (Fib .parts o m sp a))
              → Dec⟨ ⊗ˢ o A ⟩ m

open DecReadable public

-- Given all that, the tensor rule for decisions.

module DecTensor {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
                 {Fib : Fibered σ ℓX ℓP} (DR : DecReadable Fib ℓA) where

  open DecFib Fib public
  open UniqueSplit (DR .splitProp) public

  dec-⊗ : (o : σ .ops)
          (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
          (m : Fib .carrier (σ .resultSort o))
        → ((sp : Fib .Split o m) (a : σ .arities o)
           → Dec⟨ A a ⟩ (Fib .parts o m sp a))
        → Dec⟨ ⊗ˢ o A ⟩ m
  -- This consumes a decision at a FIXED index rather than by `⊕-E`: `⊕-E`
  -- eliminates uniformly in the index, and `d` supplies decisions only for
  -- splittings of THIS `m`, so no uniform motive exists -- not even the
  -- constant one, since its branches still quantify over the index.
  dec-⊗ o A m d =
    dec-elim (⊗ˢ o (λ _ → ⊤G)) m
             (λ x → DR .decSlots o A m (x .fst) (d (x .fst)))
             (λ k → dec-no (⊗ˢ o A) m (⊗-miss o A m k))
             (DR .decSplit o m tt)
