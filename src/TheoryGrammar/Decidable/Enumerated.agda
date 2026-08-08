{- Decidability through a tensor, the OTHER way. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Decidable.Enumerated where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Bool
open import Cubical.Data.Unit
open import Cubical.Data.List
open import Cubical.Data.Empty using (⊥*)

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Rules
open import TheoryGrammar.RulesFib
open import TheoryGrammar.Enumerable
open import TheoryGrammar.Par
open import TheoryGrammar.Decidable.Additive
open import TheoryGrammar.Decidable.Tensor

private variable ℓS ℓ ℓ' ℓX ℓP ℓA ℓB ℓM : Level

module DecEnum {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
               (Fib : Fibered σ ℓX ℓP) where

  open DecFib Fib public

  -- the tensor restricted to ONE splitting.  `⊗ˢ o A m` is `Σ` of this
  -- over the splittings, definitionally.
  ⊗at : (o : σ .ops) (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
        (m : Fib .carrier (σ .resultSort o)) → Fib .Split o m → Type (ℓ-max ℓ' ℓA)
  ⊗at o A m sp = (a : σ .arities o) → A a (Fib .parts o m sp a)

  Refutes : (o : σ .ops) (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
            (m : Fib .carrier (σ .resultSort o)) → Fib .Split o m → Type (ℓ-max ℓ' ℓA)
  Refutes o A m sp = ⊗at o A m sp → ⊥* {ℓ-zero}

  -- THE TENSOR, DECIDED FROM A DECISION AT EACH SPLITTING.

  -- The short circuit itself, ONCE. "A slot refuted refutes the whole
  -- splitting": the hypothesis is a TERM `A a ⊢ B`, and the conclusion is
  -- a refutation at the splitting.
  slotMiss : (o : σ .ops) (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
             (m : Fib .carrier (σ .resultSort o)) (sp : Fib .Split o m)
             (a : σ .arities o) (B : TheoryTy ℓB (σ .sortOf o a))
           → A a ⊢ B
           → (¬G B) (Fib .parts o m sp a) → Refutes o A m sp
  slotMiss o A m sp a B f k h = k (f _ (h a))

  dec-⊗-cuts : (o : σ .ops) (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
               (m : Fib .carrier (σ .resultSort o))
               (sps : List (Fib .Split o m)) → ((sp : Fib .Split o m) → sp ∈L sps)
             → ((sp : Fib .Split o m) → ⊗at o A m sp ⊎ Refutes o A m sp)
             → Dec⟨ ⊗ˢ o A ⟩ m
  dec-⊗-cuts o A m sps complete d = decΣ sps complete d

  -- every splitting in a list is refuted
  AllNo : (o : σ .ops) (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
          (m : Fib .carrier (σ .resultSort o))
        → List (Fib .Split o m) → Type (ℓ-max ℓ' ℓA)
  AllNo o A m []         = Unit*
  AllNo o A m (sp ∷ sps) = Refutes o A m sp × AllNo o A m sps

  -- ... so any splitting IN the list is refuted
  lookupNo : (o : σ .ops) (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
             (m : Fib .carrier (σ .resultSort o))
             (sps : List (Fib .Split o m)) (sp : Fib .Split o m)
           → sp ∈L sps → AllNo o A m sps → Refutes o A m sp
  lookupNo o A m (sp ∷ sps) .sp here      (k , _) = k
  lookupNo o A m (_  ∷ sps) sp  (there p) (_ , r) = lookupNo o A m sps sp p r

-- The hypothesis.

record DecEnumerable {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
                     (Fib : Fibered σ ℓX ℓP) ℓA
  : Type (ℓ-max ℓS (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓX (ℓ-max ℓP (ℓ-suc ℓA)))))) where
  open DecEnum Fib
  field
    -- the splittings of any `m` are finitely many ...
    enumSplit    : (o : σ .ops) (m : Fib .carrier (σ .resultSort o))
                 → List (Fib .Split o m)
    -- ... and the list misses none.  THIS is what turns "no listed
    -- splitting works" into a refutation of the tensor.
    enumComplete : (o : σ .ops) (m : Fib .carrier (σ .resultSort o))
                   (sp : Fib .Split o m) → sp ∈L enumSplit o m
    -- and slotwise decisions combine AT one splitting.  A plain `⊎`,
    -- because the index is fixed -- the same concession `dec-⊗` makes,
    -- and for the same reason: `⊕-E` eliminates uniformly in the index.
    decAt        : (o : σ .ops)
                   (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
                   (m : Fib .carrier (σ .resultSort o)) (sp : Fib .Split o m)
                 → ((a : σ .arities o) → Dec⟨ A a ⟩ (Fib .parts o m sp a))
                 → ⊗at o A m sp ⊎ Refutes o A m sp

open DecEnumerable public

-- The tensor rule.

module DecTensorEnum {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
                     {Fib : Fibered σ ℓX ℓP} (DE : DecEnumerable Fib ℓA) where

  open DecEnum Fib public

  module _ (o : σ .ops)
           (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
           (m : Fib .carrier (σ .resultSort o))
           (d : (sp : Fib .Split o m) (a : σ .arities o)
              → Dec⟨ A a ⟩ (Fib .parts o m sp a)) where

    private
      -- walk the enumeration: a witness, or a refutation of every entry
      search : (sps : List (Fib .Split o m))
             → (Σ[ sp ∈ Fib .Split o m ] ⊗at o A m sp) ⊎ AllNo o A m sps
      search []         = inr tt*
      search (sp ∷ sps) = step (DE .decAt o A m sp (d sp))
        where
          step : ⊗at o A m sp ⊎ Refutes o A m sp
               → (Σ[ q ∈ Fib .Split o m ] ⊗at o A m q) ⊎ AllNo o A m (sp ∷ sps)
          step (inl h) = inl (sp , h)
          step (inr k) = more (search sps)
            where more : (Σ[ q ∈ Fib .Split o m ] ⊗at o A m q) ⊎ AllNo o A m sps
                       → (Σ[ q ∈ Fib .Split o m ] ⊗at o A m q)
                         ⊎ AllNo o A m (sp ∷ sps)
                  more (inl y) = inl y
                  more (inr r) = inr (k , r)

      finish : (Σ[ sp ∈ Fib .Split o m ] ⊗at o A m sp)
               ⊎ AllNo o A m (DE .enumSplit o m)
             → Dec⟨ ⊗ˢ o A ⟩ m
      finish (inl (sp , h)) = dec-yes (⊗ˢ o A) m (sp , h)
      finish (inr all)      = dec-no  (⊗ˢ o A) m
        λ x → lookupNo o A m (DE .enumSplit o m) (x .fst)
                       (DE .enumComplete o m (x .fst)) all (x .snd)

    dec-⊗-enum : Dec⟨ ⊗ˢ o A ⟩ m
    dec-⊗-enum = finish (search (DE .enumSplit o m))

-- The pure core: decide a Σ over a listable index.  Both `dec-⊗-enum`
-- (Σ over splittings) and `dec-⊕ᴰ` (Σ over the tag type) are instances,
-- because `⊗ˢ o A m` and `⊕ᴰ Y A m` are both Σs.

-- The enumeration is a WITNESS for the internal statement, not the
-- statement.

module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
         {Fib : Fibered σ ℓX ℓP} (DE : DecEnumerable Fib ℓA) where

  open ParS Fib using (⊗-EM)
  open DecTensorEnum DE

  enum→⊗EM : (o : σ .ops)
             (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
           → ((m : Fib .carrier (σ .resultSort o)) (sp : Fib .Split o m)
              (a : σ .arities o) → Dec⟨ A a ⟩ (Fib .parts o m sp a))
           → ⊗-EM o A
  enum→⊗EM o A d m _ = dec-⊗-enum o A m (d m)
