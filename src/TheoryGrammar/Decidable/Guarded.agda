{-
  THE MISSING RULE: consuming a `▷` INSIDE a tensor.

  `Graded.Guard.löb` is stated over `Ix`-families, and `Guard` gives no
  combinators at that level -- no `&`, no `⊕ᴰ`, no `Dec⟨_⟩`, no intro or
  elim.  So the moment a program uses `▷`, the only thing it can do with
  it is apply it at a point, and that pointfulness propagates upward
  through the whole step: every intermediate definition becomes an
  ELEMENT `X m` rather than a map `A ⊢ B`.  That is what happened to
  both CYKs, and the fix is here.

  Two things are needed and both are in this file.

  (1) `▷ᴬ`, the later at the level of GRAMMARS.  A "chart" is a family
      over the sorts, `M : (s : S) → TheoryTy ℓM s`, and

          ▷ᴬ M  :  TheoryTy _ s

      is again a grammar -- "M at every strictly smaller world".  So
      `▷ᴬ M ⊢ M s` is a map OF THE CALCULUS, and `löbᵍ` turns one into a
      cover `⊤G ⊢ M s`.  Nothing about this is new mathematics; it is
      `Guard`'s `▷`/`löb` with the nonterminal index removed, which is
      exactly what makes the result a grammar.

  (2) `dec-⊗▷`, the rule.  Deciding `⊗ˢ o A` needs the slot deciders AT
      THE SLOTS, and a guarded recursion has them only at strictly
      smaller worlds -- which is what the slots of a PROPER splitting
      are.  So the slot decider is a map `M (sortOf o a) ⊢ Dec⟨ A a ⟩`,
      the chart is available LATER, and the conclusion is

          ▷ᴬ M  ⊢  Dec⟨ ⊗ˢ o A ⟩

      a term.  This is the generic analogue of `Grammar/Later/Properties`'s

          ▷-app-NE : ⟨¬Nullable B⟩ → (B ⊗ ⊤) & ▷ A ⊢ B ⊗ A

      and it is what `Instances.Strings.CYK` used to have a FIXME about.

  WHAT STAYS POINTFUL, AND WHY IT MUST.  `dec-⊗▷` takes one hypothesis
  that is not a `⊢`:

      resource : (m) (sp) → ((a) → Proper o m sp a) ⊎ Refutes o A m sp

  "at this cut, either every slot is a proper part, or the cut is
  refuted".  It is indexed by a SPLITTING, and `TheoryTy` is a family
  over the CARRIER, so no grammar states it -- the same structural fact
  that makes the cut scan itself external.  It is one named obligation
  per instance and it is the ONLY one; everything downstream composes.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Decidable.Guarded where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.List
open import Cubical.Induction.WellFounded

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Graded
open import TheoryGrammar.Enumerable
open import TheoryGrammar.Decidable.Enumerated

private variable ℓS ℓ ℓ' ℓX ℓP ℓA ℓM : Level

module DecGuard {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
                (GS : GradedFib σ ℓX ℓP) where

  private
    Fib : Fibered σ ℓX ℓP
    Fib = GS .fib

  open DecEnum Fib public

  -- ================================================================
  -- (1)  THE LATER, AT THE LEVEL OF GRAMMARS.
  -- ================================================================

  -- a CHART is a grammar at every sort at once
  SortFam : (ℓM : Level) → Type (ℓ-max ℓS (ℓ-max ℓX (ℓ-suc ℓM)))
  SortFam ℓM = (s : S) → TheoryTy ℓM s

  -- ... and its later is again a grammar
  ▷ᴬ : SortFam ℓM → {s : S} → TheoryTy (ℓ-max ℓS (ℓ-max ℓX ℓM)) s
  ▷ᴬ M {s} m = (s' : S) (m' : Fib .carrier s')
             → GS .deg s' m' < GS .deg s m → M s' m'

  -- the later is functorial, and forgetting to a smaller chart is a map
  ▷ᴬ-map : {M : SortFam ℓM} {N : SortFam ℓM} {s : S}
         → ((s' : S) → M s' ⊢ N s') → ▷ᴬ M {s} ⊢ ▷ᴬ N {s}
  ▷ᴬ-map f m r s' m' q = f s' m' (r s' m' q)

  -- ================================================================
  -- LÖB, at the level of grammars.  The step is a TERM `▷ᴬ M ⊢ M s`,
  -- never an Agda function on an index -- which is the discipline
  -- `Grammar/Parser/RecursiveDescent.fixP` sets and which the
  -- `Ix`-level `Guard.löb` cannot enforce, since `Ix` is not a sort.
  -- ================================================================

  private
    descend : (M : SortFam ℓM) (st : (s : S) → ▷ᴬ M {s} ⊢ M s)
              (n : ℕ) → Acc _<_ n
            → (s : S) (m : Fib .carrier s) → GS .deg s m ≡ n → M s m
    descend M st n (acc h) s m p =
      st s m λ s' m' q →
        descend M st (GS .deg s' m')
                (h (GS .deg s' m') (subst (GS .deg s' m' <_) p q))
                s' m' refl

  löbᵍ : (M : SortFam ℓM) → ((s : S) → ▷ᴬ M {s} ⊢ M s)
       → (s : S) → ⊤G {s} ⊢ M s
  löbᵍ M st s m _ = descend M st (GS .deg s m) (<-wellfounded _) s m refl

  -- ================================================================
  -- (2)  THE RULE.
  -- ================================================================

  module _ (o : σ .ops)
           (A : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a))
           (M : SortFam ℓM)
           -- the cut space, as for `dec-⊗-cuts`
           (sps : (m : Fib .carrier (σ .resultSort o))
                → List (Fib .Split o m))
           (complete : (m : Fib .carrier (σ .resultSort o))
                       (sp : Fib .Split o m) → sp ∈L sps m)
           -- THE ONE NON-`⊢` HYPOTHESIS.  See the header.
           (resource : (m : Fib .carrier (σ .resultSort o))
                       (sp : Fib .Split o m)
                     → ((a : σ .arities o) → GS .Proper o m sp a)
                     ⊎ Refutes o A m sp)
           -- slotwise decisions combine at ONE cut (arity finiteness)
           (atCut : (m : Fib .carrier (σ .resultSort o))
                    (sp : Fib .Split o m)
                  → ((a : σ .arities o) → Dec⟨ A a ⟩ (Fib .parts o m sp a))
                  → ⊗at o A m sp ⊎ Refutes o A m sp)
           -- and the slot decider: a MAP, out of the chart at that slot
           (d : (a : σ .arities o) → M (σ .sortOf o a) ⊢ Dec⟨ A a ⟩)
           where

    dec-⊗▷ : ▷ᴬ M {σ .resultSort o} ⊢ Dec⟨ ⊗ˢ o A ⟩
    dec-⊗▷ m later =
      dec-⊗-cuts o A m (sps m) (complete m) cut
      where
        -- at a cut whose slots are all proper, every slot is strictly
        -- smaller (`deg<`), so `later` supplies the chart there and the
        -- slot decider `d` is applied to it.  That is the whole content
        -- of "the recursive call is legal at a proper part".
        use : (sp : Fib .Split o m)
            → ((a : σ .arities o) → GS .Proper o m sp a)
            → ⊗at o A m sp ⊎ Refutes o A m sp
        use sp pr = atCut m sp λ a →
          d a (Fib .parts o m sp a)
              (later _ (Fib .parts o m sp a) (GS .deg< o m sp a (pr a)))

        cut : (sp : Fib .Split o m) → ⊗at o A m sp ⊎ Refutes o A m sp
        cut sp = go (resource m sp)
          where go : _ → ⊗at o A m sp ⊎ Refutes o A m sp
                go (inl pr) = use sp pr
                go (inr k)  = inr k
