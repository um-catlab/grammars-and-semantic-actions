{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- CHOMSKY NORMAL FORM AS A DESCRIPTION, ARITY-INDEXED. -}
module TheoryGrammar.ChomskyNormal where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Grading
open import TheoryGrammar.RulesFib
open import TheoryGrammar.Automaton using (module Guard)

private variable ℓ : Level

module CNF {σ : SortedSig Unit ℓ ℓ-zero} (GS : GradedFib σ ℓ-zero ℓ-zero) where

  open RulesF (GS .fib) public

  module Desc (o : σ .ops)                       -- the composition
              (V : Type₀)                        -- the non-terminals
              (Tok : Type₀)                      -- the terminals ...
              (atom : Tok → TheoryTy ℓ-zero tt)  -- ... and their grammars
              (NonTrivial : TheoryTy ℓ-zero tt)  -- the resource certificate
              (unitR : V → Tok → Type₀)          -- P → c
              (binR  : V → ((a : σ .arities o) → V) → Type₀)
              where

    module G = Guard GS ℓ-zero V (λ _ → tt)

    Rule : V → Type₀
    Rule P = (Σ[ c ∈ Tok ] unitR P c)
           ⊎ (Σ[ Qs ∈ ((a : σ .arities o) → V) ] binR P Qs)

    -- a recursive occurrence together with a proof its part is proper;
    -- CNF's ban on epsilon-productions is what supplies the second
    NEslot : V → Bool → G.Functor tt
    NEslot Q true  = G.Var Q
    NEslot Q false = G.⌜ NonTrivial ⌝

    NEvar : V → G.Functor tt
    NEvar Q = G.&e Bool (NEslot Q)

    -- THE LINE THE BINARY VERSION CANNOT WRITE.  No match on the arity,
    -- so no two-element eliminator and no `Bool`.
    binSlot : ((a : σ .arities o) → V) → (a : σ .arities o) → G.Functor tt
    binSlot Qs a = NEvar (Qs a)

    ruleF : (P : V) → Rule P → G.Functor tt
    ruleF P (inl (c  , _)) = G.⌜ atom c ⌝
    ruleF P (inr (Qs , _)) = G.⊗e o (binSlot Qs)

    CNFF : (P : V) → G.Functor tt
    CNFF P = G.⊕e (Rule P) (ruleF P)

    -- the parse trees, as a grammar
    Deriv : V → TheoryTy ℓ-zero tt
    Deriv P w = G.μ CNFF (P , w)

    Der : G.Ix → Type ℓ-zero
    Der = G.μ CNFF

    -- the description read as connectives; each of these is the
    -- corresponding former DEFINITIONALLY, which is what lets the
    -- generic deciders apply with no coercion
    Layer : V → TheoryTy ℓ-zero tt
    Layer P = G.⟦ CNFF P ⟧c Der

    RuleG : (P : V) → Rule P → TheoryTy ℓ-zero tt
    RuleG P r = G.⟦ ruleF P r ⟧c Der

    SlotG : V → TheoryTy ℓ-zero tt
    SlotG Q = G.⟦ NEvar Q ⟧c Der

    binSlots : ((a : σ .arities o) → V) → (a : σ .arities o)
             → TheoryTy ℓ-zero tt
    binSlots Qs a = G.⟦ binSlot Qs a ⟧c Der

    -- the fixed point, generically: `Grading.Grade`, not per instance
    unrollD : (P : V) → Deriv P ⊢ Layer P
    unrollD P = G.unrollg CNFF P

    rollD : (P : V) → Layer P ⊢ Deriv P
    rollD P = G.rollg CNFF P
