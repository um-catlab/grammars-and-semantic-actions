{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- A DECIDED DESCRIPTION IS ALREADY A GENERATOR.
   `Decidable.Inductive.DecDesc` and `Generate.GenDesc` have the same five
   clauses, and in every one the decision datum is at least as strong as
   the generation datum: DecDesc GenDesc the map Probe B Seek B
   `probe→seek`: a decision is a search space of... -}
module TheoryGrammar.Generate.FromDec where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Sum as Sum using (_⊎_; inl; inr)
open import Cubical.Data.List

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Grading
open import TheoryGrammar.Inductive
open import TheoryGrammar.Enumerable
open import TheoryGrammar.Enumerable.Listed
open import TheoryGrammar.Decidable.Inductive
open import TheoryGrammar.Generate

private variable ℓS ℓ ℓ' ℓX ℓP ℓV : Level

module GenFromDec {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
                  (GS : GradedFib σ ℓX ℓP) (ℓA : Level)
                  (X : Type ℓV) (xs : X → S)
                  (enumSplit : (o : σ .ops)
                               (m : GS .fib .carrier (σ .resultSort o))
                             → Listed (GS .fib .Split o m))
                  (enumAr : (o : σ .ops) → Listed (σ .arities o))
                  where

  -- SELECTIVE, as in `DyckDec`: both modules re-export `Ind`'s names and
  -- opening both unqualified would make every one of them ambiguous.
  open DecInd GS ℓA X xs enumSplit enumAr using (DecDesc; Probe)

  -- ... and THE FORGETTING: `Listed` minus `complete`.
  open GenInd (GS .fib) ℓA X xs (λ o m _ → enumSplit o m .elts) enumAr public

  -- a decision IS a search space -- of size 1 on the yes branch and 0 on
  -- the no branch, which is the sense in which deciding is harder
  probe→seek : {s : S} {B : TheoryTy ℓA s} → Probe B → Seek B
  probe→seek d m _ = Sum.rec (λ b → b ∷ []) (λ _ → []) (d m tt)

  fromDec : {s : S} (G : Functor s) → DecDesc G → GenDesc G
  fromDec (⌜ B ⌝)  dB        = lift (probe→seek (lower dB))
  fromDec (Var x)  _         = tt*
  fromDec (⊕e Y G) (lY , dG) = lY .elts , λ y → fromDec (G y) (dG y)
  fromDec (&e Y G) (lY , dG) = lY , λ y → fromDec (G y) (dG y)
  fromDec (⊗e o G) dG        = λ a → fromDec (G a) (dG a)
