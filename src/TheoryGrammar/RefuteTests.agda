{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- `¬presApp`, REDISCOVERED BY SEARCH. `Reindex.LinLam` proves that the
   AST-to-usages bridge is not a `Pass`, by exhibiting `dapp (dvar 0) (dvar
   0)` -- the standard non-linear term -- and refuting preservation there. -}
module TheoryGrammar.RefuteTests where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.List
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty as E using (⊥)
open import Cubical.Data.FinData.Base using (Fin)
  renaming (zero to fzero; suc to fsuc)

open import TheoryGrammar.Enumerable using (No)
open import TheoryGrammar.Reindex.Base using (PresAt; SplitPresAtOver)
open import TheoryGrammar.Refute

open import TheoryGrammar.Instances.Lambda.Signature using (LOp; varOp; appOp; lamOp)
open import TheoryGrammar.Instances.LinLam.DB using (DBTm; dvar; dapp; dlam; Term•)
open import TheoryGrammar.Instances.LinLam.Check using (Dec⊎)
open import TheoryGrammar.Reindex.LinLam using (fvMap; presApp?; ¬presApp)

open RefuteAt fvMap appOp

-- 1. THE DECIDER, MADE TOTAL.

ofDec⊎ : {A : Type₀} → Dec⊎ A → A ⊎ No A
ofDec⊎ (inl a) = inl a
ofDec⊎ (inr k) = inr λ a → lift (k a)

presAt? : (m : Term•) → PresAt fvMap appOp m ⊎ No (PresAt fvMap appOp m)
presAt? (n , dvar i)   = inl λ ()
presAt? (n , dapp u v) = ofDec⊎ (presApp? n u v)
presAt? (n , dlam b)   = inl λ ()

-- 2. THE SEARCH SPACE.

x₀ x₁ : DBTm 2
x₀ = dvar fzero
x₁ = dvar (fsuc fzero)

space : List Term•
space = (2 , x₀)                     -- a variable: no `appOp` splitting
      ∷ (2 , dlam (dvar fzero))      -- a lambda:   no `appOp` splitting
      ∷ (2 , dapp x₀ x₁)             -- LINEAR, and rejected as such
      ∷ (2 , dapp x₁ x₀)             -- LINEAR
      ∷ (2 , dapp x₀ x₀)             -- NON-LINEAR: the counterexample
      ∷ (2 , dapp x₁ x₁)             -- also non-linear, never reached
      ∷ []

verdict : Verdict
verdict = scanPres presAt? space

-- 3.  WHAT IT FOUND.

_ : culprit verdict ≡ just (2 , dapp x₀ x₀)
_ = refl

-- ... AND THE THEOREM.
notAPass : No (SplitPresAtOver fvMap appOp)
notAPass = theorem verdict tt

-- the same statement in `¬presApp`'s own form (`⊥`, not `⊥*`), so the
-- two are visibly the same theorem
notAPass' : SplitPresAtOver fvMap appOp → ⊥
notAPass' P = notAPass P .lower

-- 4. A CLEAN RUN PROVES NOTHING, AND THE TYPE SAYS SO.

linearSpace : List Term•
linearSpace = (2 , x₀) ∷ (2 , dlam (dvar fzero))
            ∷ (2 , dapp x₀ x₁) ∷ (2 , dapp x₁ x₀) ∷ []

clean : Verdict
clean = scanPres presAt? linearSpace

_ : culprit clean ≡ nothing
_ = refl

_ : tried clean ≡ 4
_ = refl

-- 5. THE SAME SCAN, DRIVEN BY THE FUZZER.

open import Cubical.Data.Bool using (Bool; true; false)

open import TheoryGrammar.Reindex.Base using (ofReindex; presToOver; fromPres)
open import TheoryGrammar.Theories.Monoid using (MonOp; nilop; appop)
open import TheoryGrammar.Instances.Strings.Base Bool using (String)
open import TheoryGrammar.Instances.Nat.LengthFib Bool using (lenIx; lenPres)
open import TheoryGrammar.GenerateTests using (fuzzWords)

lenOver = ofReindex lenIx

module Len = RefuteAt lenOver appop

presAtLen? : (m : String)
           → PresAt lenOver appop m ⊎ No (PresAt lenOver appop m)
presAtLen? m = inl (fromPres lenOver appop (presToOver lenIx appop (lenPres appop)) m)

lenVerdict : Len.Verdict
lenVerdict = Len.scanPres presAtLen? (fuzzWords 8 16 2024)

_ : Len.culprit lenVerdict ≡ nothing
_ = refl

_ : Len.tried lenVerdict ≡ 16
_ = refl
