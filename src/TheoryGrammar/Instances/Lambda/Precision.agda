{- PRECISION OVER A SYNTAX -- THE OTHER SIDE OF THE DIVIDE. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Lambda.Precision where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Bool.Properties as B
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Precision
open import TheoryGrammar.Instances.Lambda.Signature
open import TheoryGrammar.Instances.Lambda.Fibered
open import TheoryGrammar.Instances.Lambda.Readable

module LamPrecision (Name : Type₀) where

  open Terms Name
  open Readable Name using (Split-isProp)
  open FibNotation λFib
  open Prec λFib public

  -- 1.  `splitProp` HOLDS, so precision is free.

  λ-splitProp : SplitProp
  λ-splitProp = Split-isProp

  λ-partsProp : PartsProp
  λ-partsProp = splitProp→partsProp λ-splitProp

  λ-preciseP : (o : LOp) (i : LAr o) (A : TheoryTy ℓ-zero (LSortOf o i))
             → PreciseP o i A
  λ-preciseP = partsProp→preciseP λ-partsProp

  λ-preciseI : (o : LOp) (i : LAr o) (A : TheoryTy ℓ-zero (LSortOf o i))
             → PreciseI ℓ-zero o i A
  λ-preciseI = partsProp→preciseI λ-partsProp ℓ-zero

  -- ... including at `⊤G`, which is where heaps stop
  λ-preciseI-⊤ : (o : LOp) (i : LAr o) → PreciseI ℓ-zero o i ⊤G
  λ-preciseI-⊤ o i = λ-preciseI o i ⊤G

  -- 2.  THE BINARY READING at `appOp`, whose arity is `Bool` and whose
  -- eliminator is `B.elim` -- the same two computation rules the heap
  -- instance discharges with `boolΠ`.

  open Binary appOp true false B.elim (λ _ _ → Eq.refl) (λ _ _ → Eq.refl) public

  λ-preciseApp : (A : TheoryTy ℓ-zero tm) → PreciseB A
  λ-preciseApp A = preciseI→preciseB A (λ-preciseI appOp true A)

  -- 3. AND THE CONVERSE, which needs `PartsFaithful`.

  λ-faithful : (o : LOp) → PartsFaithfulAt o
  λ-faithful o m p q _ = Split-isProp o m p q

  λ-merge→splitProp : (o : LOp) → MergeAt ℓ-zero o → SplitPropAt o
  λ-merge→splitProp o mg =
    partsProp→splitProp o (λ-faithful o) (merge→partsProp o mg)

  λ-splitProp→merge : (ℓB : Level) (o : LOp) → SplitPropAt o → MergeAt ℓB o
  λ-splitProp→merge ℓB o sp =
    partsProp→merge ℓB o (splitPropAt→partsPropAt o sp)

-- 4. AND IT COMPUTES.

private
  open Terms ℕ
  open FibNotation λFib
  open LamPrecision ℕ

  K : TheoryTy ℓ-zero tm
  K _ = ℕ

  t : Raw
  t = app (var 0) (var 1)

  d : ((⌈ var 0 ⌉ ⊛ K) & (⌈ var 0 ⌉ ⊛ K)) t
  d = (mkApp (var 0) (var 1) , B.elim Eq.refl 7)
    , (mkApp (var 0) (var 1) , B.elim Eq.refl 9)

  merged : (⌈ var 0 ⌉ ⊛ (K & K)) t
  merged = λ-preciseApp ⌈ var 0 ⌉ K K t d

  _ : merged .snd false .fst Eq.≡ 7
  _ = Eq.refl

  _ : merged .snd false .snd Eq.≡ 9
  _ = Eq.refl
