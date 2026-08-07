{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  A PARTIALLY COMMUTATIVE substructural mode.

  `Modes/Concat` is `Uses` at the free monoid (ordered) and
  `Modes/Interleave` is `Uses` at the free commutative monoid (linear).
  This is the same grammar at the trace substrate, so it sits strictly
  between them: exchange is licensed exactly on independent names.

  Only `Split` changes -- `Uses`, `check` and `accepts` are inherited
  from `Modes/Core` unmodified, which is the whole claim.

  DEFINES `Ctx`, `CSplit`/`CParts`, the promodel `fib` and point
  `point`, the decision `decEnum`/`dec`, and the module `Trace` -- the
  mode itself, with leaf `Lf n = ⌈n⌉` and no modality.
-}
open import Cubical.Foundations.Prelude

open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Relation.Nullary.Base using (Discrete)
open import TheoryGrammar.Enumerable using (No)

module TheoryGrammar.Instances.Traces.Mode
  (Name : Type₀) (Ind : Name → Name → Type₀)
  (decInd    : (x y : Name) → Ind x y ⊎ No (Ind x y))
  (isPropInd : (x y : Name) → isProp (Ind x y))
  (decName : Discrete Name)
  where

open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.List using (List; []; _∷_; _++_)
open import Cubical.Data.List.Properties using (discreteList)

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Enumerable using (decΠBool)
open import TheoryGrammar.Decidable
open import TheoryGrammar.Decidable.Enumerated
open import TheoryGrammar.Decidable.Splittings
open import TheoryGrammar.Decidable.Representable
open import TheoryGrammar.Instances.Lambda.Modes.Ctx
open import TheoryGrammar.Instances.Lambda.Modes.Core

import TheoryGrammar.Instances.Traces.Enumeration as TrE
module E = TrE Name Ind decInd isPropInd

Ctx : Type₀
Ctx = E.Word

-- the trace splittings, re-presented over `ctxSig`
CSplit : (o : CtxOp) → Ctx → Type₀
CSplit mul Γ = Σ[ u ∈ Ctx ] Σ[ v ∈ Ctx ] E.ITr Ind u v Γ

CParts : (o : CtxOp) (Γ : Ctx) → CSplit o Γ → CtxAr o → Ctx
CParts mul Γ (u , v , _) b = if b then u else v

fib : Fibered ctxSig ℓ-zero ℓ-zero
fib .carrier _ = Ctx
fib .Split     = CSplit
fib .parts     = CParts

point : LaxPoint fib
point .op mul f          = f true ++ f false
point .split mul f       = f true , f false , E.itrApp Ind (f true) (f false)
point .parts-split mul f = funExt λ { true → refl ; false → refl }

-- `splitProp` fails here as it does for every resource substrate, so
-- the enumerable route is the one available.
decEnum : DecEnumerable fib ℓ-zero
decEnum .DecEnumerable.enumSplit    mul Γ             = E.shuffles Γ
decEnum .DecEnumerable.enumComplete mul Γ (u , v , s) = E.complete s
decEnum .decAt mul A Γ sp d = decΠBool (d true) (d false)

dec : DecSplittings fib ℓ-zero
dec = fromEnumerable decEnum

sing : Name → Ctx
sing n = n ∷ []

discreteCtx : Discrete Ctx
discreteCtx = discreteList decName

private
  module TrC = Core Name fib point dec sing
  module TrR = DecRep (fib .carrier)

-- the mode itself: leaf `⌈n⌉`, no modality -- weakening and contraction
-- are absent, exchange is present exactly at independent pairs
module Trace where
  open TrC public

  Lf : Name → CtxG
  Lf n = ⌈ sing n ⌉

  decLf : (n : Name) → ⊤G ⊢ Dec⟨ Lf n ⟩
  decLf n = TrR.dec-⌈⌉ discreteCtx (sing n)

  open Mode Lf decLf public
