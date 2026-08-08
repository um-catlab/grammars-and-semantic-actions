{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The trace monoid as a `Fibered`: carrier `Word`, `Split` the I-shuffle. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Traces.Base
  (Letter : Type₀) (Ind : Letter → Letter → Type₀) where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Unit
open import Cubical.Data.List
open import Cubical.Data.Empty using (⊥)

open import TheoryGrammar.Base
open import TheoryGrammar.Theories.Monoid public
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib
open import TheoryGrammar.Decidable.Tensor

open import TheoryGrammar.Instances.Traces.Shuffle Letter public

-- `MonSplit o w` DENOTES the ways w decomposes at o.  At `appop` that is
-- a pair of factors TOGETHER WITH the shuffle exhibiting them, so the
-- commutation is carried by the splitting and never re-derived.
MonSplit : (o : MonOp) → Word → Type₀
MonSplit nilop w = IsNil w
MonSplit appop w = Σ[ u ∈ Word ] Σ[ v ∈ Word ] ITr Ind u v w

-- `MonParts o w sp i` DENOTES the factor in slot i of the splitting sp.
MonParts : (o : MonOp) (w : Word) → MonSplit o w → MonAr o → Word
MonParts nilop w sp ()
MonParts appop w (u , v , _) b = if b then u else v

trFib : Fibered monoidSig ℓ-zero ℓ-zero
trFib .carrier _ = Word
trFib .Split     = MonSplit
trFib .parts     = MonParts

-- The total point, separately. Concatenation is total, so the split costs
-- this instance nothing; what it buys is that the connectives never
-- consult it -- which matters here, because the containment is STRICT (see
-- `Examples.swap-ab`).
trPoint : LaxPoint trFib
trPoint .op nilop _   = []
trPoint .op appop f   = f true ++ f false
trPoint .split nilop f = tt
trPoint .split appop f = f true , f false , itrApp Ind (f true) (f false)
trPoint .parts-split nilop f = funExt λ ()
trPoint .parts-split appop f = funExt λ { false → refl ; true → refl }

open DecFib trFib public

-- `Gr` DENOTES a predicate on traces -- the only sort there is.
Gr : Type₁
Gr = TheoryTy ℓ-zero tt

-- `_⊗'_`/`ε'` DENOTE separating conjunction and its unit: `(P ⊗' Q) w`
-- says w shuffles into a P-factor and a Q-factor.
infixr 20 _⊗'_

_⊗'_ : Gr → Gr → Gr
P ⊗' Q = ⊗ˢ appop (λ b → if b then P else Q)

ε' : Gr
ε' = ⊗ˢ nilop (λ ())

⊗-mk : {P Q : Gr} {u v w : Word} → ITr Ind u v w → P u → Q v → (P ⊗' Q) w
⊗-mk {u = u} {v} s p q = (u , v , s) , λ { true → p ; false → q }
