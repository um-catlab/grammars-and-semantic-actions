{- A SPLITTING DISPLAYED OVER A PROJECTION. `Splitting` factors the carrier
   out of `Fibered`; this factors the splittings themselves. -}
module TheoryGrammar.Lifting where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Splitting
open import TheoryGrammar.CarrierMap
open import TheoryGrammar.Gluing

private variable ℓS ℓ ℓ' ℓX ℓX' ℓY ℓP ℓP' ℓQ ℓR : Level

record Lifting {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} {X : S → Type ℓX}
               (Sp : Splitting σ X ℓP) (Y : S → Type ℓY)
               (π : (s : S) → Y s → X s) ℓQ
  : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓX (ℓ-max ℓY (ℓ-max ℓP (ℓ-suc ℓQ)))))) where
  field
    -- the lifts of a base splitting, indexed by the point upstairs
    Split↑ : (o : σ .ops) (y : Y (σ .resultSort o))
           → Sp .Split o (π _ y) → Type ℓQ
    -- what a lift holds ...
    parts↑ : (o : σ .ops) (y : Y (σ .resultSort o))
             (sp : Sp .Split o (π _ y)) → Split↑ o y sp
           → (a : σ .arities o) → Y (σ .sortOf o a)
    -- ... and that it lies over the base parts.  In `Eq`, so that
    -- `push⊗`'s coercion still reduces.
    over   : (o : σ .ops) (y : Y (σ .resultSort o))
             (sp : Sp .Split o (π _ y)) (l : Split↑ o y sp) (a : σ .arities o)
           → π _ (parts↑ o y sp l a) Eq.≡ Sp .parts o (π _ y) sp a

open Lifting public

module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} {X : S → Type ℓX}
         {Sp : Splitting σ X ℓP} {Y : S → Type ℓY}
         {π : (s : S) → Y s → X s} (L : Lifting Sp Y π ℓQ) where

  total : Splitting σ Y (ℓ-max ℓP ℓQ)
  total .Split o y       = Σ[ sp ∈ Sp .Split o (π _ y) ] L .Split↑ o y sp
  total .parts o y sq a  = L .parts↑ o y (sq .fst) (sq .snd) a

  -- the projection, as a reindexing that preserves every splitting
  proj : Reindex ⟪ Y , total ⟫ ⟪ X , Sp ⟫
  proj .hom = π

  projPres : (o : σ .ops) → SplitPresAt proj o
  projPres o .homSplit _ sq      = sq .fst
  projPres o .homParts y sq a    = Eq.sym (L .over o y (sq .fst) (sq .snd) a)

-- GLUING IS A LIFTING, on the nose.

module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
         (Fib : Fibered σ ℓX ℓP) (Fib' : Fibered σ ℓX' ℓP')
         (R : Corr Fib Fib' ℓR) where

  open Glue Fib Fib' R

  glueLifting : Lifting (splittingOf Fib) (glue .carrier) (π₁ .hom)
                        (ℓ-max ℓP' (ℓ-max ℓ' ℓR))
  glueLifting .Split↑ o g sp       = Splitᴰ o (g .fst) (g .snd .fst) sp
  glueLifting .parts↑ o g sp l a   = glue .parts o g (sp , l) a
  glueLifting .over   o g sp l a   = Eq.refl

  -- THE MEASUREMENT.  The glued `Fibered`'s splittings ARE the total of
  -- this lifting -- not isomorphic to them.
  glue-is-total : total glueLifting ≡ splittingOf glue
  glue-is-total = refl

  -- ... and the lifting's projection is `Glue`'s own, not merely one
  -- like it.  This one typechecks only BECAUSE of the line above.
  proj-is-π₁ : proj glueLifting ≡ π₁
  proj-is-π₁ = refl

-- TWO SIGNATURES ON ONE CARRIER. This is what `Gluing` could not state.

module _ {S : Type ℓS} {σ τ : SortedSig S ℓ ℓ'}
         {X X' : S → Type ℓX} {Y : S → Type ℓY}
         {Sp : Splitting σ X ℓP} {Sq : Splitting τ X' ℓP}
         {π : (s : S) → Y s → X s} {π' : (s : S) → Y s → X' s}
         (L : Lifting Sp Y π ℓQ) (L' : Lifting Sq Y π' ℓQ) where

  bothLift : Splitting (σ ⊎Sig τ) Y (ℓ-max ℓP ℓQ)
  bothLift = total L ⊎Spl total L'

  -- each theory still projects to its own factor, preserving splittings
  projˡ : Reindex ⟪ Y , total L ⟫ ⟪ X , Sp ⟫
  projˡ = proj L

  projʳ : Reindex ⟪ Y , total L' ⟫ ⟪ X' , Sq ⟫
  projʳ = proj L'
