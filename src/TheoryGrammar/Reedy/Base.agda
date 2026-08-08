{- REEDY STRUCTURE — the definition that `Cubical.Categories.Direct` does
   NOT contain. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Reedy.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category

open import Cubical.Categories.Direct.Base
  using (WFOrder ; DirectStr ; mkDirectStr ; module DirectNotation)

private variable ℓC ℓC' ℓD ℓ< ℓM : Level

-- A wide subcategory, as a property of morphisms.

record isWide {C : Category ℓC ℓC'}
              (P : {x y : Category.ob C} → C [ x , y ] → Type ℓM)
  : Type (ℓ-max (ℓ-max ℓC ℓC') ℓM) where
  open Category C
  field
    P-id  : {x : ob} → P (id {x})
    P-seq : {x y z : ob} (f : C [ x , y ]) (g : C [ y , z ])
          → P f → P g → P (f ⋆ g)

open isWide public

-- THE REEDY STRUCTURE.

module _ (C : Category ℓC ℓC') (Wo : WFOrder ℓD ℓ<) (ℓM : Level) where
  private
    module C  = Category C
    module Wo = WFOrder Wo

  -- a lowering-then-raising factorisation of f
  module _ (deg : C.ob → Wo.D)
           (C₋ C₊ : {x y : C.ob} → C [ x , y ] → Type ℓM) where

    Factorisation : {x y : C.ob} → C [ x , y ] → Type (ℓ-max (ℓ-max ℓC ℓC') ℓM)
    Factorisation {x} {y} f =
      Σ[ z ∈ C.ob ] Σ[ g ∈ C [ x , z ] ] Σ[ h ∈ C [ z , y ] ]
        (C₋ g × C₊ h × (g C.⋆ h ≡ f))

  record ReedyStr : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max (ℓ-max ℓD ℓ<) (ℓ-suc ℓM))) where
    field
      deg : C.ob → Wo.D

      -- the two wide subcategories
      C₋      : {x y : C.ob} → C [ x , y ] → Type ℓM
      C₊      : {x y : C.ob} → C [ x , y ] → Type ℓM
      wide₋   : isWide {C = C} C₋
      wide₊   : isWide {C = C} C₊

      -- C₋ lowers, C₊ raises.  (Non-strict; strictness below.)
      lowers  : {x y : C.ob} (f : C [ x , y ]) → C₋ f → deg y Wo.≤ deg x
      raises  : {x y : C.ob} (f : C [ x , y ]) → C₊ f → deg x Wo.≤ deg y

      -- THE AXIOM.  Every morphism factors, uniquely, as lower-then-raise.
      factor  : {x y : C.ob} (f : C [ x , y ])
              → isContr (Factorisation deg C₋ C₊ f)

    -- The immediate consequence: a morphism in BOTH classes preserves
    -- degree.
    degFixed : {x y : C.ob} (f : C [ x , y ]) → C₋ f → C₊ f
             → (deg x Wo.≤ deg y) × (deg y Wo.≤ deg x)
    degFixed f m p = raises f p , lowers f m

    -- and hence no strict drop can also be a rise
    noSwing : {x y : C.ob} (f : C [ x , y ]) → C₋ f → C₊ f
            → deg y Wo.< deg x → ⊥.⊥
    noSwing f m p d = Wo.¬<refl (Wo.≤-<-trans (raises f p) d)

  open ReedyStr public

-- DIRECT IS THE DEGENERATE REEDY STRUCTURE. Take C₋ = "f is an identity"
-- and C₊ = everything.

module DirectIsReedy {C : Category ℓC ℓC'} {Wo : WFOrder ℓD ℓ<}
                     (thin : {x y : Category.ob C} → isProp (C [ x , y ]))
                     (dir : DirectStr C Wo) where
  private
    module C  = Category C
    module Wo = WFOrder Wo
  open DirectNotation dir renaming (deg to degD)

  -- in a thin category, "is an identity" carries no more than x ≡ y
  Id : {x y : C.ob} → C [ x , y ] → Type ℓC
  Id {x} {y} _ = x ≡ y

  All : {x y : C.ob} → C [ x , y ] → Type ℓC
  All _ = Unit* {ℓC}

  wideId : isWide {C = C} Id
  wideId .P-id      = refl
  wideId .P-seq _ _ = _∙_

  wideAll : isWide {C = C} All
  wideAll .P-id          = tt*
  wideAll .P-seq _ _ _ _ = tt*

  private
    Fact : {x y : C.ob} → C [ x , y ] → Type _
    Fact = Factorisation C Wo ℓC degD Id All

    ctr : {x y : C.ob} (f : C [ x , y ]) → Fact f
    ctr {x} f = x , C.id , f , refl , tt* , C.⋆IdL f

    -- The factorisation object is forced to be x: the pair (z, p) lives in
    -- the based path space `singl x`, which is contractible, and
    -- everything else is propositional because C is thin.
    isPropFact : {x y : C.ob} (f : C [ x , y ]) → isProp (Fact f)
    isPropFact {x} {y} f (z , g , h , p , _ , e) (z' , g' , h' , p' , _ , e') i =
        sq i .fst
      , gp i
      , hp i
      , sq i .snd
      , tt*
      , isProp→PathP (λ j → isProp→isSet thin (gp j C.⋆ hp j) f) e e' i
      where
        sq : Path (singl x) (z , p) (z' , p')
        sq = isContr→isProp (isContrSingl x) (z , p) (z' , p')

        gp : PathP (λ i → C [ x , sq i .fst ]) g g'
        gp = isProp→PathP (λ i → thin {x} {sq i .fst}) g g'

        hp : PathP (λ i → C [ sq i .fst , y ]) h h'
        hp = isProp→PathP (λ i → thin {sq i .fst} {y}) h h'

  directReedy : ReedyStr C Wo ℓC
  directReedy .deg    = degD
  directReedy .C₋     = Id
  directReedy .C₊     = All
  directReedy .wide₋  = wideId
  directReedy .wide₊  = wideAll
  directReedy .lowers f p = inr (Eq.pathToEq (cong degD (sym p)))
  directReedy .raises f _ = non-dec f
  directReedy .factor f   = ctr f , isPropFact f (ctr f)
