{- What this instance owes `TheoryGrammar.Decidable`: a `DecReadable`, and
   the two PARTITIONS its `decSplit` is read off. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.LinTyped.Readable where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit using (Unit; tt)

open import TheoryGrammar.Base
open import TheoryGrammar.Decidable
open import TheoryGrammar.Fibered
open import TheoryGrammar.Representable
open import TheoryGrammar.View
open import TheoryGrammar.Instances.LinTyped.Signature
open import TheoryGrammar.Instances.LinTyped.Fibered
open import TheoryGrammar.Instances.LinTyped.Base

open Views linFib using (Cover; Complete; exclusive; fromUnique; decBranch)

-- PRIMITIVE.  At most one splitting, at either result sort.
Split-isProp : (o : TOp) (m : Carrier (TResult o)) (p q : TSplit o m) → p ≡ q
Split-isProp varOp  _ (mkVar _)   (mkVar _)   = refl
Split-isProp appOp  _ (mkApp _ _) (mkApp _ _) = refl
Split-isProp lamOp  _ (mkLam _)   (mkLam _)   = refl
Split-isProp annOp  _ (mkAnn _ _) (mkAnn _ _) = refl
Split-isProp baseOp _ mkBase      mkBase      = refl
Split-isProp lolOp  _ (mkLol _ _) (mkLol _ _) = refl

open UniqueSplit Split-isProp public
open Repr linFib linPoint unsplit public using (⌈⌉-into; ⌈⌉-from; op-inj)

-- PRIMITIVE.  THE OPERATIONS PARTITION THE CARRIER -- ONCE PER SORT.

-- `TmOp`/`TyOp` denote the branch labels of the two partitions.
data TmOp : Type₀ where oVar oApp oLam oAnn : TmOp
data TyOp : Type₀ where oBase oLol : TyOp

-- `tmB o` denotes "this term is an `o`-node", with the slots erased.
tmB : TmOp → TheoryTy ℓ-zero tm
tmB oVar = ⊗ˢ varOp (λ _ → ⊤G)
tmB oApp = ⊗ˢ appOp (λ _ → ⊤G)
tmB oLam = ⊗ˢ lamOp (λ _ → ⊤G)
tmB oAnn = ⊗ˢ annOp (λ _ → ⊤G)

-- `tyB o` denotes the same at the `ty` sort.
tyB : TyOp → TheoryTy ℓ-zero ty
tyB oBase = ⊗ˢ baseOp (λ _ → ⊤G)
tyB oLol  = ⊗ˢ lolOp  (λ _ → ⊤G)

tmOf : Raw → TmOp
tmOf (var _)   = oVar
tmOf (app _ _) = oApp
tmOf (lam _)   = oLam
tmOf (ann _ _) = oAnn

tyOf : Ty → TyOp
tyOf base       = oBase
tyOf (_ ⊸ᵗ _)  = oLol

-- an `o`-splitting of `t` forces `o` to be `t`'s own label
tmB→tmOf : (o : TmOp) (t : Raw) → tmB o t → o ≡ tmOf t
tmB→tmOf oVar .(var _)   (mkVar _   , _) = refl
tmB→tmOf oApp .(app _ _) (mkApp _ _ , _) = refl
tmB→tmOf oLam .(lam _)   (mkLam _   , _) = refl
tmB→tmOf oAnn .(ann _ _) (mkAnn _ _ , _) = refl

tyB→tyOf : (o : TyOp) (A : Ty) → tyB o A → o ≡ tyOf A
tyB→tyOf oBase .base      (mkBase    , _) = refl
tyB→tyOf oLol  .(_ ⊸ᵗ _) (mkLol _ _ , _) = refl

-- `tmCase`/`tyCase` denote the partitions themselves.
tmCase : Complete TmOp tmB
tmCase = fromUnique discrim
           (λ y z t py pz → tmB→tmOf y t py ∙ sym (tmB→tmOf z t pz))
  where
    discrim : Cover (⊕ᴰ TmOp tmB)
    discrim (var n)   _ = oVar , (mkVar n   , λ _ → tt)
    discrim (app u v) _ = oApp , (mkApp u v , λ _ → tt)
    discrim (lam t)   _ = oLam , (mkLam t   , λ _ → tt)
    discrim (ann t A) _ = oAnn , (mkAnn t A , λ _ → tt)

tyCase : Complete TyOp tyB
tyCase = fromUnique discrim
           (λ y z A py pz → tyB→tyOf y A py ∙ sym (tyB→tyOf z A pz))
  where
    discrim : Cover (⊕ᴰ TyOp tyB)
    discrim base      _ = oBase , (mkBase    , λ _ → tt)
    discrim (A ⊸ᵗ B) _ = oLol  , (mkLol A B , λ _ → tt)

-- ... and therefore `⊗-decSplit` is DERIVED.

private
  TmCode : TmOp → TmOp → Type₀
  TmCode oVar oVar = Unit
  TmCode oApp oApp = Unit
  TmCode oLam oLam = Unit
  TmCode oAnn oAnn = Unit
  TmCode _    _    = ⊥

  tmRefl : (y : TmOp) → TmCode y y
  tmRefl oVar = tt
  tmRefl oApp = tt
  tmRefl oLam = tt
  tmRefl oAnn = tt

  tmEncode : (y z : TmOp) → y ≡ z → TmCode y z
  tmEncode y z p = subst (TmCode y) p (tmRefl y)

  TyCode : TyOp → TyOp → Type₀
  TyCode oBase oBase = Unit
  TyCode oLol  oLol  = Unit
  TyCode _     _     = ⊥

  tyRefl : (y : TyOp) → TyCode y y
  tyRefl oBase = tt
  tyRefl oLol  = tt

  tyEncode : (y z : TyOp) → y ≡ z → TyCode y z
  tyEncode y z p = subst (TyCode y) p (tyRefl y)

tmB-cmp : (y z : TmOp) → (tmB z ⊢ tmB y) ⊎ (y ≡ z → ⊥)
tmB-cmp oVar oVar = inl idg
tmB-cmp oApp oApp = inl idg
tmB-cmp oLam oLam = inl idg
tmB-cmp oAnn oAnn = inl idg
tmB-cmp oVar oApp = inr (tmEncode oVar oApp)
tmB-cmp oVar oLam = inr (tmEncode oVar oLam)
tmB-cmp oVar oAnn = inr (tmEncode oVar oAnn)
tmB-cmp oApp oVar = inr (tmEncode oApp oVar)
tmB-cmp oApp oLam = inr (tmEncode oApp oLam)
tmB-cmp oApp oAnn = inr (tmEncode oApp oAnn)
tmB-cmp oLam oVar = inr (tmEncode oLam oVar)
tmB-cmp oLam oApp = inr (tmEncode oLam oApp)
tmB-cmp oLam oAnn = inr (tmEncode oLam oAnn)
tmB-cmp oAnn oVar = inr (tmEncode oAnn oVar)
tmB-cmp oAnn oApp = inr (tmEncode oAnn oApp)
tmB-cmp oAnn oLam = inr (tmEncode oAnn oLam)

tyB-cmp : (y z : TyOp) → (tyB z ⊢ tyB y) ⊎ (y ≡ z → ⊥)
tyB-cmp oBase oBase = inl idg
tyB-cmp oLol  oLol  = inl idg
tyB-cmp oBase oLol  = inr (tyEncode oBase oLol)
tyB-cmp oLol  oBase = inr (tyEncode oLol  oBase)

-- the two partitions, dispatched by which sort the operation lands at
⊗-decSplit : (o : TOp) → ⊤G ⊢ Dec⟨ ⊗ˢ o (λ _ → ⊤G) ⟩
⊗-decSplit varOp  = decBranch tmB-cmp tmCase oVar
⊗-decSplit appOp  = decBranch tmB-cmp tmCase oApp
⊗-decSplit lamOp  = decBranch tmB-cmp tmCase oLam
⊗-decSplit annOp  = decBranch tmB-cmp tmCase oAnn
⊗-decSplit baseOp = decBranch tyB-cmp tyCase oBase
⊗-decSplit lolOp  = decBranch tyB-cmp tyCase oLol

-- Slotwise decisions combine.  Matches on the OPERATION, never on a
-- term and never on a sum.  The two UNARY operations use `decSlots¹`.
linDecSlots : (o : TOp) (A : (a : TAr o) → TheoryTy ℓ-zero (TSortOf o a))
              (m : Carrier (TResult o)) (sp : TSplit o m)
            → ((a : TAr o) → Dec⟨ A a ⟩ (TParts o m sp a))
            → Dec⟨ ⊗ˢ o A ⟩ m
linDecSlots varOp  A m sp h = decSlots¹ varOp A m sp tt (λ x _ → x) (h tt)
linDecSlots lamOp  A m sp h = decSlots¹ lamOp A m sp tt (λ x _ → x) (h tt)
linDecSlots baseOp A m sp h = dec-yes (⊗ˢ baseOp A) m (sp , λ ())
linDecSlots appOp  A m sp h =
  decSlots² appOp A m sp true false decSlotsBool (h true) (h false)
linDecSlots annOp  A m sp h =
  decSlots² annOp A m sp true false decSlotsBool (h true) (h false)
linDecSlots lolOp  A m sp h =
  decSlots² lolOp A m sp true false decSlotsBool (h true) (h false)

linDR : DecReadable linFib ℓ-zero
linDR .splitProp = Split-isProp
linDR .decSplit  = ⊗-decSplit
linDR .decSlots  = linDecSlots

open DecTensor linDR public using (dec-⊗)

-- DERIVED.  Two views of the SAME world cannot use different head
-- operations: the partition's own `exclusive`, pulled back along the
-- maps that forget the slots.

varApp-⊥ : {P : NmG} {A B : TmG} → (VarG P & AppG A B) ⊢ ⊥G
varApp-⊥ {P} {A} {B} =
  exclusive tmCase oVar oApp (tmEncode oVar oApp)
  ∘g &-I (⊗-erase varOp (varFam P)   ∘g &-E₁)
         (⊗-erase appOp (appFam A B) ∘g &-E₂)

varAnn-⊥ : {P : NmG} {A : TmG} {Q : TyG} → (VarG P & AnnG A Q) ⊢ ⊥G
varAnn-⊥ {P} {A} {Q} =
  exclusive tmCase oVar oAnn (tmEncode oVar oAnn)
  ∘g &-I (⊗-erase varOp (varFam P)   ∘g &-E₁)
         (⊗-erase annOp (annFam A Q) ∘g &-E₂)

appAnn-⊥ : {A B : TmG} {C : TmG} {Q : TyG} → (AppG A B & AnnG C Q) ⊢ ⊥G
appAnn-⊥ {A} {B} {C} {Q} =
  exclusive tmCase oApp oAnn (tmEncode oApp oAnn)
  ∘g &-I (⊗-erase appOp (appFam A B) ∘g &-E₁)
         (⊗-erase annOp (annFam C Q) ∘g &-E₂)

-- the `ty` sort's only pair, at arbitrary lollipop slots
baseLol-⊥ : {A : (a : TAr lolOp) → TheoryTy ℓ-zero (TSortOf lolOp a)}
          → (tyB oBase & ⊗ˢ lolOp A) ⊢ ⊥G
baseLol-⊥ {A} =
  exclusive tyCase oBase oLol (tyEncode oBase oLol)
  ∘g &-I &-E₁ (⊗-erase lolOp A ∘g &-E₂)
