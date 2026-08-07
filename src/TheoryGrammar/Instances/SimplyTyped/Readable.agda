{-
  What this instance owes `TheoryGrammar.Decidable`: a `DecReadable`,
  and the two PARTITIONS its `decSplit` is read off.

  Three promodel facts -- at most one splitting, decidably so, and
  slotwise decisions combine -- give `dec-⊗`; `Split-isProp` alone gives
  `⊗-refute`, `⊗-merge` and `merge2` (all `UniqueSplit`'s);
  `Fibered.unsplit` gives `⌈⌉-into`/`⌈⌉-from`, and with `Split-isProp`
  also `op-inj`.

  PRIMITIVE inventory: THREE -- `Split-isProp`, the two partitions
  (`tmCase`/`tyCase`, one per result sort), and `stDecSlots`.
  `⊗-decSplit` is `View.decBranch` at the partitions, and disjointness
  of the head operations is their `exclusive`; neither is primitive.
  Everything the rest of the instance uses about the representation
  comes from here.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.SimplyTyped.Readable where

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
open import TheoryGrammar.Instances.SimplyTyped.Signature
open import TheoryGrammar.Instances.SimplyTyped.Fibered
open import TheoryGrammar.Instances.SimplyTyped.Base

module StReadable (Name : Type₀) where

  open StBase Name
  open Views stlcFib using (Cover; Complete; exclusive; fromUnique; decBranch)

  -- PRIMITIVE.  At most one splitting, at either result sort.
  Split-isProp : (o : TOp) (m : Carrier (TResult o)) (p q : TSplit o m) → p ≡ q
  Split-isProp varOp  _ (mkVar _)   (mkVar _)   = refl
  Split-isProp appOp  _ (mkApp _ _) (mkApp _ _) = refl
  Split-isProp lamOp  _ (mkLam _ _) (mkLam _ _) = refl
  Split-isProp annOp  _ (mkAnn _ _) (mkAnn _ _) = refl
  Split-isProp baseOp _ mkBase      mkBase      = refl
  Split-isProp arrOp  _ (mkArr _ _) (mkArr _ _) = refl

  -- `⊗-refute`, `⊗-merge` AND `merge2` now all come from `UniqueSplit`
  -- -- one hypothesis, read with either sign.  (The module was called
  -- `Precise`; its parameter is unique readability, not precision.)
  -- `merge2` -- merge two tensors at the same operation, then eliminate
  -- -- used to be written out here even though it names nothing but
  -- `⊗-merge` and `⊗ˢ-E`; it now sits beside `⊗-merge` upstream.
  open UniqueSplit Split-isProp public
  open Repr stlcFib stlcPoint unsplit public using (⌈⌉-into; ⌈⌉-from; op-inj)

  -- PRIMITIVE.  And it is decidable whether there is one, internally.
  -- ================================================================
  -- THE OPERATIONS PARTITION THE CARRIER -- ONCE PER SORT.
  --
  -- This instance's operations span TWO sorts, so it is two partitions,
  -- not one: `Complete Y P` fixes a sort, and `⊗ˢ o ⊤` lives at
  -- `TResult o`.  That is the honest shape -- a syntax with several
  -- sorts partitions each of them separately -- and it is why the index
  -- type is a parameter of `Complete` rather than `σ .ops`.
  --
  -- Both are built by `fromUnique`: the branch is a function of the
  -- world, and the split constructor pins the world, so each clause of
  -- `opOf-split` is `refl`.
  -- ================================================================

  -- `TmOp`/`TyOp` denote the branch labels of the two partitions -- the
  -- term-forming and type-forming subsets of `TOp`, as their own types
  -- so that `Complete` can be stated at a fixed sort.
  data TmOp : Type₀ where oVar oApp oLam oAnn : TmOp
  data TyOp : Type₀ where oBase oArr : TyOp

  -- `tmB o` denotes "this term is an `o`-node", with the slots erased.
  tmB : TmOp → TheoryTy ℓ-zero tm
  tmB oVar = ⊗ˢ varOp (λ _ → ⊤G)
  tmB oApp = ⊗ˢ appOp (λ _ → ⊤G)
  tmB oLam = ⊗ˢ lamOp (λ _ → ⊤G)
  tmB oAnn = ⊗ˢ annOp (λ _ → ⊤G)

  -- `tyB o` denotes the same at the `ty` sort.
  tyB : TyOp → TheoryTy ℓ-zero ty
  tyB oBase = ⊗ˢ baseOp (λ _ → ⊤G)
  tyB oArr  = ⊗ˢ arrOp  (λ _ → ⊤G)

  -- `tmOf t` denotes the label of `t`'s head node; `tyOf` the same at
  -- `ty`.  Only `fromUnique` consumes these -- nothing downstream reads
  -- a bare label, because `tmCase` hands back the SPLITTING as well.
  tmOf : Raw → TmOp
  tmOf (var _)   = oVar
  tmOf (app _ _) = oApp
  tmOf (lam _ _) = oLam
  tmOf (ann _ _) = oAnn

  tyOf : Ty → TyOp
  tyOf base      = oBase
  tyOf (_ ⇒ᵗ _)  = oArr

  -- an `o`-splitting of `t` forces `o` to be `t`'s own label: this is
  -- the uniqueness `fromUnique` asks for, one sort at a time
  tmB→tmOf : (o : TmOp) (t : Raw) → tmB o t → o ≡ tmOf t
  tmB→tmOf oVar .(var _)   (mkVar _   , _) = refl
  tmB→tmOf oApp .(app _ _) (mkApp _ _ , _) = refl
  tmB→tmOf oLam .(lam _ _) (mkLam _ _ , _) = refl
  tmB→tmOf oAnn .(ann _ _) (mkAnn _ _ , _) = refl

  tyB→tyOf : (o : TyOp) (A : Ty) → tyB o A → o ≡ tyOf A
  tyB→tyOf oBase .base      (mkBase   , _) = refl
  tyB→tyOf oArr  .(_ ⇒ᵗ _)  (mkArr _ _ , _) = refl

  -- `tmCase`/`tyCase` denote the partitions themselves: every term is
  -- an `o`-node for exactly one `o`, and likewise every type.
  tmCase : Complete TmOp tmB
  tmCase = fromUnique discrim
             (λ y z t py pz → tmB→tmOf y t py ∙ sym (tmB→tmOf z t pz))
    where
      discrim : Cover (⊕ᴰ TmOp tmB)
      discrim (var n)   _ = oVar , (mkVar n   , λ _ → tt)
      discrim (app u v) _ = oApp , (mkApp u v , λ _ → tt)
      discrim (lam n t) _ = oLam , (mkLam n t , λ _ → tt)
      discrim (ann t A) _ = oAnn , (mkAnn t A , λ _ → tt)

  tyCase : Complete TyOp tyB
  tyCase = fromUnique discrim
             (λ y z A py pz → tyB→tyOf y A py ∙ sym (tyB→tyOf z A pz))
    where
      discrim : Cover (⊕ᴰ TyOp tyB)
      discrim base     _ = oBase , (mkBase  , λ _ → tt)
      discrim (A ⇒ᵗ B) _ = oArr  , (mkArr A B , λ _ → tt)

  -- ================================================================
  -- ... and therefore `⊗-decSplit` is DERIVED, as in `Lambda.Readable`.
  --
  -- The comparison `decBranch` asks for is `(P z ⊢ P y) ⊎ (y ≢ z)`, not
  -- `Discrete`: on the diagonal it must be `idg`, since a `subst` there
  -- would block reduction for every consumer generic in the world.  The
  -- off-diagonal half is uniform by encode-decode -- `TmCode y z` is
  -- `⊥` off the diagonal, so `tmEncode y z` IS the disequality and no
  -- arithmetic on tags appears.
  -- ================================================================

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
    TyCode oArr  oArr  = Unit
    TyCode _     _     = ⊥

    tyRefl : (y : TyOp) → TyCode y y
    tyRefl oBase = tt
    tyRefl oArr  = tt

    tyEncode : (y z : TyOp) → y ≡ z → TyCode y z
    tyEncode y z p = subst (TyCode y) p (tyRefl y)

  -- `tmB-cmp y z` denotes the comparison `decBranch` asks for: on the
  -- diagonal a coercion (`idg`, never a `subst`), off it a refutation of
  -- the tags.  `tyB-cmp` is the same at `ty`.
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
  tyB-cmp oArr  oArr  = inl idg
  tyB-cmp oBase oArr  = inr (tyEncode oBase oArr)
  tyB-cmp oArr  oBase = inr (tyEncode oArr  oBase)

  -- the two partitions, dispatched by which sort the operation lands at
  ⊗-decSplit : (o : TOp) → ⊤G ⊢ Dec⟨ ⊗ˢ o (λ _ → ⊤G) ⟩
  ⊗-decSplit varOp  = decBranch tmB-cmp tmCase oVar
  ⊗-decSplit appOp  = decBranch tmB-cmp tmCase oApp
  ⊗-decSplit lamOp  = decBranch tmB-cmp tmCase oLam
  ⊗-decSplit annOp  = decBranch tmB-cmp tmCase oAnn
  ⊗-decSplit baseOp = decBranch tyB-cmp tyCase oBase
  ⊗-decSplit arrOp  = decBranch tyB-cmp tyCase oArr


  -- Slotwise decisions combine.  Matches on the OPERATION, never on a
  -- term and never on a sum: each alternative names its slots and hands
  -- them to `UniqueSplit`'s `decSlots¹`/`decSlots²`.  `baseOp` is the
  -- degenerate case -- an empty arity has nothing to combine, so the
  -- answer is always yes.  The two-slot family is
  -- `Decidable.Tensor.decSlotsBool`, `Bool`'s own dependent eliminator,
  -- which both `Readable`s used to define for themselves.
  stDecSlots : (o : TOp) (A : (a : TAr o) → TheoryTy ℓ-zero (TSortOf o a))
               (m : Carrier (TResult o)) (sp : TSplit o m)
             → ((a : TAr o) → Dec⟨ A a ⟩ (TParts o m sp a))
             → Dec⟨ ⊗ˢ o A ⟩ m
  stDecSlots varOp  A m sp h = decSlots¹ varOp A m sp tt (λ x _ → x) (h tt)
  stDecSlots baseOp A m sp h = dec-yes (⊗ˢ baseOp A) m (sp , λ ())
  stDecSlots appOp  A m sp h =
    decSlots² appOp A m sp true false decSlotsBool (h true) (h false)
  stDecSlots lamOp  A m sp h =
    decSlots² lamOp A m sp true false decSlotsBool (h true) (h false)
  stDecSlots annOp  A m sp h =
    decSlots² annOp A m sp true false decSlotsBool (h true) (h false)
  stDecSlots arrOp  A m sp h =
    decSlots² arrOp A m sp true false decSlotsBool (h true) (h false)

  stDR : DecReadable stlcFib ℓ-zero
  stDR .splitProp = Split-isProp
  stDR .decSplit  = ⊗-decSplit
  stDR .decSlots  = stDecSlots

  open DecTensor stDR public using (dec-⊗)

  -- ================================================================
  -- DERIVED.  Two views of the SAME world cannot use different head
  -- operations.  That is not a new fact about the representation: it is
  -- the partition's own `exclusive`, pulled back along the maps that
  -- forget the slots -- `Decidable.Tensor.⊗-erase`, the same map
  -- `⊗-miss` applies to a refutation, here applied to a pair of
  -- witnesses.  (It was written out locally as `forget`; it is named
  -- once upstream now.)  The disequality of tags is
  -- `tmEncode`/`tyEncode`, already needed for `tmB-cmp`/`tyB-cmp`.
  --
  -- At `tm`, only the three pairs the inference rules can confuse are
  -- needed; `Unique.agda`'s six impossible cases are these three and
  -- their swaps.  At `ty` there is only one pair, and it is what makes
  -- `Types.base≢arr` a consequence rather than an absurd match.
  -- ================================================================

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

  -- the `ty` sort's only pair, at arbitrary arrow slots
  baseArr-⊥ : {A : (a : TAr arrOp) → TheoryTy ℓ-zero (TSortOf arrOp a)}
            → (tyB oBase & ⊗ˢ arrOp A) ⊢ ⊥G
  baseArr-⊥ {A} =
    exclusive tyCase oBase oArr (tyEncode oBase oArr)
    ∘g &-I &-E₁ (⊗-erase arrOp A ∘g &-E₂)
