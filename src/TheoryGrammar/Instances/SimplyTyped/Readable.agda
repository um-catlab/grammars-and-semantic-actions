{-
  What this instance owes the generic layers: a `DecReadable`, and the
  `unsplit` law the representables need.

  Three promodel facts -- at most one splitting, decidably so, and
  slotwise decisions combine -- give `dec-⊗`; `Split-isProp` alone gives
  `⊗-refute` and `⊗-merge`; `unsplit` alone gives `⌈⌉-into`/`⌈⌉-from`,
  and with `Split-isProp` also `op-inj`.

  PRIMITIVE inventory of this file: `Split-isProp`, the two partitions
  (`tmCase`/`tyCase`, one per sort) and `stDecSlots`.  `⊗-decSplit` is
  NOT among them any more -- it is `View.decBranch` at the partitions,
  as in `Lambda.Readable`.  Everything the rest of the instance uses
  about the representation comes from here.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.SimplyTyped.Readable where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
import Cubical.Data.Bool.Properties as B
open import Cubical.Data.Unit
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty as E using (⊥; ⊥*)

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Decidable
open import TheoryGrammar.View
open import TheoryGrammar.Representable
open import TheoryGrammar.Instances.SimplyTyped.Signature
open import TheoryGrammar.Instances.SimplyTyped.Fibered
open import TheoryGrammar.Instances.SimplyTyped.Base

module StReadable (Name : Type₀) where

  open StBase Name
  open Views stlcFib using (Cover; Complete; total; exclusive; completeCase; certifies; fromUnique; decBranch)

  -- PRIMITIVE.  At most one splitting, at either result sort.
  Split-isProp : (o : TOp) (m : Carrier (TResult o)) (p q : TSplit o m) → p ≡ q
  Split-isProp varOp  _ (mkVar _)   (mkVar _)   = refl
  Split-isProp appOp  _ (mkApp _ _) (mkApp _ _) = refl
  Split-isProp lamOp  _ (mkLam _ _) (mkLam _ _) = refl
  Split-isProp annOp  _ (mkAnn _ _) (mkAnn _ _) = refl
  Split-isProp baseOp _ mkBase      mkBase      = refl
  Split-isProp arrOp  _ (mkArr _ _) (mkArr _ _) = refl

  -- `⊗-refute` AND `⊗-merge` now both come from `Precise` -- same
  -- hypothesis, opposite sign.
  open Precise Split-isProp public
  open Repr stlcFib stlcPoint unsplit public using (⌈⌉-into; ⌈⌉-from; op-inj)

  -- Merge two tensors at the same operation and eliminate, in one step:
  -- `⊗-merge` (from unique readability) followed by the tensor's own
  -- elimination rule.  This is how two derivations of the SAME term get
  -- compared slotwise.
  merge2 : (o : TOp) (A B : (a : TAr o) → TheoryTy ℓ-zero (TSortOf o a))
           (C : TheoryTy ℓ-zero (TResult o))
         → MultiHomˢ o (λ a → A a & B a) C
         → (⊗ˢ o A & ⊗ˢ o B) ⊢ C
  merge2 o A B C body = ⊗ˢ-E o {A = λ a → A a & B a} {B = C} body ∘g ⊗-merge o A B

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

  data TmOp : Type₀ where oVar oApp oLam oAnn : TmOp
  data TyOp : Type₀ where oBase oArr : TyOp

  tmB : TmOp → TheoryTy ℓ-zero tm
  tmB oVar = ⊗ˢ varOp (λ _ → ⊤G)
  tmB oApp = ⊗ˢ appOp (λ _ → ⊤G)
  tmB oLam = ⊗ˢ lamOp (λ _ → ⊤G)
  tmB oAnn = ⊗ˢ annOp (λ _ → ⊤G)

  tyB : TyOp → TheoryTy ℓ-zero ty
  tyB oBase = ⊗ˢ baseOp (λ _ → ⊤G)
  tyB oArr  = ⊗ˢ arrOp  (λ _ → ⊤G)

  tmOf : Raw → TmOp
  tmOf (var _)   = oVar
  tmOf (app _ _) = oApp
  tmOf (lam _ _) = oLam
  tmOf (ann _ _) = oAnn

  tyOf : Ty → TyOp
  tyOf base      = oBase
  tyOf (_ ⇒ᵗ _)  = oArr

  tmOf-split : (o : TmOp) (t : Raw) → tmB o t → o ≡ tmOf t
  tmOf-split oVar .(var _)   (mkVar _   , _) = refl
  tmOf-split oApp .(app _ _) (mkApp _ _ , _) = refl
  tmOf-split oLam .(lam _ _) (mkLam _ _ , _) = refl
  tmOf-split oAnn .(ann _ _) (mkAnn _ _ , _) = refl

  tyOf-split : (o : TyOp) (A : Ty) → tyB o A → o ≡ tyOf A
  tyOf-split oBase .base      (mkBase   , _) = refl
  tyOf-split oArr  .(_ ⇒ᵗ _)  (mkArr _ _ , _) = refl

  tmCase : Complete TmOp tmB
  tmCase = fromUnique discrim
             (λ y z t py pz → tmOf-split y t py ∙ sym (tmOf-split z t pz))
    where
      discrim : Cover (⊕ᴰ TmOp tmB)
      discrim (var n)   _ = oVar , (mkVar n   , λ _ → tt)
      discrim (app u v) _ = oApp , (mkApp u v , λ _ → tt)
      discrim (lam n t) _ = oLam , (mkLam n t , λ _ → tt)
      discrim (ann t A) _ = oAnn , (mkAnn t A , λ _ → tt)

  tyCase : Complete TyOp tyB
  tyCase = fromUnique discrim
             (λ y z A py pz → tyOf-split y A py ∙ sym (tyOf-split z A pz))
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

  cmpTm : (y z : TmOp) → (tmB z ⊢ tmB y) ⊎ (y ≡ z → ⊥)
  cmpTm oVar oVar = inl idg
  cmpTm oApp oApp = inl idg
  cmpTm oLam oLam = inl idg
  cmpTm oAnn oAnn = inl idg
  cmpTm oVar oApp = inr (tmEncode oVar oApp)
  cmpTm oVar oLam = inr (tmEncode oVar oLam)
  cmpTm oVar oAnn = inr (tmEncode oVar oAnn)
  cmpTm oApp oVar = inr (tmEncode oApp oVar)
  cmpTm oApp oLam = inr (tmEncode oApp oLam)
  cmpTm oApp oAnn = inr (tmEncode oApp oAnn)
  cmpTm oLam oVar = inr (tmEncode oLam oVar)
  cmpTm oLam oApp = inr (tmEncode oLam oApp)
  cmpTm oLam oAnn = inr (tmEncode oLam oAnn)
  cmpTm oAnn oVar = inr (tmEncode oAnn oVar)
  cmpTm oAnn oApp = inr (tmEncode oAnn oApp)
  cmpTm oAnn oLam = inr (tmEncode oAnn oLam)

  cmpTy : (y z : TyOp) → (tyB z ⊢ tyB y) ⊎ (y ≡ z → ⊥)
  cmpTy oBase oBase = inl idg
  cmpTy oArr  oArr  = inl idg
  cmpTy oBase oArr  = inr (tyEncode oBase oArr)
  cmpTy oArr  oBase = inr (tyEncode oArr  oBase)

  -- the two partitions, dispatched by which sort the operation lands at
  ⊗-decSplit : (o : TOp) → ⊤G ⊢ Dec⟨ ⊗ˢ o (λ _ → ⊤G) ⟩
  ⊗-decSplit varOp  = decBranch cmpTm tmCase oVar
  ⊗-decSplit appOp  = decBranch cmpTm tmCase oApp
  ⊗-decSplit lamOp  = decBranch cmpTm tmCase oLam
  ⊗-decSplit annOp  = decBranch cmpTm tmCase oAnn
  ⊗-decSplit baseOp = decBranch cmpTy tyCase oBase
  ⊗-decSplit arrOp  = decBranch cmpTy tyCase oArr


  -- `Bool`'s own dependent eliminator, under the name it earns here:
  -- assemble a two-slot family from its two slots.  Not a decision.
  private
    mkSlots : {P : Bool → Type₀} → P true → P false → (b : Bool) → P b
    mkSlots = B.elim

  -- Slotwise decisions combine.  Matches on the OPERATION, never on a
  -- term and never on a sum: each alternative names its slots and hands
  -- them to `Precise`'s `decSlots¹`/`decSlots²`.  `baseOp` is the
  -- degenerate case -- an empty arity has nothing to combine, so the
  -- answer is always yes.
  stDecSlots : (o : TOp) (A : (a : TAr o) → TheoryTy ℓ-zero (TSortOf o a))
               (m : Carrier (TResult o)) (sp : TSplit o m)
             → ((a : TAr o) → Dec⟨ A a ⟩ (TParts o m sp a))
             → Dec⟨ ⊗ˢ o A ⟩ m
  stDecSlots varOp  A m sp h = decSlots¹ varOp A m sp tt (λ x _ → x) (h tt)
  stDecSlots baseOp A m sp h = dec-yes (⊗ˢ baseOp A) m (sp , λ ())
  stDecSlots appOp  A m sp h =
    decSlots² appOp A m sp true false mkSlots (h true) (h false)
  stDecSlots lamOp  A m sp h =
    decSlots² lamOp A m sp true false mkSlots (h true) (h false)
  stDecSlots annOp  A m sp h =
    decSlots² annOp A m sp true false mkSlots (h true) (h false)
  stDecSlots arrOp  A m sp h =
    decSlots² arrOp A m sp true false mkSlots (h true) (h false)

  stDR : DecReadable stlcFib ℓ-zero
  stDR .splitProp = Split-isProp
  stDR .decSplit  = ⊗-decSplit
  stDR .decSlots  = stDecSlots

  open DecTensor stDR public using (dec-⊗)

  -- PRIMITIVE.  Distinct operations at the same result sort have
  -- disjoint images.  Only the three `tm` pairs the inference rules can
  -- confuse are needed.
  var∤app : (t : Raw) → IsVar t → IsApp t → ⊥
  var∤app _ (mkVar _) ()

  var∤ann : (t : Raw) → IsVar t → IsAnn t → ⊥
  var∤ann _ (mkVar _) ()

  app∤ann : (t : Raw) → IsApp t → IsAnn t → ⊥
  app∤ann _ (mkApp _ _) ()

  -- ... lifted to the tensors, which is how they get used: two
  -- derivations of the same term cannot use different head operations
  varApp-⊥ : {P : NmG} {A B : TmG} → (VarG P & AppG A B) ⊢ ⊥G
  varApp-⊥ t (x , y) = E.rec (var∤app t (x .fst) (y .fst))

  varAnn-⊥ : {P : NmG} {A : TmG} {Q : TyG} → (VarG P & AnnG A Q) ⊢ ⊥G
  varAnn-⊥ t (x , y) = E.rec (var∤ann t (x .fst) (y .fst))

  appAnn-⊥ : {A B : TmG} {C : TmG} {Q : TyG} → (AppG A B & AnnG C Q) ⊢ ⊥G
  appAnn-⊥ t (x , y) = E.rec (app∤ann t (x .fst) (y .fst))
