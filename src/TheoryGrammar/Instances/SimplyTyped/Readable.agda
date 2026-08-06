{-
  What this instance owes the generic layers: a `DecReadable`, and the
  `unsplit` law the representables need.

  Three promodel facts -- at most one splitting, decidably so, and
  slotwise decisions combine -- give `dec-⊗`; `Split-isProp` alone gives
  `⊗-refute` and `⊗-merge`; `unsplit` alone gives `⌈⌉-into`/`⌈⌉-from`,
  and with `Split-isProp` also `op-inj`.

  PRIMITIVE inventory of this file: `Split-isProp`, `⊗-decSplit`,
  `stDecSlots`, and the three pairwise disjointness facts.  Everything
  the rest of the instance uses about the representation comes from
  here.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.SimplyTyped.Readable where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_)
import Cubical.Data.Bool.Properties as B
open import Cubical.Data.Unit
open import Cubical.Data.Empty as E using (⊥; ⊥*)

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Decidable
open import TheoryGrammar.Representable
open import TheoryGrammar.Instances.SimplyTyped.Signature
open import TheoryGrammar.Instances.SimplyTyped.Fibered
open import TheoryGrammar.Instances.SimplyTyped.Base

module StReadable (Name : Type₀) where

  open StBase Name

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
  ⊗-decSplit : (o : TOp) → ⊤G ⊢ Dec⟨ ⊗ˢ o (λ _ → ⊤G) ⟩
  ⊗-decSplit varOp  (var n)   _ = dec-yes (⊗ˢ varOp  (λ _ → ⊤G)) _ (mkVar n   , λ _ → tt)
  ⊗-decSplit varOp  (app _ _) _ = dec-no  (⊗ˢ varOp  (λ _ → ⊤G)) _ λ { (() , _) }
  ⊗-decSplit varOp  (lam _ _) _ = dec-no  (⊗ˢ varOp  (λ _ → ⊤G)) _ λ { (() , _) }
  ⊗-decSplit varOp  (ann _ _) _ = dec-no  (⊗ˢ varOp  (λ _ → ⊤G)) _ λ { (() , _) }
  ⊗-decSplit appOp  (var _)   _ = dec-no  (⊗ˢ appOp  (λ _ → ⊤G)) _ λ { (() , _) }
  ⊗-decSplit appOp  (app u v) _ = dec-yes (⊗ˢ appOp  (λ _ → ⊤G)) _ (mkApp u v , λ _ → tt)
  ⊗-decSplit appOp  (lam _ _) _ = dec-no  (⊗ˢ appOp  (λ _ → ⊤G)) _ λ { (() , _) }
  ⊗-decSplit appOp  (ann _ _) _ = dec-no  (⊗ˢ appOp  (λ _ → ⊤G)) _ λ { (() , _) }
  ⊗-decSplit lamOp  (var _)   _ = dec-no  (⊗ˢ lamOp  (λ _ → ⊤G)) _ λ { (() , _) }
  ⊗-decSplit lamOp  (app _ _) _ = dec-no  (⊗ˢ lamOp  (λ _ → ⊤G)) _ λ { (() , _) }
  ⊗-decSplit lamOp  (lam n t) _ = dec-yes (⊗ˢ lamOp  (λ _ → ⊤G)) _ (mkLam n t , λ _ → tt)
  ⊗-decSplit lamOp  (ann _ _) _ = dec-no  (⊗ˢ lamOp  (λ _ → ⊤G)) _ λ { (() , _) }
  ⊗-decSplit annOp  (var _)   _ = dec-no  (⊗ˢ annOp  (λ _ → ⊤G)) _ λ { (() , _) }
  ⊗-decSplit annOp  (app _ _) _ = dec-no  (⊗ˢ annOp  (λ _ → ⊤G)) _ λ { (() , _) }
  ⊗-decSplit annOp  (lam _ _) _ = dec-no  (⊗ˢ annOp  (λ _ → ⊤G)) _ λ { (() , _) }
  ⊗-decSplit annOp  (ann t A) _ = dec-yes (⊗ˢ annOp  (λ _ → ⊤G)) _ (mkAnn t A , λ _ → tt)
  ⊗-decSplit baseOp base      _ = dec-yes (⊗ˢ baseOp (λ _ → ⊤G)) _ (mkBase    , λ _ → tt)
  ⊗-decSplit baseOp (_ ⇒ᵗ _)  _ = dec-no  (⊗ˢ baseOp (λ _ → ⊤G)) _ λ { (() , _) }
  ⊗-decSplit arrOp  base      _ = dec-no  (⊗ˢ arrOp  (λ _ → ⊤G)) _ λ { (() , _) }
  ⊗-decSplit arrOp  (A ⇒ᵗ B)  _ = dec-yes (⊗ˢ arrOp  (λ _ → ⊤G)) _ (mkArr A B , λ _ → tt)

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
