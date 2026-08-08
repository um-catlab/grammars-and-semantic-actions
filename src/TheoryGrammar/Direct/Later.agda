{-
  IS OUR `▷` THE DIRECT-CATEGORY `▷`?

  Short answer: the PRESENTATION is literally identical; the CATEGORY it
  is taken over is not.  Both halves of that sentence are proved below.

  PART A.  The presentation is the same, on the nose.

  `Cubical/Categories/Direct/LaterPresentation.agda` (ccl, branch `lob`)
  isolates what a guarded fixed point needs from a well-founded order --

      record LaterPres (_<_) where
        ▷ : (D → Type ℓ) → D → Type (▷lvl ℓ)
        ⇑ : (x : D) → (∀ y → y < x → A y) → ▷ A x

  -- and gives two instances: `downsetPres`, where `▷ A x` IS
  `∀ y → y < x → A y` and `⇑` is the identity, and `predPres`, where a
  greatest strict predecessor lets `▷ A (suc n)` collapse to `A n`.  It
  then derives `löb`, `löb-fix`, `löb-uniq` by `WFI.induction` /
  `WFI.induction-compute`.

  `TheoryGrammar/Later.agda`'s `WFLater` is `downsetPres` -- not
  analogous to it, EQUAL to it.  `▷-agree`, `löb-agree`, `unfold-agree`
  and `unique-agree` below are all `refl`.  The only difference is
  η-expansion: ours writes `step i (λ j q → rec j q)` where ccl writes
  `f x (⇑ x rec)` and `⇑ x rec = rec`.

  So `TheoryGrammar.Grading`'s `Grade` module does not have a private
  later modality that happens to look like ccl's.  It has ccl's, at the
  downset presentation, at the order `deg i < deg j`.

  PART B.  Which category, though?

  `Direct/StrictDownset.agda` builds `▷` from the sieve

      ↡x  ∋  (f : C [ y , x ])  with  deg y < deg x

  so the hypothesis available in a löb step at `x` is indexed by MAPS
  into `x` of lower degree, not by OBJECTS of lower degree.  Over the
  divisibility category `Div` of `Direct/Divisibility.agda` that reads

      ▷ᵈ A x  ≈  (y : Elt) → ∥ y ≼ x ∥₁ → deg y < deg x → A y
      ▷ᵍ A x  =  (y : Elt) →              deg y < deg x → A y

  and `▷ᵍ → ▷ᵈ` by forgetting the divisibility (`▷ᵍ→▷ᵈ`).  There is no
  map back: `▷ᵈ` never hears about a smaller element that is not a
  factor.  This is precisely the situation `TheoryGrammar/Later.agda`'s
  `▷-mono` already names -- "a FINER order gives a WEAKER modality" --
  and precisely why `Instances/Strings/CYK.agda` needs no infix modality:
  the graded `▷` already dominates it.

  The separation is not hypothetical.  PART C exhibits a `Fibered` with NO
  splittings at all: `Div` is discrete, `↡` is empty at every object, so
  `▷ᵈ` is TERMINAL and its löb proves nothing -- while `▷ᵍ`, over the same
  data, is ordinary strong induction on ℕ and is visibly not terminal.
  Two modalities, one of which is a point and the other of which is not.

  And they DO coincide, exactly when the category is the thin category on
  the degree order itself: `↡fib≅` shows the sieve fibre of
  `WFOrder→Cat Wo` collapses to `y < x`, because there the hom `y ≤ x` is
  a proposition implied by `y < x` and carries nothing.  That is the
  instance `Grammar/Later/Ordered.agda` already uses (`PosetDirect`), and
  `DegPoset` below is that instance for a graded `Fibered`: there the two
  modalities are interderivable, in BOTH directions (`▷ᵈ→▷ᵍ`, `▷ᵍ→▷ᵈ`).

  VERDICT.

    * Our ▷ = ccl's ▷ at the DOWNSET PRESENTATION -- same definition,
      same löb, same unfolding, same uniqueness.  `refl`.
    * Our ▷ = ccl's DIRECT-CATEGORY ▷ for the thin category on the
      DEGREE order.
    * Our ▷ ≠ ccl's direct-category ▷ for the DIVISIBILITY category.
      Ours is strictly stronger, and the gap is exactly "smaller but not
      a factor".  A theorem proved for one transfers to the other only in
      the direction `▷ᵍ → ▷ᵈ`.

  Which one a parser wants is a real question and this file does not
  settle it: `▷ᵈ` is the honest modality (you may only recurse on genuine
  sub-parses, and its löb therefore never needs the degree to be a
  number), while `▷ᵍ` is the one that is cheap to satisfy.  The
  development currently uses `▷ᵍ`.

  ccl NOTE.  `Direct/Base` and `Direct/StrictDownset` are imported for
  real and used.  `Direct/LaterPresentation.agda` is NOT on the branch
  checked out at `~/cubical-categorical-logic` (it lives on `lob` and
  `reedy-dialgebra`), so `LaterPres`, `downsetPres` and the löb module in
  PART A are copied from
  `git show lob:Cubical/Categories/Direct/LaterPresentation.agda`
  verbatim, minus `predPres` (which needs `Direct/StrictMax.agda`, also
  off-branch).
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Direct.Later where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as E using (⊥)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Induction.WellFounded
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open Functor
open import Cubical.Categories.Direct.Base
  using (WFOrder ; WFOrder→Cat ; DirectStr ; mkDirectStr
        ; pullbackWFOrder ; module DirectNotation)
open import Cubical.Categories.Direct.StrictDownset using (↡Psh)

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Grading
open import TheoryGrammar.Later
open import TheoryGrammar.Direct.Divisibility

private variable ℓS ℓ ℓ' ℓD ℓ< ℓM ℓX ℓP : Level

-- PART A. ccl's `LaterPres`, and the identification.

record LaterPres {ℓD ℓ<} {D : Type ℓD} (_<_ : D → D → Type ℓ<) : Typeω where
  field
    ▷lvl : Level → Level
    ▷    : ∀ {ℓ} → (D → Type ℓ) → D → Type (▷lvl ℓ)
    ⇑    : ∀ {ℓ} {A : D → Type ℓ} (x : D) → (∀ y → y < x → A y) → ▷ A x

module LP {D : Type ℓD} {_<_ : D → D → Type ℓ<}
          (wf : WellFounded _<_) (LP : LaterPres _<_) where
  open LaterPres LP public

  module _ {ℓ : Level} {A : D → Type ℓ} (f : ∀ x → ▷ A x → A x) where
    private
      step : ∀ x → (∀ y → y < x → A y) → A x
      step x rec = f x (⇑ x rec)

    löb : ∀ x → A x
    löb = WFI.induction wf step

    löb-fix : ∀ x → löb x ≡ f x (⇑ x (λ y _ → löb y))
    löb-fix = WFI.induction-compute wf step

    löb-uniq : (g : ∀ x → A x)
             → (∀ x → g x ≡ f x (⇑ x (λ y _ → g y)))
             → ∀ x → g x ≡ löb x
    löb-uniq g gfix = WFI.induction wf λ x IH →
      gfix x
      ∙ cong (f x) (cong (⇑ x) (funExt λ y → funExt λ y<x → IH y y<x))
      ∙ sym (löb-fix x)

downsetPres : {D : Type ℓD} (_<_ : D → D → Type ℓ<) → LaterPres _<_
downsetPres {ℓD = ℓD} {ℓ< = ℓ<} _<_ = record
  { ▷lvl = λ ℓ → ℓ-max (ℓ-max ℓD ℓ<) ℓ
  ; ▷    = λ A x → ∀ y → y < x → A y
  ; ⇑    = λ x rec → rec }

-- THEOREM. `TheoryGrammar.Later`'s `WFLater` IS `downsetPres`.

module Agreement {ℓI ℓR : Level} {I : Type ℓI}
                 (_≺_ : I → I → Type ℓR) (≺-wf : WellFounded _≺_) where

  open WFLater _≺_ ≺-wf
  private
    module C = LP ≺-wf (downsetPres _≺_)

  ▷-agree : {A : I → Type ℓM} (i : I) → ▷ A i ≡ C.▷ A i
  ▷-agree i = refl

  next-agree : {A : I → Type ℓM} (f : (i : I) → A i) (i : I)
             → next f i ≡ C.⇑ i (λ j _ → f j)
  next-agree f i = refl

  löb-agree : {A : I → Type ℓM} (step : (i : I) → ▷ A i → A i) (i : I)
            → löb step i ≡ C.löb step i
  löb-agree step i = refl

  unfold-agree : {A : I → Type ℓM} (step : (i : I) → ▷ A i → A i) (i : I)
               → löb-unfold step i ≡ C.löb-fix step i
  unfold-agree step i = refl

  unique-agree : {A : I → Type ℓM} (step : (i : I) → ▷ A i → A i)
                 (f : (i : I) → A i)
                 (hf : (i : I) → f i ≡ step i (λ j _ → f j)) (i : I)
               → löb-unique step f hf i ≡ C.löb-uniq step f hf i
  unique-agree step f hf i = refl

-- PART B.i THE SIEVE FIBRE OVER A THIN DEGREE ORDER COLLAPSES.

module PosetCollapse {ℓD : Level} (Wo : WFOrder ℓD ℓD) where

  private module Wo = WFOrder Wo

  PosetCat : Category ℓD ℓD
  PosetCat = WFOrder→Cat Wo

  PosetDirect : DirectStr PosetCat Wo
  PosetDirect = mkDirectStr PosetCat Wo (λ x → x) (λ f → f)

  open DirectNotation PosetDirect using (_≺_)

  ↡fib : (x y : Wo.D) → Type ℓD
  ↡fib x y = ⟨ ↡Psh PosetDirect x .F-ob y ⟩

  -- THEOREM.  the sieve fibre IS the strict order
  ↡fib≅ : (x y : Wo.D) → Iso (↡fib x y) (y ≺ x)
  ↡fib≅ x y .Iso.fun            = snd
  ↡fib≅ x y .Iso.inv q          = inl q , q
  ↡fib≅ x y .Iso.sec q          = refl
  ↡fib≅ x y .Iso.ret (f , q) i  = Wo.isProp≤ (inl q) f i , q

-- PART B.ii ... AND OVER THE DIVISIBILITY CATEGORY IT DOES NOT.

module DivCompare {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
                  (Fib : Fibered σ ℓX ℓP) (G : Grading Fib) where

  open Div Fib
  open Div.Graded Fib G

  private
    dir = DivDirect↑

  ↡fibᵈ : (x y : Elt) → Type _
  ↡fibᵈ x y = ⟨ ↡Psh dir x .F-ob y ⟩

  -- the sieve fibre, unpacked: a factorisation AND a degree drop
  ↡split : {x y : Elt} → ↡fibᵈ x y → ∥ y ≼ x ∥₁ × (degE y < degE x)
  ↡split (f , q) = f , lower q

  ↡join : {x y : Elt} → ∥ y ≼ x ∥₁ → degE y < degE x → ↡fibᵈ x y
  ↡join f q = f , lift q

  -- the two modalities
  ▷ᵍ : (Elt → Type ℓM) → Elt → Type _
  ▷ᵍ A x = (y : Elt) → y ≺ x → A y

  ▷ᵈ : (Elt → Type ℓM) → Elt → Type _
  ▷ᵈ A x = (y : Elt) → ↡fibᵈ x y → A y

  -- THEOREM.  The graded modality dominates the sieve modality.  This is
  -- `TheoryGrammar.Later`'s `▷-mono` at the inclusion `↡ ⊆ ≺`.
  ▷ᵍ→▷ᵈ : {A : Elt → Type ℓM} (x : Elt) → ▷ᵍ A x → ▷ᵈ A x
  ▷ᵍ→▷ᵈ x r y h = r y (lower (h .snd))

  -- The converse would need `y ≺ x → ∥ y ≼ x ∥₁`: "smaller implies a
  -- factor".  PART C refutes it.

-- PART B.iii WHERE THEY DO AGREE. Instantiate `PosetCollapse` at the
-- degree order of a graded `Fibered`: the thin category whose objects are
-- carrier elements and whose maps are "no bigger in degree".

module DegPoset {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
                (Fib : Fibered σ ℓX ℓP) (G : Grading Fib)
                (isSetElt : isSet (Div.Elt Fib)) where

  open Div Fib
  open Div.Graded Fib G

  private
    ℓE : Level
    ℓE = ℓ-max ℓS ℓX

  DegWo : WFOrder ℓE ℓE
  DegWo = pullbackWFOrder (ℕWFOrder↑ ℓE) isSetElt degE

  open PosetCollapse DegWo public using (PosetCat ; PosetDirect ; ↡fib ; ↡fib≅)

  private
    unliftIso : {ℓ ℓ'' : Level} {A : Type ℓ} → Iso (Lift ℓ'' A) A
    unliftIso .Iso.fun     = lower
    unliftIso .Iso.inv     = lift
    unliftIso .Iso.sec _   = refl
    unliftIso .Iso.ret _   = refl

  -- the sieve fibre of the degree poset IS the graded modality's
  -- hypothesis, on the nose up to the `Lift`
  fibIso : (x y : Elt) → Iso (↡fib x y) (degE y < degE x)
  fibIso x y = compIso (↡fib≅ x y) unliftIso

  ▷ᵈ→▷ᵍ : {A : Elt → Type ℓM} (x : Elt)
        → ((y : Elt) → ↡fib x y → A y) → ((y : Elt) → y ≺ x → A y)
  ▷ᵈ→▷ᵍ x r y q = r y (fibIso x y .Iso.inv q)

  ▷ᵍ→▷ᵈ : {A : Elt → Type ℓM} (x : Elt)
        → ((y : Elt) → y ≺ x → A y) → ((y : Elt) → ↡fib x y → A y)
  ▷ᵍ→▷ᵈ x r y h = r y (fibIso x y .Iso.fun h)

-- PART C. THE SEPARATION.

emptySig : SortedSig Unit ℓ-zero ℓ-zero
emptySig .ops          = Unit
emptySig .arities _    = Unit
emptySig .sortOf _ _   = tt
emptySig .resultSort _ = tt

emptyFib : Fibered emptySig ℓ-zero ℓ-zero
emptyFib .carrier _   = ℕ
emptyFib .Split _ _   = ⊥
emptyFib .parts _ _ ()

emptyG : Grading emptyFib
emptyG .deg _ n        = n
emptyG .Proper _ _ () _
emptyG .deg≤ _ _ ()
emptyG .deg< _ _ ()

module Emp  = Div emptyFib
module EmpG = Div.Graded emptyFib emptyG
module EmpC = DivCompare emptyFib emptyG

isSetElt : isSet Emp.Elt
isSetElt = isSetΣ isSetUnit (λ _ → isSetℕ)

-- no splitting, hence no step ...
no-step : {n m : Emp.Elt} → ¬ (n Emp.◃₁ m)
no-step (Emp.slot o m () a)

-- ... hence the divisibility category is discrete ...
≼→≡ : {n m : Emp.Elt} → n Emp.≼ m → n ≡ m
≼→≡ Emp.nil      = refl
≼→≡ (s Emp.∷ p)  = E.rec (no-step s)

-- ... hence the sieve is empty ...
↡-empty : (x y : Emp.Elt) → ¬ (EmpC.↡fibᵈ x y)
↡-empty x y (f , q) =
  ¬m<m (subst (λ z → EmpG.degE z < EmpG.degE x)
              (PT.rec (isSetElt y x) ≼→≡ f)
              (lower q))

-- ... hence ▷ᵈ is TERMINAL: it has a point at every family and object.
▷ᵈ-terminal : {A : Emp.Elt → Type ℓM} (x : Emp.Elt) → EmpC.▷ᵈ A x
▷ᵈ-terminal x y h = E.rec (↡-empty x y h)

-- while ▷ᵍ at the empty family is NOT inhabited over any nonzero degree:
-- ordinary strong induction on ℕ still has hypotheses.
▷ᵍ-not-terminal : ¬ (EmpC.▷ᵍ {ℓM = ℓ-zero} (λ _ → ⊥) (tt , 1))
▷ᵍ-not-terminal r = r (tt , 0) ≤-refl

-- THEOREM.  There is no comparison `▷ᵈ → ▷ᵍ`, natural or otherwise: one
-- is inhabited where the other is empty.
no-▷ᵈ→▷ᵍ : ¬ ((A : Emp.Elt → Type ℓ-zero) (x : Emp.Elt) → EmpC.▷ᵈ A x → EmpC.▷ᵍ A x)
no-▷ᵈ→▷ᵍ h = ▷ᵍ-not-terminal (h (λ _ → ⊥) (tt , 1) (▷ᵈ-terminal (tt , 1)))
