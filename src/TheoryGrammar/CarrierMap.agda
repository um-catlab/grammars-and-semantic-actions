{-
  CARRIER MAPS: change of theory, at a fixed promodel.

  `ChangeOfTheory` reinterprets along a homomorphism of MODELS.  A
  compiler pass is the same move with the laws dropped: it rewrites the
  term, so it moves the carrier, but it is not a homomorphism.

  A `CarrierMap` is therefore just `hom` -- `ModelHom` minus `homOp`.
  That is enough for the whole additive fragment (`pull`, `pullTerm`,
  and the seven laws below, all `refl`), and for nothing else.

  `homOp` reappears as `SplitPresAt o`: preservation of o-splittings.
  It is what `push⊗` needs, and it is a PER-OPERATION condition -- which
  is the point, since a pass fails it at exactly the operation it
  rewrites.  `ReflectsSplitAt` is `ChangeOfTheory.ReflectsSplit` for a
  promodel, and inverts `push⊗`.

  `Transport` is the free-transport theorem: a carrier map preserving
  ALL splittings transports every inductive grammar, given only a
  transport for each CONSTANT of the description.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.CarrierMap where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
import TheoryGrammar.ChangeOfTheory as CT

private variable ℓS ℓ ℓ' ℓX ℓP ℓA ℓB ℓD ℓM ℓV : Level

-- ==================================================================
-- A carrier map, and preservation of splittings.
-- ==================================================================

record CarrierMap {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
                  (Fib : Fibered σ ℓX ℓP) : Type (ℓ-max ℓS ℓX) where
  field
    hom : (s : S) → Fib .carrier s → Fib .carrier s

open CarrierMap public

-- `homOp` of a `ModelHom`, respelled for a promodel and localised at
-- ONE operation.  A pass satisfies it at every operation it leaves
-- alone and fails it at the one it rewrites.
record SplitPresAt {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
                   {Fib : Fibered σ ℓX ℓP}
                   (h : CarrierMap Fib) (o : σ .ops)
  : Type (ℓ-max ℓ' (ℓ-max ℓX ℓP)) where
  field
    homSplit : (m : Fib .carrier (σ .resultSort o))
             → Fib .Split o m → Fib .Split o (h .hom _ m)
    homParts : (m : Fib .carrier (σ .resultSort o)) (sp : Fib .Split o m)
               (a : σ .arities o)
             → Fib .parts o (h .hom _ m) (homSplit m sp) a
               Eq.≡ h .hom _ (Fib .parts o m sp a)

open SplitPresAt public

-- ==================================================================
-- The bridge to `ChangeOfTheory`: at the CANONICAL promodel (the
-- equational presentation), a `ModelHom` is precisely a carrier map
-- that preserves every splitting.  `homOp` is the whole content of
-- `homSplit`, and `homParts` is then `Eq.refl`.
-- ==================================================================

module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} {M : Model σ ℓX}
         (g : CT.ModelHom M M) where

  ofModelHom : CarrierMap (canonical M)
  ofModelHom .hom = CT.ModelHom.hom g

  ofModelHomPres : (o : σ .ops) → SplitPresAt ofModelHom o
  ofModelHomPres o .homSplit _ (m⃗ , Eq.refl) =
    (λ a → CT.ModelHom.hom g _ (m⃗ a)) , Eq.sym (CT.ModelHom.homOp g o m⃗)
  ofModelHomPres o .homParts _ (m⃗ , Eq.refl) a = Eq.refl

-- ==================================================================
-- Reinterpretation.
-- ==================================================================

module Along {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} {Fib : Fibered σ ℓX ℓP}
             (h : CarrierMap Fib) where

  open FibNotation Fib

  pull : {s : S} → TheoryTy ℓA s → TheoryTy ℓA s
  pull {s = s} B m = B (h .hom s m)

  -- every derivation reinterprets, with no cost and no hypothesis
  pullTerm : {s : S} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s}
           → A ⊢ B → pull A ⊢ pull B
  pullTerm f m x = f _ x

  -- ================================================================
  -- The additive fragment, ON THE NOSE.  No law of `h` is used.
  -- ================================================================

  pull-⊤ : {s : S} → pull (⊤G {s}) ≡ ⊤G
  pull-⊤ = refl

  pull-⊥ : {s : S} → pull (⊥G {s}) ≡ ⊥G
  pull-⊥ = refl

  pull-& : {s : S} (A : TheoryTy ℓA s) (B : TheoryTy ℓB s)
         → pull (A & B) ≡ (pull A & pull B)
  pull-& _ _ = refl

  pull-⊕ : {s : S} (A : TheoryTy ℓA s) (B : TheoryTy ℓB s)
         → pull (A ⊕ B) ≡ (pull A ⊕ pull B)
  pull-⊕ _ _ = refl

  pull-⇒ : {s : S} (A : TheoryTy ℓA s) (B : TheoryTy ℓB s)
         → pull (A ⇒ B) ≡ (pull A ⇒ pull B)
  pull-⇒ _ _ = refl

  pull-⊕ᴰ : {s : S} (Y : Type ℓV) (A : Y → TheoryTy ℓA s)
          → pull (⊕ᴰ Y A) ≡ ⊕ᴰ Y (λ y → pull (A y))
  pull-⊕ᴰ _ _ = refl

  pull-&ᴰ : {s : S} (Y : Type ℓV) (A : Y → TheoryTy ℓA s)
          → pull (&ᴰ Y A) ≡ &ᴰ Y (λ y → pull (A y))
  pull-&ᴰ _ _ = refl

  -- The representable is the ONE former of the additive fragment that
  -- mentions the carrier, and it is exactly the one that does not
  -- transport: `pull ⌈ a ⌉ m` is `hom m Eq.≡ a`, not `m Eq.≡ a`.

  private
    coeTy : {s : S} (B : TheoryTy ℓA s) {x y : Fib .carrier s}
          → x Eq.≡ y → B y → B x
    coeTy B Eq.refl b = b

  -- ================================================================
  -- The multiplicative fragment: lax, and only given preservation.
  -- ================================================================

  module _ (o : σ .ops) (P : SplitPresAt h o)
           {B : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a)} where

    push⊗ : ⊗ˢ o (λ a → pull (B a)) ⊢ pull (⊗ˢ o B)
    push⊗ m (sp , k) =
      P .homSplit m sp , λ a → coeTy (B a) (P .homParts m sp a) (k a)

  -- ... and invertible exactly when `h` REFLECTS splittings: the
  -- discrete Conduché condition of `ChangeOfTheory`, at a promodel.
  ReflectsSplitAt : (o : σ .ops) → Type (ℓ-max ℓ' (ℓ-max ℓX ℓP))
  ReflectsSplitAt o =
    (m : Fib .carrier (σ .resultSort o)) (sp' : Fib .Split o (h .hom _ m))
    → Σ[ sp ∈ Fib .Split o m ]
        ((a : σ .arities o) → Fib .parts o (h .hom _ m) sp' a
                              Eq.≡ h .hom _ (Fib .parts o m sp a))

  module _ (o : σ .ops) (R : ReflectsSplitAt o)
           {B : (a : σ .arities o) → TheoryTy ℓA (σ .sortOf o a)} where

    pull⊗ : pull (⊗ˢ o B) ⊢ ⊗ˢ o (λ a → pull (B a))
    pull⊗ m (sp' , k) =
      R m sp' .fst , λ a → coeTy (B a) (Eq.sym (R m sp' .snd a)) (k a)

  -- ================================================================
  -- FREE TRANSPORT of an inductive grammar.
  --
  -- If `h` preserves every splitting then `μ F` transports along it,
  -- and the ONLY obligations are one per CONSTANT of the description.
  -- The recursion, the shapes, the positions and the index bookkeeping
  -- are all discharged generically.
  -- ================================================================

  module Transport (P : (o : σ .ops) → SplitPresAt h o)
                   (ℓD : Level) (X : Type ℓV) (xs : X → S) where

    open Ind Fib ℓD X xs

    private
      ℓT : Level
      ℓT = ℓ-max ℓ' (ℓ-max ℓX ℓD)

    -- what a description owes: a transport for each constant
    Tr : {s : S} → Functor s → Type ℓT
    Tr (⌜ B ⌝)  = Lift ℓ' (B ⊢ pull B)
    Tr (Var x)  = Unit*
    Tr (⊕e Y G) = (y : Y) → Tr (G y)
    Tr (&e Y G) = (y : Y) → Tr (G y)
    Tr (⊗e o G) = (a : σ .arities o) → Tr (G a)

    private
      coeF : (B : Ix → Type ℓM) {s : S} (F : Functor s)
             {x y : Fib .carrier s} → x Eq.≡ y → ⟦ F ⟧ B y → ⟦ F ⟧ B x
      coeF B F Eq.refl t = t

    mapF : (B : Ix → Type ℓM) {s : S} (F : Functor s) → Tr F
         → (m : Fib .carrier s)
         → ⟦ F ⟧ (λ i → B (i .fst , h .hom _ (i .snd))) m
         → ⟦ F ⟧ B (h .hom s m)
    mapF B (⌜ C ⌝)  tr m (sh , _) = lift (tr .lower _ (sh .lower)) , λ ()
    mapF B (Var x)  tr m (sh , f) = tt* , λ _ → f tt*
    mapF B (⊕e Y G) tr m ((y , sh) , f) =
      (y , mapF B (G y) (tr y) m (sh , f) .fst)
        , mapF B (G y) (tr y) m (sh , f) .snd
    mapF B (&e Y G) tr m (sh , f) =
      (λ y → mapF B (G y) (tr y) m (sh y , λ p → f (y , p)) .fst)
        , λ { (y , p) → mapF B (G y) (tr y) m (sh y , λ p' → f (y , p')) .snd p }
    mapF B (⊗e o G) tr m ((sp , sh) , f) =
      (P o .homSplit m sp , λ a → step a .fst) , λ { (a , p) → step a .snd p }
      where
      step : (a : σ .arities o)
           → ⟦ G a ⟧ B (Fib .parts o (h .hom _ m) (P o .homSplit m sp) a)
      step a = coeF B (G a) (P o .homParts m sp a)
                 (mapF B (G a) (tr a) _ (sh a , λ p → f (a , p)))

    -- the transport itself: a single generic `fold`
    mapμ : (F : (x : X) → Functor (xs x)) → ((x : X) → Tr (F x))
         → (x : X) (m : Fib .carrier (xs x))
         → μ F (x , m) → μ F (x , h .hom _ m)
    mapμ F tr x m d = fold Mot α (x , m) d
      where
      Mot : Ix → Type ℓμ
      Mot i = μ F (i .fst , h .hom _ (i .snd))

      α : (x' : X) (m' : Fib .carrier (xs x')) (sh : Sh (F x') m')
        → ((p : Pos (F x') m' sh) → Mot (nx (F x') m' sh p)) → Mot (x' , m')
      α x' m' sh rc =
        μ-alg F x' (h .hom _ m') (mapF (μ F) (F x') (tr x') m' (sh , rc))
