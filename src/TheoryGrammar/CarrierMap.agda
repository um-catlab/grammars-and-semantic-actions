{-
  REINDEXING BETWEEN PROMODELS -- change of theory with the laws dropped.

  `ChangeOfTheory` reinterprets along a homomorphism of MODELS.  A pass
  rewrites the term, so it moves the carrier and is NOT a homomorphism.
  `Reindex` is therefore `ModelHom` minus `homOp`: just `hom`, with
  `CarrierMap` the endo case.  That suffices for the whole additive
  fragment -- `pull`, `pullTerm`, and the seven laws below, all `refl` --
  and for nothing else; `⌈_⌉` is the one former mentioning the carrier
  and the one that does not commute.

  `homOp` reappears as `SplitPresAt o`, what `push⊗` needs.  It is
  PER-OPERATION, which is the point: a pass fails it at exactly the
  operation it rewrites.  `ReflectsSplitAt` inverts `push⊗`.

  `Transport`: preserving ALL splittings transports every inductive
  grammar, leaving one obligation per CONSTANT of the description.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.CarrierMap where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
import TheoryGrammar.ChangeOfTheory as CT

private variable ℓS ℓ ℓ' ℓX ℓX' ℓP ℓP' ℓA ℓB ℓD ℓM ℓV : Level

-- ==================================================================
-- A carrier map, and preservation of splittings.
-- ==================================================================

-- A reindexing between two promodels over one signature.  A compiler
-- PASS is the special case `Fib' = Fib` (it rewrites within a theory);
-- an ELABORATION lands in a different one, which is what named →
-- de Bruijn is and what the endo-only version could not express.
-- The two promodels may sit at DIFFERENT levels: the glued promodel of
-- `TheoryGrammar.Gluing` has a carrier at the max of its two factors'
-- and projects to each, so level-uniformity here would exclude the only
-- interesting reindexings.  Nothing else in the file used it.
record Reindex {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
               (Fib : Fibered σ ℓX ℓP) (Fib' : Fibered σ ℓX' ℓP')
             : Type (ℓ-max ℓS (ℓ-max ℓX ℓX')) where
  field
    -- a sort-indexed map of carriers, and NO law.  Everything the
    -- additive fragment needs is already here; everything else is
    -- `SplitPresAt`, which is deliberately separate and per-operation.
    hom : (s : S) → Fib .carrier s → Fib' .carrier s

open Reindex public

-- the endo case, under its old name, so every existing pass is unchanged
CarrierMap : {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
           → Fibered σ ℓX ℓP → Type (ℓ-max ℓS ℓX)
CarrierMap Fib = Reindex Fib Fib

-- `SplitPresAt h o` denotes: `h` carries `o`-decompositions forward.
-- It is `homOp` of a `ModelHom`, respelled for a promodel and localised
-- at ONE operation -- a pass satisfies it at every operation it leaves
-- alone and fails it at the one it rewrites.  The two fields say the
-- transported splitting exists and that it holds the transported parts;
-- the second is what makes the first more than a shape coincidence.
record SplitPresAt {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
                   {Fib : Fibered σ ℓX ℓP} {Fib' : Fibered σ ℓX' ℓP'}
                   (h : Reindex Fib Fib') (o : σ .ops)
  : Type (ℓ-max ℓ' (ℓ-max ℓX (ℓ-max ℓX' (ℓ-max ℓP ℓP')))) where
  field
    -- every `o`-splitting of `m` gives one of `hom m`
    homSplit : (m : Fib .carrier (σ .resultSort o))
             → Fib .Split o m → Fib' .Split o (h .hom _ m)
    -- ... whose slots hold exactly the transported parts.  In `Eq`, so
    -- that `push⊗`'s coercion still reduces.
    homParts : (m : Fib .carrier (σ .resultSort o)) (sp : Fib .Split o m)
               (a : σ .arities o)
             → Fib' .parts o (h .hom _ m) (homSplit m sp) a
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

module Along {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
             {Fib : Fibered σ ℓX ℓP} {Fib' : Fibered σ ℓX' ℓP'}
             (h : Reindex Fib Fib') where

  open FibNotation Fib
  module T = FibNotation Fib'

  -- a grammar over the TARGET, reindexed to one over the source
  pull : {s : S} → T.TheoryTy ℓA s → TheoryTy ℓA s
  pull {s = s} B m = B (h .hom s m)

  -- every derivation reinterprets, with no cost and no hypothesis
  pullTerm : {s : S} {A : T.TheoryTy ℓA s} {B : T.TheoryTy ℓB s}
           → A T.⊢ B → pull A ⊢ pull B
  pullTerm f m x = f _ x

  -- The additive fragment, ON THE NOSE.  No law of `h` is used.

  pull-⊤ : {s : S} → pull (T.⊤G {s}) ≡ ⊤G
  pull-⊤ = refl

  pull-⊥ : {s : S} → pull (T.⊥G {s}) ≡ ⊥G
  pull-⊥ = refl

  pull-& : {s : S} (A : T.TheoryTy ℓA s) (B : T.TheoryTy ℓB s)
         → pull (A T.& B) ≡ (pull A & pull B)
  pull-& _ _ = refl

  pull-⊕ : {s : S} (A : T.TheoryTy ℓA s) (B : T.TheoryTy ℓB s)
         → pull (A T.⊕ B) ≡ (pull A ⊕ pull B)
  pull-⊕ _ _ = refl

  pull-⇒ : {s : S} (A : T.TheoryTy ℓA s) (B : T.TheoryTy ℓB s)
         → pull (A T.⇒ B) ≡ (pull A ⇒ pull B)
  pull-⇒ _ _ = refl

  pull-⊕ᴰ : {s : S} (Y : Type ℓV) (A : Y → T.TheoryTy ℓA s)
          → pull (T.⊕ᴰ Y A) ≡ ⊕ᴰ Y (λ y → pull (A y))
  pull-⊕ᴰ _ _ = refl

  pull-&ᴰ : {s : S} (Y : Type ℓV) (A : Y → T.TheoryTy ℓA s)
          → pull (T.&ᴰ Y A) ≡ &ᴰ Y (λ y → pull (A y))
  pull-&ᴰ _ _ = refl

  -- The representable is the ONE former of the additive fragment that
  -- mentions the carrier, and it is exactly the one that does not
  -- transport: `pull ⌈ a ⌉ m` is `hom m Eq.≡ a`, not `m Eq.≡ a`.

  private
    coeTy : {s : S} (B : T.TheoryTy ℓA s) {x y : Fib' .carrier s}
          → x Eq.≡ y → B y → B x
    coeTy B Eq.refl b = b

  -- The multiplicative fragment: lax, and only given preservation.

  module _ (o : σ .ops) (P : SplitPresAt h o)
           {B : (a : σ .arities o) → T.TheoryTy ℓA (σ .sortOf o a)} where

    push⊗ : ⊗ˢ o (λ a → pull (B a)) ⊢ pull (T.⊗ˢ o B)
    push⊗ m (sp , k) =
      P .homSplit m sp , λ a → coeTy (B a) (P .homParts m sp a) (k a)

  -- ... and invertible exactly when `h` REFLECTS splittings: the
  -- discrete Conduché condition of `ChangeOfTheory`, at a promodel.
  ReflectsSplitAt : (o : σ .ops)
                  → Type (ℓ-max ℓ' (ℓ-max ℓX (ℓ-max ℓX' (ℓ-max ℓP ℓP'))))
  ReflectsSplitAt o =
    (m : Fib .carrier (σ .resultSort o)) (sp' : Fib' .Split o (h .hom _ m))
    → Σ[ sp ∈ Fib .Split o m ]
        ((a : σ .arities o) → Fib' .parts o (h .hom _ m) sp' a
                              Eq.≡ h .hom _ (Fib .parts o m sp a))

  module _ (o : σ .ops) (R : ReflectsSplitAt o)
           {B : (a : σ .arities o) → T.TheoryTy ℓA (σ .sortOf o a)} where

    pull⊗ : pull (T.⊗ˢ o B) ⊢ ⊗ˢ o (λ a → pull (B a))
    pull⊗ m (sp' , k) =
      R m sp' .fst , λ a → coeTy (B a) (Eq.sym (R m sp' .snd a)) (k a)


-- ==================================================================
-- FREE TRANSPORT of an inductive grammar.
--
-- If `h` preserves every splitting then `μ F` transports along it,
-- and the ONLY obligations are one per CONSTANT of the description.
-- The recursion, the shapes, the positions and the index bookkeeping
-- are all discharged generically.
-- ==================================================================

module Transport {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} {Fib : Fibered σ ℓX ℓP}
                 (h : CarrierMap Fib)
                 (P : (o : σ .ops) → SplitPresAt h o)
                 (ℓD : Level) (X : Type ℓV) (xs : X → S) where

  open FibNotation Fib
  open Along h
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
