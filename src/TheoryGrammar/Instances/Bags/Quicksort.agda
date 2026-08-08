{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Quicksort, plain and at the specification. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Bags.Quicksort (A : Type₀) where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.List
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded
open import TheoryGrammar.View
open import TheoryGrammar.SemanticAction

open import TheoryGrammar.Instances.Bags.QuicksortFunctor A public

open Views bagFib using (Cover; Complete; total; exclusive; completeCase; certifies; fromUnique; caseOf; caseOfᴰ; refine; withView; viewCase; viewCaseᴰ; cover→probe; Probe; _⇛_)
-- (the semantic actions now arrive via `DecFib` in Base)

-- The join, point-free: `lo ++ piv ∷ hi` is two appends and a unit of
-- the listing monoid (`Permutation`).  Nothing quicksort-specific.
specJoin : (piv : A) → (SpecG ⊗' (⌈ piv ∷ [] ⌉ ⊗' SpecG)) ⊢ SpecG
specJoin piv = appendSpec ∘g ⊗-map idg (appendSpec ∘g ⊗-map (unitSpec piv) idg)

module Sort (le : A → A → Bool)
            (leTotal : (x y : A) → le x y Eq.≡ false → le y x Eq.≡ true)
            (leTrans : (x y z : A) → le x y Eq.≡ true → le y z Eq.≡ true
                     → le x z Eq.≡ true)
            where

  open QSF le leTrans public

  -- Partition, keeping the two ordering facts discovered along the
  -- way -- they are what the sorted algebra needs, so they travel with
  -- the parts.  The only place `le` is used.
  partitionOrd : (x : A) (xs : Bag)
    → Σ[ lo ∈ Bag ] Σ[ hi ∈ Bag ] (Ilv lo hi xs × Above x lo × Below x hi)
  partitionOrd x []       = [] , [] , nil , []ᵃ , []ᵇ
  partitionOrd x (y ∷ xs) = go (le y x) Eq.refl (partitionOrd x xs)
    where
      Res : Bag → Type₀
      Res b = Σ[ lo ∈ Bag ] Σ[ hi ∈ Bag ] (Ilv lo hi b × Above x lo × Below x hi)

      go : (bl : Bool) → le y x Eq.≡ bl → Res xs → Res (y ∷ xs)
      go true  e (lo , hi , t , aa , bb) =
        (y ∷ lo) , hi , left t , (e ∷ᵃ aa) , bb
      go false e (lo , hi , t , aa , bb) =
        lo , (y ∷ hi) , right t , aa , (leTotal y x e ∷ᵇ bb)

  -- QUICKSORT'S ONE PRIMITIVE.  Typed as `⇛`, a view morphism: `_⇛_` is
  -- `_⊢_`, and the name records the role.
  splitAround : (x : A)
              → (⌈ x ∷ [] ⌉ ⊗' ⊤G)
              ⇛ ((⊤G & Above x) ⊗' (⌈ x ∷ [] ⌉ ⊗' (⊤G & Below x)))
  splitAround x w ((u , v , s) , h) = go (h true) s
    where
      go : u Eq.≡ x ∷ [] → Ilv u v w
         → ((⊤G & Above x) ⊗' (⌈ x ∷ [] ⌉ ⊗' (⊤G & Below x))) w
      go Eq.refl s' =
        let (lo , hi , t , aa , bb) = partitionOrd x v
            (rest , e1 , e2)        = ilvAssoc s' t
        in ⊗-mk e1 (tt , aa) (⊗-mk e2 Eq.refl (tt , bb))

  -- COERCION, not a primitive: the description's ⊗e carries a Lift and
  -- its arity-family is not `if`-shaped, so the two spellings of one
  -- type need a translation in each direction.
  intoQ : (x : A) → ((⊤G & Above x) ⊗' (⌈ x ∷ [] ⌉ ⊗' (⊤G & Below x)))
                  ⊢ ⟦ ⊗e appop (QG x) ⟧c (λ _ → Unit)
  intoQ x w ((lo , rest , e1) , h) =
    ⊗I {P = λ a → ⟦ QG x a ⟧c (λ _ → Unit)} e1
      (λ { true → tt ; false → lift (h true .snd) })
      (⊗E {P = λ a → if a then ⌈ x ∷ [] ⌉ else (⊤G & Below x)}
          (λ p1 hi e2 pf bb →
             ⊗I {P = λ a → ⟦ QG' x a ⟧c (λ _ → Unit)} e2 (lift pf)
               (λ { true → tt ; false → lift (bb .snd) }))
          (h false))

  -- ... and back again, for the algebras.  Generic in the motive, so
  -- all three share it.
  outQ : (B : Fam) (piv : A)
       → ⟦ ⊗e appop (QG piv) ⟧ᴳ B
       ⊢ ((B tt & Liftg (Above piv))
            ⊗' (⌈ piv ∷ [] ⌉ ⊗' (B tt & Liftg (Below piv))))
  outQ B piv w ((lo , rest , e1) , h) =
    ⊗-mk e1 (h true true , h true false) (go (h false))
    where
      go : ⟦ ⊗e appop (QG' piv) ⟧ᴳ B rest
         → (⌈ piv ∷ [] ⌉ ⊗' (B tt & Liftg (Below piv))) rest
      go ((p1 , hi , e2) , g) =
        ⊗-mk e2 (lower (g true)) (g false true , g false false)

  -- `Sorted.agda` consumes the two ordering witnesses `outQ` hands
  -- back; the algebras below discard them, and `&-E₁` is that discard.
  dropBounds : (B : Fam) (piv : A)
             → ((B tt & Liftg (Above piv))
                  ⊗' (⌈ piv ∷ [] ⌉ ⊗' (B tt & Liftg (Below piv))))
             ⊢ (B tt ⊗' (⌈ piv ∷ [] ⌉ ⊗' B tt))
  dropBounds B piv = ⊗-map &-E₁ (⊗-map idg &-E₁)

  -- The coalgebra, point-free: decompose, then for each pivot partition
  -- around it and inject.
  qcoalg : Coalgᴳ QF (λ _ → ⊤G)
  qcoalg tt =
    caseOf bagCase
      (⊕ᴰ-I _ true ∘g liftg)
      (⊕ᴰ-E (λ x → ⊕ᴰ-I _ false ∘g ⊕ᴰ-I _ x
                      ∘g intoQ x ∘g splitAround x))

  -- The plain algebra: the same composite as `qalgV`, at the constant
  -- carrier.
  nilBag : ⌈ [] ⌉ ⊢ CBag
  nilBag = ⌈⌉-E []

  joinBag : (piv : A) → (CBag ⊗' (⌈ piv ∷ [] ⌉ ⊗' CBag)) ⊢ CBag
  joinBag piv w =
    ⊗E {P = λ b → if b then CBag else (⌈ piv ∷ [] ⌉ ⊗' CBag)} {w = w}
       λ _ _ _ lo inner →
         lo ++ (piv ∷ ⊗E {P = λ b → if b then ⌈ piv ∷ [] ⌉ else CBag}
                         (λ _ _ _ _ hi → hi) inner)

  qalg : AlgC QF (λ _ → Bag)
  qalg tt =
    ⊕ᴰ-E λ { true  → nilBag ∘g lowerg
           ; false → ⊕ᴰ-E λ piv →
               joinBag piv ∘g dropBounds (λ _ → CBag) piv
                           ∘g outQ (λ _ → CBag) piv }

  -- The plain sort, still a term: `Δ Bag` carries the answer and `run`
  -- is the single exit, in a test.
  qsortP : ⊤G ⊢ Δ Bag
  qsortP = intoΔ Bag ∘g hyloᴳ qfGuarded qcoalg qalg tt

  -- ... and the same coalgebra at the specification: `qalg` with
  -- `nilSpec`/`specJoin` swapped in.  Those are ⊢-terms at an indexed
  -- carrier, so the permutation certificate comes from the types.
  qalgV : Algᴳ QF (λ _ → SpecG)
  qalgV tt =
    ⊕ᴰ-E λ { true  → nilSpec ∘g lowerg
           ; false → ⊕ᴰ-E λ piv →
               specJoin piv ∘g dropBounds (λ _ → SpecG) piv
                            ∘g outQ (λ _ → SpecG) piv }

  -- Intrinsically verified quicksort, as a `Cover`: deliberately not
  -- spelled `(m : Bag) → Σ[ out ] Perm out m`, which is already outside.
  quicksortC : Cover SpecG
  quicksortC = hyloᴳ qfGuarded qcoalg qalgV tt

  qsortV : ⊤G ⊢ Δ Bag
  qsortV = tagA Bag ∘g quicksortC
