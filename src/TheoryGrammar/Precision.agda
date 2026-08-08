{- PRECISION -- separation logic's, internalised -- AND THE UNIQUENESS
   HYPOTHESES IT IS NOT. -}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Precision where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered

private variable ℓS ℓ ℓ' ℓX ℓP ℓA ℓB : Level

-- PRIMITIVE.  Transport of a family along a STRICT equality: the one
-- match in this file, and it is `Eq` rather than a path so that every
-- payload it moves still reduces.
coeEq : {X : Type ℓ} (P : X → Type ℓ') {x y : X} → x Eq.≡ y → P x → P y
coeEq P Eq.refl p = p

module Prec {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (Fib : Fibered σ ℓX ℓP) where

  open FibNotation Fib

  -- 1.  THE TWO FORMS OF PRECISION.

  -- POINTWISE: among the splittings whose slot `i` satisfies `A`, that
  -- slot is unique.  This is `splitProp` with `A` inserted.
  PreciseP : (o : σ .ops) (i : σ .arities o)
           → TheoryTy ℓA (σ .sortOf o i) → Type (ℓ-max ℓX (ℓ-max ℓP ℓA))
  PreciseP o i A =
    (m : Fib .carrier (σ .resultSort o)) (p q : Fib .Split o m)
    → A (Fib .parts o m p i) → A (Fib .parts o m q i)
    → Fib .parts o m p i Eq.≡ Fib .parts o m q i

  -- The tensor with a DISTINGUISHED slot: `A` at `i`, `B` everywhere.
  -- The `⊤` this leaves at slot `i` of `B` costs nothing, and it is
  -- what lets the statement be n-ary without deciding slot equality.
  ⊗at : (o : σ .ops) (i : σ .arities o)
      → TheoryTy ℓA (σ .sortOf o i)
      → ((a : σ .arities o) → TheoryTy ℓB (σ .sortOf o a))
      → TheoryTy (ℓ-max ℓP (ℓ-max ℓ' (ℓ-max ℓA ℓB))) (σ .resultSort o)
  ⊗at o i A B m =
    Σ[ sp ∈ Fib .Split o m ]
      (A (Fib .parts o m sp i) × ((a : σ .arities o) → B a (Fib .parts o m sp a)))

  -- INTERNAL: `⊗` distributes over `&` at a precise left argument.  A
  -- `⊢`-term; no splitting is mentioned.
  PreciseI : (ℓB : Level) (o : σ .ops) (i : σ .arities o)
             (A : TheoryTy ℓA (σ .sortOf o i))
           → Type (ℓ-max ℓX (ℓ-max ℓP (ℓ-max ℓ' (ℓ-max ℓA (ℓ-suc ℓB)))))
  PreciseI ℓB o i A =
    (B C : (a : σ .arities o) → TheoryTy ℓB (σ .sortOf o a))
    → ((⊗at o i A B) & (⊗at o i A C)) ⊢ ⊗at o i A (λ a → B a & C a)

  -- 2.  THE HYPOTHESES ON THE SUBSTRATE, in decreasing strength.

  -- at most one splitting: unique readability, `Decidable.Tensor`'s
  -- `UniqueSplit` hypothesis
  SplitPropAt : (o : σ .ops) → Type (ℓ-max ℓX ℓP)
  SplitPropAt o = (m : Fib .carrier (σ .resultSort o))
                  (p q : Fib .Split o m) → p ≡ q

  SplitProp : Type (ℓ-max ℓ (ℓ-max ℓX ℓP))
  SplitProp = (o : σ .ops) → SplitPropAt o

  -- at most one TUPLE OF PARTS -- the splittings may still differ
  PartsPropAt : (o : σ .ops) → Type (ℓ-max ℓX (ℓ-max ℓP ℓ'))
  PartsPropAt o = (m : Fib .carrier (σ .resultSort o)) (p q : Fib .Split o m)
                  (a : σ .arities o)
                → Fib .parts o m p a Eq.≡ Fib .parts o m q a

  PartsProp : Type (ℓ-max ℓ (ℓ-max ℓX (ℓ-max ℓP ℓ')))
  PartsProp = (o : σ .ops) → PartsPropAt o

  -- ... and the gap between the two: a splitting carries no more
  -- information than its parts
  PartsFaithfulAt : (o : σ .ops) → Type (ℓ-max ℓX (ℓ-max ℓP ℓ'))
  PartsFaithfulAt o = (m : Fib .carrier (σ .resultSort o)) (p q : Fib .Split o m)
                    → ((a : σ .arities o) → Fib .parts o m p a Eq.≡ Fib .parts o m q a)
                    → p ≡ q

  -- RELATIVISED: slot `i` determines every slot.
  SlotDet : (o : σ .ops) (i : σ .arities o) → Type (ℓ-max ℓX (ℓ-max ℓP ℓ'))
  SlotDet o i = (m : Fib .carrier (σ .resultSort o)) (p q : Fib .Split o m)
              → Fib .parts o m p i Eq.≡ Fib .parts o m q i
              → (a : σ .arities o) → Fib .parts o m p a Eq.≡ Fib .parts o m q a

  -- 3.  THE DEGENERATE CASE: `splitProp` makes EVERYTHING precise.

  -- one operation at a time -- an instance whose partiality sits at one
  -- operation needs exactly these
  splitPropAt→partsPropAt : (o : σ .ops) → SplitPropAt o → PartsPropAt o
  splitPropAt→partsPropAt o sp m p q a =
    Eq.pathToEq (funExt⁻ (cong (Fib .parts o m) (sp m p q)) a)

  partsPropAt→slotDet : (o : σ .ops) (i : σ .arities o) → PartsPropAt o → SlotDet o i
  partsPropAt→slotDet o i pp m p q _ = pp m p q

  partsPropAt→preciseP : (o : σ .ops) (i : σ .arities o)
                         (A : TheoryTy ℓA (σ .sortOf o i))
                       → PartsPropAt o → PreciseP o i A
  partsPropAt→preciseP o i A pp m p q _ _ = pp m p q i

  -- ... and uniformly in the operation
  splitProp→partsProp : SplitProp → PartsProp
  splitProp→partsProp sp o = splitPropAt→partsPropAt o (sp o)

  partsProp→slotDet : PartsProp → (o : σ .ops) (i : σ .arities o) → SlotDet o i
  partsProp→slotDet pp o i = partsPropAt→slotDet o i (pp o)

  partsProp→preciseP : PartsProp → (o : σ .ops) (i : σ .arities o)
                       (A : TheoryTy ℓA (σ .sortOf o i)) → PreciseP o i A
  partsProp→preciseP pp o i A = partsPropAt→preciseP o i A (pp o)

  -- 4. POINTWISE ⟹ INTERNAL, given `SlotDet`.

  preciseP→preciseI : (ℓB : Level) (o : σ .ops) (i : σ .arities o)
                      (A : TheoryTy ℓA (σ .sortOf o i))
                    → SlotDet o i → PreciseP o i A → PreciseI ℓB o i A
  preciseP→preciseI ℓB o i A det pr B C m ((p , x , h) , (q , y , k)) =
    p , x , λ a → h a , coeEq (C a) (det m q p (pr m q p y x) a) (k a)

  partsPropAt→preciseI : (ℓB : Level) (o : σ .ops) (i : σ .arities o)
                         (A : TheoryTy ℓA (σ .sortOf o i))
                       → PartsPropAt o → PreciseI ℓB o i A
  partsPropAt→preciseI ℓB o i A pp =
    preciseP→preciseI ℓB o i A (partsPropAt→slotDet o i pp)
                               (partsPropAt→preciseP o i A pp)

  partsProp→preciseI : PartsProp → (ℓB : Level) (o : σ .ops) (i : σ .arities o)
                       (A : TheoryTy ℓA (σ .sortOf o i)) → PreciseI ℓB o i A
  partsProp→preciseI pp ℓB o i A = partsPropAt→preciseI ℓB o i A (pp o)

  splitProp→preciseI : SplitProp → (ℓB : Level) (o : σ .ops) (i : σ .arities o)
                       (A : TheoryTy ℓA (σ .sortOf o i)) → PreciseI ℓB o i A
  splitProp→preciseI sp = partsProp→preciseI (splitProp→partsProp sp)

  -- 5. A REPRESENTABLE IS POINTWISE PRECISE, always.

  preciseP-⌈⌉ : (o : σ .ops) (i : σ .arities o)
                (c : Fib .carrier (σ .sortOf o i)) → PreciseP o i ⌈ c ⌉
  preciseP-⌈⌉ o i c m p q x y = x Eq.∙ Eq.sym y

  -- 6. IS `splitProp` "⊤ IS PRECISE"? `PreciseI` at `⊤G` has a trivial
  -- focused component, so it is the MERGE rule: two views of one composite
  -- merge slotwise.

  MergeAt : (ℓB : Level) (o : σ .ops)
          → Type (ℓ-max ℓX (ℓ-max ℓP (ℓ-max ℓ' (ℓ-suc ℓB))))
  MergeAt ℓB o = (B C : (a : σ .arities o) → TheoryTy ℓB (σ .sortOf o a))
               → ((⊗ˢ o B) & (⊗ˢ o C)) ⊢ ⊗ˢ o (λ a → B a & C a)

  preciseI-⊤→merge : (ℓB : Level) (o : σ .ops) (i : σ .arities o)
                   → PreciseI ℓB o i ⊤G → MergeAt ℓB o
  preciseI-⊤→merge ℓB o i pr B C m ((p , h) , (q , k)) = r .fst , r .snd .snd
    where r = pr B C m ((p , tt , h) , (q , tt , k))

  merge→preciseI-⊤ : (ℓB : Level) (o : σ .ops) (i : σ .arities o)
                   → MergeAt ℓB o → PreciseI ℓB o i ⊤G
  merge→preciseI-⊤ ℓB o i mg B C m ((p , _ , h) , (q , _ , k)) =
    r .fst , tt , r .snd
    where r = mg B C m ((p , h) , (q , k))

  -- ... and the merge rule IS `PartsPropAt`, in both directions.
  merge→partsProp : (o : σ .ops) → MergeAt ℓX o → PartsPropAt o
  merge→partsProp o mg m p q a = Eq.sym (r .snd a .fst) Eq.∙ r .snd a .snd
    where r = mg (λ b → ⌈ Fib .parts o m p b ⌉) (λ b → ⌈ Fib .parts o m q b ⌉) m
                 ((p , λ _ → Eq.refl) , (q , λ _ → Eq.refl))

  partsProp→merge : (ℓB : Level) (o : σ .ops) → PartsPropAt o → MergeAt ℓB o
  partsProp→merge ℓB o pp B C m ((p , h) , (q , k)) =
    p , λ a → h a , coeEq (C a) (pp m q p a) (k a)

  -- The pointwise form of the same coincidence, with nothing to prove:
  -- `PartsPropAt` IS "`⊤` is pointwise precise at every slot".
  preciseP-⊤→partsProp : (o : σ .ops)
                       → ((i : σ .arities o) → PreciseP o i ⊤G) → PartsPropAt o
  preciseP-⊤→partsProp o pr m p q a = pr a m p q tt tt

  partsProp→preciseP-⊤ : (o : σ .ops) → PartsPropAt o
                       → (i : σ .arities o) → PreciseP o i ⊤G
  partsProp→preciseP-⊤ o pp i m p q _ _ = pp m p q i

  -- THE ONE STEP THAT IS NOT FREE.  Everything above says `⊤`-precision
  -- is `PartsPropAt`; getting back to `SplitPropAt` needs the splitting
  -- to be determined by its parts, and nothing in `Fibered` says so.
  partsProp→splitProp : (o : σ .ops) → PartsFaithfulAt o
                      → PartsPropAt o → SplitPropAt o
  partsProp→splitProp o pf pp m p q = pf m p q (pp m p q)

  -- 7. THE BINARY READING.

  module Binary (o : σ .ops) (i j : σ .arities o)
                (slotΠ : ∀ {ℓM} {M : σ .arities o → Type ℓM}
                       → M i → M j → (a : σ .arities o) → M a)
                (slotΠ-i : ∀ {ℓM} {M : σ .arities o → Type ℓM} (x : M i) (y : M j)
                         → slotΠ {M = M} x y i Eq.≡ x)
                (slotΠ-j : ∀ {ℓM} {M : σ .arities o → Type ℓM} (x : M i) (y : M j)
                         → slotΠ {M = M} x y j Eq.≡ y)
                where

    private
      TyM : (ℓA : Level) → σ .arities o → Type (ℓ-max ℓX (ℓ-suc ℓA))
      TyM ℓA a = TheoryTy ℓA (σ .sortOf o a)

    -- the separating conjunction of the instance, generically
    _⊛_ : {ℓA : Level} → TheoryTy ℓA (σ .sortOf o i) → TheoryTy ℓA (σ .sortOf o j)
        → TheoryTy (ℓ-max ℓP (ℓ-max ℓ' ℓA)) (σ .resultSort o)
    _⊛_ {ℓA} A B = ⊗ˢ o (slotΠ {M = TyM ℓA} A B)

    infixr 20 _⊛_

    PreciseB : {ℓA : Level} → TheoryTy ℓA (σ .sortOf o i)
             → Type (ℓ-max ℓX (ℓ-max ℓP (ℓ-max ℓ' (ℓ-suc ℓA))))
    PreciseB {ℓA} A = (B C : TheoryTy ℓA (σ .sortOf o j))
                    → ((A ⊛ B) & (A ⊛ C)) ⊢ (A ⊛ (B & C))

    -- ... and it is the n-ary statement, read at this arity.
    into : {ℓA : Level} (A : TheoryTy ℓA (σ .sortOf o i)) (B : TheoryTy ℓA (σ .sortOf o j))
         → (A ⊛ B) ⊢ ⊗at o i A (slotΠ {M = TyM ℓA} A B)
    into {ℓA} A B m (sp , h) =
        sp
      , coeEq (λ G → G (Fib .parts o m sp i)) (slotΠ-i {M = TyM ℓA} A B) (h i)
      , h

    out : {ℓA : Level} (A : TheoryTy ℓA (σ .sortOf o i))
          (B C : TheoryTy ℓA (σ .sortOf o j))
        → ⊗at o i A (λ a → slotΠ {M = TyM ℓA} A B a & slotΠ {M = TyM ℓA} A C a)
          ⊢ (A ⊛ (B & C))
    out {ℓA} A B C m (sp , x , k) =
      sp , slotΠ {M = λ a → slotΠ {M = TyM ℓA} A (B & C) a (Fib .parts o m sp a)} xi kj
      where
        xi : slotΠ {M = TyM ℓA} A (B & C) i (Fib .parts o m sp i)
        xi = coeEq (λ G → G (Fib .parts o m sp i))
                   (Eq.sym (slotΠ-i {M = TyM ℓA} A (B & C))) x
        kj : slotΠ {M = TyM ℓA} A (B & C) j (Fib .parts o m sp j)
        kj = coeEq (λ G → G (Fib .parts o m sp j))
                   (Eq.sym (slotΠ-j {M = TyM ℓA} A (B & C)))
                   ( coeEq (λ G → G (Fib .parts o m sp j))
                           (slotΠ-j {M = TyM ℓA} A B) (k j .fst)
                   , coeEq (λ G → G (Fib .parts o m sp j))
                           (slotΠ-j {M = TyM ℓA} A C) (k j .snd) )

    preciseI→preciseB : {ℓA : Level} (A : TheoryTy ℓA (σ .sortOf o i))
                      → PreciseI ℓA o i A → PreciseB A
    preciseI→preciseB {ℓA} A pr B C m (x , y) =
      out A B C m (pr (slotΠ {M = TyM ℓA} A B) (slotΠ {M = TyM ℓA} A C) m
                      (into A B m x , into A C m y))

    -- the composite the instances actually use
    preciseP→preciseB : {ℓA : Level} (A : TheoryTy ℓA (σ .sortOf o i))
                      → SlotDet o i → PreciseP o i A → PreciseB A
    preciseP→preciseB {ℓA} A det pr =
      preciseI→preciseB A (preciseP→preciseI ℓA o i A det pr)
