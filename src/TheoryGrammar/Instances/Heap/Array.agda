{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- A RECURSIVE SEPARATION-LOGIC PREDICATE, AS A GUARDED `μ`. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Heap.Array where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.List using (List; []; _∷_; length)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded

open import TheoryGrammar.Instances.Heap.Graded  public
open import TheoryGrammar.Instances.Heap.Precise public

-- nonterminals are indexed by (start location, length)
open Guard heapGraded ℓ-zero (ℕ × ℕ) (λ _ → tt) public

-- "location i holds something".

Cellv : ℕ → Gr
Cellv i = ⊕ᴰ Val (λ v → ⌈ single i v ⌉)

-- PRIMITIVE (phase 1): a cell owns exactly one location, so it is
-- nonempty.  This is the `literalNN` of this instance.
cellNonEmp : (i : ℕ) (u : Heap) → Cellv i u → 0 < length u
cellNonEmp i _ (v , Eq.refl) = ≤-refl

-- THE DESCRIPTION.  Recursion on the COUNT; the heap shrinks with it.

arrSlot : ℕ → ℕ → Bool → Functor tt
arrSlot i n true  = ⌜ Cellv i ⌝
arrSlot i n false = Var (suc i , n)

arrF : (x : ℕ × ℕ) → Functor tt
arrF (i , zero)  = ⌜ emp ⌝
arrF (i , suc n) = ⊗e appop (arrSlot i n)

Array : ℕ → ℕ → Gr
Array i n h = μ arrF ((i , n) , h)

-- GUARDEDNESS.  Line for line `decompGuarded` in
-- `Strings/Decomposition`, with `cellNonEmp` for `literalNN`.

arrGuarded : (x : ℕ × ℕ) → Guarded (arrF x)
arrGuarded (i , zero)  = <⌜⌝ emp
arrGuarded (i , suc n) = ⊗-guard appop (arrSlot i n) go
  where
    go : (h : Heap) (sp : HeapSplit appop h)
         (sh : (a : Bool) → Sh (arrSlot i n a) (HeapParts appop h sp a))
         (a : Bool) (p : Pos (arrSlot i n a) _ (sh a))
       → degIx (nx (arrSlot i n a) _ (sh a) p) < length h
    go h sp sh true ()
    go h (u , v , il , d) sh false p =
      slotProper appop h (u , v , il , d) false
                 (≤Var (suc i , n))
                 (cellNonEmp i u (lower (sh true)))
                 (sh false) p

-- The fixpoint's intro and elim in CONNECTIVE form.

-- `rollg` / `unrollg` come from `Guard` now; the comment above recorded
-- the level coincidence that makes them typecheck here but "not
-- generically", and that turned out to be avoidable -- `Grade`
-- instantiates `Ind` at a description level wide enough to absorb `ℓV` and
-- `ℓX`, and then they are...

-- THE CONSTRUCTORS, in the surface connectives.  Phase 2 apart from
-- `liftg`, which is the `Lift` that `⟦ ⌜ A ⌝ ⟧c` puts on constants --
-- pure bookkeeping, exactly as in `Bags/Connectives`.

array-nil : (i : ℕ) → emp ⊢ Array i 0
array-nil i = rollg arrF (i , 0) ∘g liftg

array-cons : (i n : ℕ) → (Cellv i ∗ Array (suc i) n) ⊢ Array i (suc n)
array-cons i n =
  rollg arrF (i , suc n)
  ∘g ⊗ˢ-map appop
       {A = boolΠ (Cellv i) (Array (suc i) n)}
       {B = λ a → ⟦ arrSlot i n a ⟧c (μ arrF)}
       (boolΠ {M = λ a → boolΠ (Cellv i) (Array (suc i) n) a
                       ⊢ ⟦ arrSlot i n a ⟧c (μ arrF)}
              liftg idg)

array-unroll0 : (i : ℕ) → Array i 0 ⊢ emp
array-unroll0 i = lowerg ∘g unrollg arrF (i , 0)

array-unrollS : (i n : ℕ) → Array i (suc n) ⊢ (Cellv i ∗ Array (suc i) n)
array-unrollS i n =
  ⊗ˢ-map appop
    {A = λ a → ⟦ arrSlot i n a ⟧c (μ arrF)}
    {B = boolΠ (Cellv i) (Array (suc i) n)}
    (boolΠ {M = λ a → ⟦ arrSlot i n a ⟧c (μ arrF)
                    ⊢ boolΠ (Cellv i) (Array (suc i) n) a}
           lowerg idg)
  ∘g unrollg arrF (i , suc n)
