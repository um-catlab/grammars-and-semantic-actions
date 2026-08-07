{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  A RECURSIVE SEPARATION-LOGIC PREDICATE, AS A GUARDED `μ`.

  The first PROGRAM over a partial promodel: everything before this built
  the language over heaps, or proved things about it from outside.

  WHY `Array` AND NOT `lseg`.  The classic list segment needs a cell to
  store a LOCATION, and `Base`'s `Val` is three-valued -- chosen so that
  every table reduces and the tests are `refl`.  So pointers are not
  available, and the predicate to write is the other standard one: a
  BLOCK of consecutive locations,

      Array i 0        =  emp
      Array i (suc n)  =  (∃v. i ↦ v)  ∗  Array (suc i) n

  which is the SL "array"/"block" assertion.  It exercises exactly the
  machinery `lseg` would -- a guarded `μ`, a `hyloC` fold, and the append
  lemma -- and the recursion is on the COUNT while the heap shrinks,
  which is the interesting part.

  GUARDEDNESS is the question this file was written to answer.  It
  discharges through `slotProper`, with "the cell is nonempty" playing
  exactly the role "the literal is non-nullable" plays in
  `Strings/KleeneStar` and `Strings/Decomposition`.  The recursive
  occurrence sits at the heap MINUS one cell, and `heapGrading`'s
  `Proper` at slot `false` says the sibling (the cell) owns something.
  So the analogy holds and the certificate is the same shape.

  Note where partiality does NOT interfere: `deg`/`Proper` come from
  `Ilv` alone and never mention `_#_`, so the guardedness argument is
  identical to the one a total promodel would need.  Partiality obstructs
  the total point, not the recursion.
-}
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

-- ==================================================================
-- "location i holds something".
-- ==================================================================

Cellv : ℕ → Gr
Cellv i = ⊕ᴰ Val (λ v → ⌈ single i v ⌉)

-- PRIMITIVE (phase 1): a cell owns exactly one location, so it is
-- nonempty.  This is the `literalNN` of this instance.
cellNonEmp : (i : ℕ) (u : Heap) → Cellv i u → 0 < length u
cellNonEmp i _ (v , Eq.refl) = ≤-refl

-- ==================================================================
-- THE DESCRIPTION.  Recursion on the COUNT; the heap shrinks with it.
-- ==================================================================

arrSlot : ℕ → ℕ → Bool → Functor tt
arrSlot i n true  = ⌜ Cellv i ⌝
arrSlot i n false = Var (suc i , n)

arrF : (x : ℕ × ℕ) → Functor tt
arrF (i , zero)  = ⌜ emp ⌝
arrF (i , suc n) = ⊗e appop (arrSlot i n)

Array : ℕ → ℕ → Gr
Array i n h = μ arrF ((i , n) , h)

-- ==================================================================
-- GUARDEDNESS.  Line for line `decompGuarded` in
-- `Strings/Decomposition`, with `cellNonEmp` for `literalNN`.
-- ==================================================================

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

-- ==================================================================
-- The fixpoint's intro and elim in CONNECTIVE form.  Defined here, not
-- upstream: `⟦_⟧c` takes motives at `ℓSh` while `μ` sits at `ℓμ`, and
-- the two coincide only when `ℓV` and `ℓX` are below `ℓSh` -- true here
-- (`X = ℕ × ℕ`, carrier `Heap`, both `ℓ-zero`) but not generically.  See
-- the note in `TheoryGrammar.Inductive`.
-- ==================================================================

rollg : (x : ℕ × ℕ) → ⟦ arrF x ⟧c (μ arrF) ⊢ (λ h → μ arrF (x , h))
rollg x h t = roll (fromC (arrF x) h t)

unrollg : (x : ℕ × ℕ) → (λ h → μ arrF (x , h)) ⊢ ⟦ arrF x ⟧c (μ arrF)
unrollg x h t = toC (arrF x) h (unroll t)

-- ==================================================================
-- THE CONSTRUCTORS, in the surface connectives.  Phase 2 apart from
-- `liftg`, which is the `Lift` that `⟦ ⌜ A ⌝ ⟧c` puts on constants --
-- pure bookkeeping, exactly as in `Bags/Connectives`.
-- ==================================================================

liftg : {A : Gr} → A ⊢ (λ h → Lift ℓ-zero (A h))
liftg _ = lift

lowerg : {A : Gr} → (λ h → Lift ℓ-zero (A h)) ⊢ A
lowerg _ = lower

array-nil : (i : ℕ) → emp ⊢ Array i 0
array-nil i = rollg (i , 0) ∘g liftg

array-cons : (i n : ℕ) → (Cellv i ∗ Array (suc i) n) ⊢ Array i (suc n)
array-cons i n =
  rollg (i , suc n)
  ∘g ⊗ˢ-map appop
       {A = boolΠ (Cellv i) (Array (suc i) n)}
       {B = λ a → ⟦ arrSlot i n a ⟧c (μ arrF)}
       (boolΠ {M = λ a → boolΠ (Cellv i) (Array (suc i) n) a
                       ⊢ ⟦ arrSlot i n a ⟧c (μ arrF)}
              liftg idg)

array-unroll0 : (i : ℕ) → Array i 0 ⊢ emp
array-unroll0 i = lowerg ∘g unrollg (i , 0)

array-unrollS : (i n : ℕ) → Array i (suc n) ⊢ (Cellv i ∗ Array (suc i) n)
array-unrollS i n =
  ⊗ˢ-map appop
    {A = λ a → ⟦ arrSlot i n a ⟧c (μ arrF)}
    {B = boolΠ (Cellv i) (Array (suc i) n)}
    (boolΠ {M = λ a → ⟦ arrSlot i n a ⟧c (μ arrF)
                    ⊢ boolΠ (Cellv i) (Array (suc i) n) a}
           lowerg idg)
  ∘g unrollg (i , suc n)
