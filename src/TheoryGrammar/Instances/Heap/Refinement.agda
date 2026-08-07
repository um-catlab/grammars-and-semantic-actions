{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- HEAPS ARE A REFINEMENT ALGEBRA -- the separation-logic CROSS-SPLIT,
   and the reason the generic statement was written on `Split`/`parts`
   rather than on `op`.

   `Heap` has no total composition, so the usual formulation ("if
   h₁ ∗ h₂ = k₁ ∗ k₂ then there are four heaps with ...") carries four
   definedness side conditions.  Here there is nothing to say: a
   splitting IS an `Ilv` together with `_#_`, the interleaving half is
   the bag argument verbatim, and the four disjointness obligations are
   all sub-heap restrictions of the TWO that were given.

   `Cross`/`cross` below are `Bags/Refinement`'s verbatim.  They are not
   shared because `Ilv` is declared separately at each carrier; the fix
   is one interleaving relation, generic in the element type.

   MAIN: `cross` (the matrix), `heapRefinable` (`Refinement.Refinable`
   at heap composition), and the six apartness restrictions
   `freshSubˡ/ʳ`, `#-subLˡ/ʳ`, `#-subRˡ/ʳ`.

   PRIMITIVE: none new -- the six restrictions are inductions on `Ilv`. -}
module TheoryGrammar.Instances.Heap.Refinement where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit
open import Cubical.Data.List using (List; []; _∷_)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Refinement
open import TheoryGrammar.Instances.Heap.Base public

open Refine heapFib

appHom : HomOp tt
appHom .op⋆    = appop
appHom .resH   = Eq.refl
appHom .argH _ = Eq.refl

-- ==================================================================
-- Sub-heaps of apart heaps are apart.  Six inductions on `Ilv`, no new
-- match on `Eq`.
--
-- Each is stated at ONE factor rather than at both: the callers below
-- want a single side, and a conjunctive conclusion would only be
-- projected away again at every use.  `ˡ` is the left factor of the
-- interleaving, `ʳ` the right.
-- ==================================================================

-- `l` is fresh for the whole, hence for the left factor ...
freshSubˡ : ∀ {a b v l} → Ilv a b v → Fresh l v → Fresh l a
freshSubˡ nil       _        = tt
freshSubˡ (left p)  (d , fr) = d , freshSubˡ p fr
freshSubˡ (right p) (_ , fr) = freshSubˡ p fr

-- ... and for the right factor
freshSubʳ : ∀ {a b v l} → Ilv a b v → Fresh l v → Fresh l b
freshSubʳ nil       _        = tt
freshSubʳ (left p)  (_ , fr) = freshSubʳ p fr
freshSubʳ (right p) (d , fr) = d , freshSubʳ p fr

-- apartness restricted along a splitting of its LEFT argument
#-subLˡ : ∀ {a b u v} → Ilv a b u → u # v → a # v
#-subLˡ nil       _        = tt
#-subLˡ (left p)  (fr , d) = fr , #-subLˡ p d
#-subLˡ (right p) (_  , d) = #-subLˡ p d

#-subLʳ : ∀ {a b u v} → Ilv a b u → u # v → b # v
#-subLʳ nil       _        = tt
#-subLʳ (left p)  (_  , d) = #-subLʳ p d
#-subLʳ (right p) (fr , d) = fr , #-subLʳ p d

-- apartness restricted along a splitting of its RIGHT argument
#-subRˡ : ∀ {a b v} → Ilv a b v → (u : Heap) → u # v → u # a
#-subRˡ q []            _        = tt
#-subRˡ q ((l , x) ∷ u) (fr , d) = freshSubˡ q fr , #-subRˡ q u d

#-subRʳ : ∀ {a b v} → Ilv a b v → (u : Heap) → u # v → u # b
#-subRʳ q []            _        = tt
#-subRʳ q ((l , x) ∷ u) (fr , d) = freshSubʳ q fr , #-subRʳ q u d

-- ==================================================================
-- The matrix.  Interleaving only -- disjointness is bolted on after,
-- because it is not an inductive invariant but a restriction.
-- ==================================================================

record Cross (u₁ v₁ u₂ v₂ : Heap) : Type₀ where
  field
    c₀₀ c₀₁ c₁₀ c₁₁ : Heap
    row₀ : Ilv c₀₀ c₀₁ u₁
    row₁ : Ilv c₁₀ c₁₁ v₁
    col₀ : Ilv c₀₀ c₁₀ u₂
    col₁ : Ilv c₀₁ c₁₁ v₂

open Cross public

cross : ∀ {u₁ v₁ u₂ v₂ w} → Ilv u₁ v₁ w → Ilv u₂ v₂ w → Cross u₁ v₁ u₂ v₂
cross nil nil =
  record { c₀₀ = [] ; c₀₁ = [] ; c₁₀ = [] ; c₁₁ = []
         ; row₀ = nil ; row₁ = nil ; col₀ = nil ; col₁ = nil }
cross (left {c = y} d₁) (left d₂) =
  record { c₀₀ = y ∷ r .c₀₀ ; c₀₁ = r .c₀₁ ; c₁₀ = r .c₁₀ ; c₁₁ = r .c₁₁
         ; row₀ = left (r .row₀) ; row₁ = r .row₁
         ; col₀ = left (r .col₀) ; col₁ = r .col₁ }
  where r = cross d₁ d₂
cross (left {c = y} d₁) (right d₂) =
  record { c₀₀ = r .c₀₀ ; c₀₁ = y ∷ r .c₀₁ ; c₁₀ = r .c₁₀ ; c₁₁ = r .c₁₁
         ; row₀ = right (r .row₀) ; row₁ = r .row₁
         ; col₀ = r .col₀ ; col₁ = left (r .col₁) }
  where r = cross d₁ d₂
cross (right {c = y} d₁) (left d₂) =
  record { c₀₀ = r .c₀₀ ; c₀₁ = r .c₀₁ ; c₁₀ = y ∷ r .c₁₀ ; c₁₁ = r .c₁₁
         ; row₀ = r .row₀ ; row₁ = left (r .row₁)
         ; col₀ = right (r .col₀) ; col₁ = r .col₁ }
  where r = cross d₁ d₂
cross (right {c = y} d₁) (right d₂) =
  record { c₀₀ = r .c₀₀ ; c₀₁ = r .c₀₁ ; c₁₀ = r .c₁₀ ; c₁₁ = y ∷ r .c₁₁
         ; row₀ = r .row₀ ; row₁ = right (r .row₁)
         ; col₀ = r .col₀ ; col₁ = right (r .col₁) }
  where r = cross d₁ d₂

-- ==================================================================
-- REFINABILITY.  Each of the four cells' disjointness is one `#-subL`
-- followed by one `#-subR`: restrict a given apartness to a sub-heap
-- on the left, then on the right.
-- ==================================================================

heapRefinable : Refinable appHom appHom
heapRefinable h (u₁ , v₁ , e₁ , d₁) (u₂ , v₂ , e₂ , d₂) = R
  where
  r = cross e₁ e₂

  -- from `u₂ # v₂`: the two ROWS
  #row₀ : r .c₀₀ # r .c₀₁
  #row₀ = #-subRˡ (r .col₁) (r .c₀₀) (#-subLˡ (r .col₀) d₂)
  #row₁ : r .c₁₀ # r .c₁₁
  #row₁ = #-subRʳ (r .col₁) (r .c₁₀) (#-subLʳ (r .col₀) d₂)

  -- from `u₁ # v₁`: the two COLUMNS
  #col₀ : r .c₀₀ # r .c₁₀
  #col₀ = #-subRˡ (r .row₁) (r .c₀₀) (#-subLˡ (r .row₀) d₁)
  #col₁ : r .c₀₁ # r .c₁₁
  #col₁ = #-subRʳ (r .row₁) (r .c₀₁) (#-subLʳ (r .row₀) d₁)

  R : Refinement appHom appHom h (u₁ , v₁ , e₁ , d₁) (u₂ , v₂ , e₂ , d₂)
  R .cell true  true  = r .c₀₀
  R .cell true  false = r .c₀₁
  R .cell false true  = r .c₁₀
  R .cell false false = r .c₁₁
  R .rowSplit true  = r .c₀₀ , r .c₀₁ , r .row₀ , #row₀
  R .rowSplit false = r .c₁₀ , r .c₁₁ , r .row₁ , #row₁
  R .rowCell true  true  = Eq.refl
  R .rowCell true  false = Eq.refl
  R .rowCell false true  = Eq.refl
  R .rowCell false false = Eq.refl
  R .colSplit true  = r .c₀₀ , r .c₁₀ , r .col₀ , #col₀
  R .colSplit false = r .c₀₁ , r .c₁₁ , r .col₁ , #col₁
  R .colCell true  true  = Eq.refl
  R .colCell true  false = Eq.refl
  R .colCell false true  = Eq.refl
  R .colCell false false = Eq.refl

-- ==================================================================
-- It computes, at numerals: `0↦v0 ∗ 1↦v1` split the two ways round has
-- both off-diagonal cells inhabited and the diagonal empty.
-- ==================================================================

private
  h₂ : Heap
  h₂ = (0 , v0) ∷ (1 , v1) ∷ []

  pLR : SplitH appHom h₂
  pLR = single 0 v0 , single 1 v1 , left (right nil) , (tt , tt) , tt

  pRL : SplitH appHom h₂
  pRL = single 1 v1 , single 0 v0 , right (left nil) , (tt , tt) , tt

  Rh : Refinement appHom appHom h₂ pLR pRL
  Rh = heapRefinable h₂ pLR pRL

  _ : Rh .cell true true Eq.≡ []
  _ = Eq.refl
  _ : Rh .cell true false Eq.≡ single 0 v0
  _ = Eq.refl
  _ : Rh .cell false true Eq.≡ single 1 v1
  _ = Eq.refl
  _ : Rh .cell false false Eq.≡ []
  _ = Eq.refl
