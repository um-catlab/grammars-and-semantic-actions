{-
  HEAPS: THE PARTIAL COMMUTATIVE MONOID.

  A heap is a list of cells; `h₁ ∗ h₂` is defined only when the domains
  are DISJOINT.  As at `Field`, partiality is not a side condition: it is

      Split appop h = Σ u, Σ v, Ilv u v h × (u # v),

  and the `u # v` conjunct is the whole of it.  Dropping exactly that
  conjunct gives `cellFib` -- same carrier, same `parts` -- which DOES
  have a total point (it is `Bags` at `Cell`).  So the obstruction is
  located at one conjunct of one operation.

  Representation: an association LIST, not `Loc → Maybe V`.  A function
  carrier would make heap equality `funExt` and every `refl` test inert;
  a list of cells keeps `⌈ h ⌉` structural and `Diff`/`Fresh`/`_#_`
  Unit/⊥-valued, hence definitionally propositional.

  PRIMITIVE (matching the representation): `Diff`, `Fresh`, `_#_`,
  `IsNil`, `Ilv`, `HeapSplit`, `HeapParts`, `boolΠ`.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Heap.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Unit
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Empty using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Theories.Monoid public
open import TheoryGrammar.Fibered

-- ==================================================================
-- Locations, values, cells, heaps.
--
-- Three values, as `Field` takes 𝔽₃: every table reduces, so the tests
-- are `refl`.  Locations are ℕ, which reduces on numerals.
-- ==================================================================

Loc : Type₀
Loc = ℕ

data Val : Type₀ where
  v0 v1 v2 : Val

Cell : Type₀
Cell = Loc × Val

Heap : Type₀
Heap = List Cell

single : Loc → Val → Heap
single l x = (l , x) ∷ []

-- ==================================================================
-- Apartness.  Every one of these is Unit/⊥-valued, so a proof is a
-- nest of `tt` and any two are definitionally equal -- which is what
-- keeps a splitting's disjointness component from blocking `refl`.
-- ==================================================================

Diff : Loc → Loc → Type₀                          -- PRIMITIVE
Diff zero    zero    = ⊥
Diff zero    (suc _) = Unit
Diff (suc _) zero    = Unit
Diff (suc m) (suc n) = Diff m n

diff-irrefl : (l : Loc) → Diff l l → ⊥            -- PRIMITIVE
diff-irrefl zero    d = d
diff-irrefl (suc l) d = diff-irrefl l d

-- `l` is not a key of `h`
Fresh : Loc → Heap → Type₀                        -- PRIMITIVE
Fresh l []            = Unit
Fresh l ((k , _) ∷ h) = Diff l k × Fresh l h

-- disjoint domains.  THE partiality condition.
infix 4 _#_

_#_ : Heap → Heap → Type₀                         -- PRIMITIVE
[]            # v = Unit
((l , _) ∷ u) # v = Fresh l v × (u # v)

-- transport of disjointness along `Eq`, so nothing downstream needs a
-- Path where an index has to reduce
#-Eq : {u u' v v' : Heap} → u Eq.≡ u' → v Eq.≡ v' → u # v → u' # v'
#-Eq Eq.refl Eq.refl d = d

-- everything is apart from the empty heap
#-nil : (u : Heap) → u # []
#-nil []            = tt
#-nil ((l , _) ∷ u) = tt , #-nil u

-- a cell is never apart from itself: the ONE fact the no-point theorem
-- turns on
#-self : (l : Loc) (x : Val) → single l x # single l x → ⊥
#-self l x ((d , _) , _) = diff-irrefl l d

-- ==================================================================
-- Splittings.  `Ilv` is the interleaving relation, indexed by the
-- WHOLE; `_#_` restricts it to disjoint decompositions.
-- ==================================================================

IsNil : Heap → Type₀                              -- PRIMITIVE
IsNil []      = Unit
IsNil (_ ∷ _) = ⊥

data Ilv : Heap → Heap → Heap → Type₀ where       -- PRIMITIVE
  nil   : Ilv [] [] []
  left  : ∀ {c u v w} → Ilv u v w → Ilv (c ∷ u) v (c ∷ w)
  right : ∀ {c u v w} → Ilv u v w → Ilv u (c ∷ v) (c ∷ w)

ilv-nilL : (v : Heap) → Ilv [] v v
ilv-nilL []      = nil
ilv-nilL (c ∷ v) = right (ilv-nilL v)

ilv-nilR : (u : Heap) → Ilv u [] u
ilv-nilR []      = nil
ilv-nilR (c ∷ u) = left (ilv-nilR u)

-- the left part of an interleaving with an empty right part
ilv-nilL-inv : {v w : Heap} → Ilv [] v w → v Eq.≡ w
ilv-nilL-inv nil       = Eq.refl
ilv-nilL-inv (right p) = Eq.ap (_ ∷_) (ilv-nilL-inv p)

ilv-nilR-inv : {u w : Heap} → Ilv u [] w → u Eq.≡ w
ilv-nilR-inv nil      = Eq.refl
ilv-nilR-inv (left p) = Eq.ap (_ ∷_) (ilv-nilR-inv p)

-- the dependent eliminator for the arity.  `MonAr appop` is `Bool`, so
-- a slot family is a Bool-family; this is its induction principle and
-- the only place `true`/`false` are matched.
boolΠ : ∀ {ℓ} {M : Bool → Type ℓ} → M true → M false → (b : Bool) → M b
boolΠ t f true  = t                               -- PRIMITIVE
boolΠ t f false = f

-- ==================================================================
-- The promodel.
-- ==================================================================

HeapSplit : (o : MonOp) → Heap → Type₀            -- PRIMITIVE
HeapSplit nilop h = IsNil h
HeapSplit appop h = Σ[ u ∈ Heap ] Σ[ v ∈ Heap ] (Ilv u v h × (u # v))

HeapParts : (o : MonOp) (h : Heap) → HeapSplit o h → MonAr o → Heap
HeapParts nilop h sp ()                           -- PRIMITIVE
HeapParts appop h (u , v , _) = boolΠ u v

heapFib : Fibered monoidSig ℓ-zero ℓ-zero
heapFib .carrier _ = Heap
heapFib .Split     = HeapSplit
heapFib .parts     = HeapParts

-- ==================================================================
-- THE FRAGMENT THAT IS TOTAL: the same carrier, the same `parts`, the
-- same `Ilv` -- with the `u # v` conjunct deleted.  This is `Bags` at
-- `Cell`, and it has a lax point (bag union).  Compare `Field`, where
-- the fragment is the same promodel with one OPERATION deleted; here it
-- is one CONJUNCT of one splitting, which is as sharp as the
-- localisation gets.
-- ==================================================================

CellSplit : (o : MonOp) → Heap → Type₀
CellSplit nilop h = IsNil h
CellSplit appop h = Σ[ u ∈ Heap ] Σ[ v ∈ Heap ] Ilv u v h

CellParts : (o : MonOp) (h : Heap) → CellSplit o h → MonAr o → Heap
CellParts nilop h sp ()
CellParts appop h (u , v , _) = boolΠ u v

cellFib : Fibered monoidSig ℓ-zero ℓ-zero
cellFib .carrier _ = Heap
cellFib .Split     = CellSplit
cellFib .parts     = CellParts

_++h_ : Heap → Heap → Heap
[]      ++h v = v
(c ∷ u) ++h v = c ∷ (u ++h v)

ilv-app : (u v : Heap) → Ilv u v (u ++h v)
ilv-app []      v = ilv-nilL v
ilv-app (c ∷ u) v = left (ilv-app u v)

cellPoint : LaxPoint cellFib
cellPoint .op nilop _ = []
cellPoint .op appop f = f true ++h f false
cellPoint .split nilop f = tt
cellPoint .split appop f = f true , f false , ilv-app (f true) (f false)
cellPoint .parts-split nilop f = funExt λ ()
cellPoint .parts-split appop f = funExt (boolΠ refl refl)
