{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- SEPARATION LOGIC AS THE GENERIC CONNECTIVES, AND PARTIALITY AS A THEOREM
   OF THE CALCULUS. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Heap.Connectives where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Empty as E using (⊥; ⊥*)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib
open import TheoryGrammar.Theories.MonoidSep

open import TheoryGrammar.Instances.Heap.Base public

-- GENERIC: a partiality located at a TUPLE refutes every total point.

module Generic {S : Type₀} {σ : SortedSig S ℓ-zero ℓ-zero}
               (Fib : Fibered σ ℓ-zero ℓ-zero) where

  open FibNotation Fib

  no-tuple-point : (o : σ .ops)
                   (m⃗ : (a : σ .arities o) → Fib .carrier (σ .sortOf o a))
                 → (⊗ˢ o (λ a → ⌈ m⃗ a ⌉) ⊢ ⊥G)
                 → LaxPoint Fib → ⊥
  no-tuple-point o m⃗ k P =
    E.rec* (k (P .op o m⃗)
              ( P .split o m⃗
              , λ a → Eq.pathToEq (funExt⁻ (P .parts-split o m⃗) a) ))

open RulesF heapFib public

Gr : Type₁
Gr = TheoryTy ℓ-zero tt

-- The separating conjunction and the empty heap.

emp : Gr
emp = ⊗ˢ nilop (λ ())

-- `⊗ˢ` at the partial operation. `(A ∗ B) h` is inhabited only when `h`
-- actually splits DISJOINTLY -- the `u # v` conjunct of `HeapSplit` -- so
-- the whole content of separation is in the `Fibered`, not here.

-- THE FRAME RULE is the functorial action of `∗`.

-- `∗-map`, `frame` and `frameL` come from `Theories.MonoidSep` now: not
-- one line of them mentioned heaps, only `appop` and `⊗ˢ-map`.
open MonSep heapFib public using (_∗_; ∗-map; frame; frameL)

-- THE MAGIC WAND, via `Focus`. Focused at slot `false`: the index is the
-- heap we hold, `Rest` is the single other slot, and `whole` is the join.

heapFocus : Focus heapFib appop false
heapFocus .SplitAt v = Σ[ u ∈ Heap ] Σ[ h ∈ Heap ] (Ilv u v h × (u # v))
heapFocus .whole (u , h , _) = h
heapFocus .Rest = Unit
heapFocus .restOf _ = true
heapFocus .restSlot (u , _ , _) _ = u

open FocusNotation heapFocus public

_─∗_ : Gr → Gr → Gr
A ─∗ B = ⊸ᶠ (boolΠ A ⊤G) B

infixr 19 _─∗_

-- The adjunction, with β and η both `refl` -- `⊸ᶠ-UP` from `Fibered`.
-- This is the payoff of using `Focus`: no weakening, no `tt`, no
-- pointful step.
wand-UP : {A B : Gr} → _
wand-UP {A} {B} = ⊸ᶠ-UP {A = boolΠ A ⊤G} {B = B}

-- PARTIALITY, AS A THEOREM OF THE CALCULUS. The separation-logic statement
-- of "a location cannot be owned twice" is not a side condition but an
-- internal refutation: ⌈ single l x ⌉ ∗ ⌈ single l x ⌉ ⊢ ⊥G Compare
-- `Field/Partial`, where "inv is undefined at 0" is `Domˢ invOp ⊣⊢ ¬G ⌈ f0
-- ⌉`.

-- PRIMITIVE (phase 1): the only new one.  A splitting entails
-- disjointness of its parts; this is the interface to `HeapSplit`'s
-- fourth component, and the one place it is projected.
split-# : (h : Heap) (sp : heapFib .Split appop h)
        → heapFib .parts appop h sp true # heapFib .parts appop h sp false
split-# h (u , v , _ , d) = d

-- THEOREM (phase 2): `⊗ˢ-E` supplies the splitting and the two
-- representable payloads; `#-Eq` moves disjointness onto them; `#-self`
-- refutes it.  All three are already primitives of `Base`.
apart-self : (l : Loc) (x : Val)
           → (⌈ single l x ⌉ ∗ ⌈ single l x ⌉) ⊢ ⊥G
apart-self l x =
  ⊗ˢ-E appop {A = boolΠ ⌈ single l x ⌉ ⌈ single l x ⌉}
       (λ h sp k → E.rec (#-self l x (#-Eq (k true) (k false) (split-# h sp))))

-- ... and the refutation of every total point, from that theorem alone.

-- Pure coercion between two spellings of one family -- compare `intoQ` in
-- Bags/Quicksort.
respell : {u v : Heap} (a : Bool) → ⌈ boolΠ u v a ⌉ ⊢ boolΠ ⌈ u ⌉ ⌈ v ⌉ a
respell {u} {v} = boolΠ {M = λ a → ⌈ boolΠ u v a ⌉ ⊢ boolΠ ⌈ u ⌉ ⌈ v ⌉ a} idg idg

-- THE MONEY RESULT, and every step of it is a term of the calculus:
-- `⊗ˢ-map` to respell, then the internal refutation `apart-self`.
noHeapPoint : LaxPoint heapFib → ⊥
noHeapPoint =
  Generic.no-tuple-point heapFib appop (boolΠ s s)
    ( apart-self 0 v0
    ∘g ⊗ˢ-map appop {A = λ a → ⌈ boolΠ s s a ⌉}
                    {B = boolΠ ⌈ s ⌉ ⌈ s ⌉} respell )
  where s = single 0 v0
