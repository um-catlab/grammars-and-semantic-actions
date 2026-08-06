{-
  THE FREE COMMUTATIVE MONOID (bags), and quicksort's recursion.

  THE DESIGN DECISION, up front, because it is the whole point.

  The obvious move is to take the carrier to be `FMSet A`.  It does not
  work: `FMSet` is a HIT, so the natural splitting

      Split appop m = Σ[ (l , r) ] (l ++ r ≡ m)

  carries a PATH, and `Substrate` exists precisely to avoid carrying
  proofs -- that is what buys `⊗-UP-β/η ≡ refl` (TheoryGrammar.Substrate).
  Worse, matching on such a splitting means matching on indices of HIT
  type.

  So don't quotient the carrier.  Take

      carrier = List A          -- a list, PRESENTING a bag
      Split   = interleaving    -- an inductive family, no paths

  The commutativity lives in the SPLITTING RELATION, not in the carrier.
  This is the substrate/frame being primitive rather than the algebra:
  `Ilv u v w` says w's elements are dealt out into u and v, which is
  exactly the free commutative monoid's promonoidal structure, and it is
  a perfectly ordinary inductive family.

  Note what this costs, honestly: `Ilv` is NOT the fibre of `++`.
  `Ilv u v w` does not imply `u ++ v ≡ w`, only that they agree as bags.
  So this substrate is one where `Split` is deliberately larger than the
  fibre -- which is exactly the `op-parts` law I flagged as missing from
  the record.  Here its absence is a feature, and that is the argument
  for NOT adding it as a field.

  Commutativity of ⊗ is then `ilvSwap`, three lines, and quicksort's
  recursion is guarded because the pivot is removed.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.Bags where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
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
open import TheoryGrammar.Substrate
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded

module Bags (A : Type₀) where

  Bag : Type₀
  Bag = List A

  -- ================================================================
  -- Signature.  Same as monoids -- commutativity is an EQUATION, and
  -- equations live in the model, not the signature.
  -- ================================================================

  data MonOp : Type₀ where
    nilop appop : MonOp

  MonAr : MonOp → Type₀
  MonAr nilop = ⊥
  MonAr appop = Bool

  cmSig : SortedSig Unit ℓ-zero ℓ-zero
  cmSig .ops          = MonOp
  cmSig .arities      = MonAr
  cmSig .sortOf _ _   = tt
  cmSig .resultSort _ = tt

  -- ================================================================
  -- Interleaving: the commutative splitting.
  -- ================================================================

  data Ilv : Bag → Bag → Bag → Type₀ where
    nil   : Ilv [] [] []
    left  : ∀ {x u v w} → Ilv u v w → Ilv (x ∷ u) v (x ∷ w)
    right : ∀ {x u v w} → Ilv u v w → Ilv u (x ∷ v) (x ∷ w)

  IsNil : Bag → Type₀
  IsNil []      = Unit
  IsNil (_ ∷ _) = ⊥

  ilvApp : (u v : Bag) → Ilv u v (u ++ v)
  ilvApp []      []      = nil
  ilvApp []      (x ∷ v) = right (ilvApp [] v)
  ilvApp (x ∷ u) v       = left (ilvApp u v)

  -- COMMUTATIVITY, at the level of splittings
  ilvSwap : ∀ {u v w} → Ilv u v w → Ilv v u w
  ilvSwap nil       = nil
  ilvSwap (left s)  = right (ilvSwap s)
  ilvSwap (right s) = left (ilvSwap s)

  -- lengths
  ilvLenL : ∀ {u v w} → Ilv u v w → length u ≤ length w
  ilvLenL nil       = ≤-refl
  ilvLenL (left s)  = suc-≤-suc (ilvLenL s)
  ilvLenL (right s) = ≤-suc (ilvLenL s)

  ilvLenR : ∀ {u v w} → Ilv u v w → length v ≤ length w
  ilvLenR nil       = ≤-refl
  ilvLenR (left s)  = ≤-suc (ilvLenR s)
  ilvLenR (right s) = suc-≤-suc (ilvLenR s)

  -- a nonempty COMPLEMENT makes the slot strictly smaller
  ilvLenL< : ∀ {u v w} → Ilv u v w → 0 < length v → length u < length w
  ilvLenL< nil       pr = E.rec (¬-<-zero pr)
  ilvLenL< (left s)  pr = suc-≤-suc (ilvLenL< s pr)
  ilvLenL< (right s) pr = suc-≤-suc (ilvLenL s)

  ilvLenR< : ∀ {u v w} → Ilv u v w → 0 < length u → length v < length w
  ilvLenR< nil       pr = E.rec (¬-<-zero pr)
  ilvLenR< (left s)  pr = suc-≤-suc (ilvLenR s)
  ilvLenR< (right s) pr = suc-≤-suc (ilvLenR< s pr)

  -- ================================================================
  -- The substrate.
  -- ================================================================

  MonSplit : (o : MonOp) → Bag → Type₀
  MonSplit nilop w = IsNil w
  MonSplit appop w = Σ[ u ∈ Bag ] Σ[ v ∈ Bag ] Ilv u v w

  MonParts : (o : MonOp) (w : Bag) → MonSplit o w → MonAr o → Bag
  MonParts nilop w sp ()
  MonParts appop w (u , v , _) b = if b then u else v

  bagSub : Substrate cmSig ℓ-zero ℓ-zero
  bagSub .carrier _   = Bag
  bagSub .op nilop _  = []
  bagSub .op appop f  = f true ++ f false
  bagSub .Split       = MonSplit
  bagSub .parts       = MonParts
  bagSub .split nilop f = tt
  bagSub .split appop f = f true , f false , ilvApp (f true) (f false)
  bagSub .parts-split nilop f = funExt λ ()
  bagSub .parts-split appop f = funExt λ { false → refl ; true → refl }

  open SubNotation bagSub

  Gr : Type₁
  Gr = TheoryTy ℓ-zero tt

  _⊗'_ : Gr → Gr → Gr
  P ⊗' Q = ⊗ˢ appop (λ b → if b then P else Q)

  ε' : Gr
  ε' = ⊗ˢ nilop (λ ())

  ⊗-mk : {P Q : Gr} {u v w : Bag} → Ilv u v w → P u → Q v → (P ⊗' Q) w
  ⊗-mk {u = u} {v} s p q = (u , v , s) , λ { true → p ; false → q }

  -- ================================================================
  -- THE COMMUTATIVITY EQUATION, lifted to an isomorphism.  This is the
  -- `eqn→Iso` shape at the one equation that distinguishes commutative
  -- monoids from monoids, discharged by `ilvSwap`.
  -- ================================================================

  ⊗-comm : {P Q : Gr} → (P ⊗' Q) ⊢ (Q ⊗' P)
  ⊗-comm w ((u , v , s) , h) = (v , u , ilvSwap s) , λ { true → h false ; false → h true }

  ilvSwap-inv : ∀ {u v w} (s : Ilv u v w) → ilvSwap (ilvSwap s) ≡ s
  ilvSwap-inv nil       = refl
  ilvSwap-inv (left s)  = cong left  (ilvSwap-inv s)
  ilvSwap-inv (right s) = cong right (ilvSwap-inv s)

  ⊗-comm-invol : {P Q : Gr} (w : Bag) (t : (P ⊗' Q) w)
               → ⊗-comm {P = Q} {Q = P} w (⊗-comm {P = P} {Q = Q} w t) ≡ t
  ⊗-comm-invol w ((u , v , s) , h) =
    ΣPathP ( (λ i → u , v , ilvSwap-inv s i)
           , funExt λ { true → refl ; false → refl } )

  -- ================================================================
  -- The grading.  Properness of a slot = its COMPLEMENT is nonempty.
  -- ================================================================

  Proper' : (o : MonOp) (m : Bag) → MonSplit o m → MonAr o → Type₀
  Proper' nilop m sp ()
  Proper' appop m (u , v , _) b = 0 < length (if b then v else u)

  bagGraded : GradedSubstrate cmSig ℓ-zero ℓ-zero
  bagGraded .sub    = bagSub
  bagGraded .deg _  = length
  bagGraded .Proper = Proper'
  bagGraded .deg≤ nilop m sp ()
  bagGraded .deg≤ appop m (u , v , s) true  = ilvLenL s
  bagGraded .deg≤ appop m (u , v , s) false = ilvLenR s
  bagGraded .deg< nilop m sp ()
  bagGraded .deg< appop m (u , v , s) true  pr = ilvLenL< s pr
  bagGraded .deg< appop m (u , v , s) false pr = ilvLenR< s pr

  -- ================================================================
  -- QUICKSORT'S FUNCTOR, and why its recursion is guarded.
  --
  --     H X b  =  (b is empty)  ⊕  Σ[piv] X lo ⊗ ⌈piv⌉ ⊗ X hi
  --
  -- The two recursive slots are discharged DIFFERENTLY, which is the
  -- whole reason `⊗-guard` takes a per-slot certificate:
  --
  --   * `lo` shrinks because its COMPLEMENT (piv ∷ hi) is nonempty --
  --     `slotProper`.  The pivot is the witness.
  --   * `hi` does NOT shrink for that reason: its sibling `lo` may be
  --     empty.  It shrinks because the pivot sits INSIDE its own factor,
  --     so that factor is already guarded -- `slotGuarded`.
  --
  -- This is the agent's finding made mechanical: the decrease comes from
  -- the pivot, not from the partition.  A bare `b = lo ⊎ hi` in a
  -- commutative monoid does not decrease at all.
  -- ================================================================

  open Guard bagGraded ℓ-zero Unit (λ _ → tt) public

  QG' : A → Bool → Functor tt
  QG' piv true  = ⌜ ⌈ piv ∷ [] ⌉ ⌝
  QG' piv false = Var tt

  QG : A → Bool → Functor tt
  QG piv true  = Var tt
  QG piv false = ⊗e appop (QG' piv)

  QAlt : Bool → Functor tt
  QAlt true  = ⌜ ⌈ [] ⌉ ⌝
  QAlt false = ⊕e A (λ piv → ⊗e appop (QG piv))

  QF : Unit → Functor tt
  QF _ = ⊕e Bool QAlt

  -- the pivot witnesses that the right factor is nonempty
  restNonEmpty : (piv : A) (rest : Bag)
               → Sh (⊗e appop (QG' piv)) rest → 0 < length rest
  restNonEmpty piv rest ((p1 , hi , ilv) , sh') with lower (sh' true)
  ... | Eq.refl = ilvLenL ilv

  innerGuarded : (piv : A) → Guarded (⊗e appop (QG' piv))
  innerGuarded piv = ⊗-guard appop (QG' piv) go
    where
      go : (v : Bag) (sp' : MonSplit appop v)
           (sh' : (a : Bool) → Sh (QG' piv a) (MonParts appop v sp' a))
           (a : Bool) (p : Pos (QG' piv a) _ (sh' a))
         → degIx (nx (QG' piv a) _ (sh' a) p) < length v
      go v sp' sh' true ()
      go v (p1 , hi , ilv) sh' false p with lower (sh' true)
      ... | Eq.refl =
        slotProper appop v (p1 , hi , ilv) false (≤Var tt) ≤-refl (sh' false) p

  qfGuarded : (x : Unit) → Guarded (QF x)
  qfGuarded tt = <⊕e Bool _ alt
    where
      go : (piv : A) (m : Bag) (sp : MonSplit appop m)
           (sh : (a : Bool) → Sh (QG piv a) (MonParts appop m sp a))
           (a : Bool) (p : Pos (QG piv a) _ (sh a))
         → degIx (nx (QG piv a) _ (sh a) p) < length m
      go piv m (lo , rest , ilv) sh true p =
        slotProper appop m (lo , rest , ilv) true (≤Var tt)
                   (restNonEmpty piv rest (sh false)) (sh true) p
      go piv m sp sh false p =
        slotGuarded appop m sp false (innerGuarded piv) (sh false) p

      alt : (b : Bool) → Guarded (QAlt b)
      alt true  = <⌜⌝ ⌈ [] ⌉
      alt false = <⊕e A _ (λ piv → ⊗-guard appop (QG piv) (go piv))

  -- ================================================================
  -- QUICKSORT, as a hylomorphism.  The coalgebra partitions, the
  -- algebra concatenates, and `hylo` (TheoryGrammar.Graded) supplies the
  -- recursion from `qfGuarded` alone.  No `with`, no explicit
  -- well-founded recursion at the use site: the termination certificate
  -- IS the guardedness of the description.
  -- ================================================================

  partition : (p : A → Bool) (xs : Bag)
            → Σ[ lo ∈ Bag ] Σ[ hi ∈ Bag ] Ilv lo hi xs
  partition p [] = [] , [] , nil
  partition p (y ∷ xs) with p y
  ... | true  = let (lo , hi , s) = partition p xs in (y ∷ lo) , hi , left s
  ... | false = let (lo , hi , s) = partition p xs in lo , (y ∷ hi) , right s

  -- ================================================================
  -- ⊗ intro and elim AT THE CONNECTIVE LEVEL.  These two are the only
  -- places below that mention a splitting; everything after is built
  -- from them.
  -- ================================================================

  ⊗I : {P : Bool → Bag → Type₀} {u v w : Bag}
     → Ilv u v w → P true u → P false v
     → Σ[ sp ∈ MonSplit appop w ] ((a : Bool) → P a (MonParts appop w sp a))
  ⊗I {u = u} {v} s p q = (u , v , s) , λ { true → p ; false → q }

  ⊗E : {P : Bool → Bag → Type₀} {R : Type₀} {w : Bag}
     → ((u v : Bag) → Ilv u v w → P true u → P false v → R)
     → Σ[ sp ∈ MonSplit appop w ] ((a : Bool) → P a (MonParts appop w sp a)) → R
  ⊗E f ((u , v , s) , h) = f u v s (h true) (h false)

  -- ================================================================
  -- PERMUTATION, for the intrinsic specification.  `Perm a w` says the
  -- list `a` is a rearrangement of `w`; insertion is `Ilv (x ∷ []) v w`,
  -- so permutation is built from the SUBSTRATE'S OWN relation rather
  -- than from a quotient.
  -- ================================================================

  data Perm : Bag → Bag → Type₀ where
    nil  : Perm [] []
    cons : ∀ {x u v w} → Perm u v → Ilv (x ∷ []) v w → Perm (x ∷ u) w

  ilvNilL : ∀ {v w} → Ilv [] v w → v Eq.≡ w
  ilvNilL nil = Eq.refl
  ilvNilL (right s) with ilvNilL s
  ... | Eq.refl = Eq.refl

  -- ================================================================
  -- COMBINATORS.  These are the rules of the calculus; they are the
  -- only pointful things in this file apart from the two primitives
  -- below.  Everything after composes them.
  -- ================================================================

  ⊤' : Gr
  ⊤' _ = Unit

  idg : {P : Gr} → P ⊢ P
  idg _ p = p

  _∘g_ : {P Q R : Gr} → Q ⊢ R → P ⊢ Q → P ⊢ R
  (g ∘g f) w p = g w (f w p)

  infixr 9 _∘g_

  ⊕-elim : {P Q R : Gr} → P ⊢ R → Q ⊢ R → (P ⊕ Q) ⊢ R
  ⊕-elim f g w (inl p) = f w p
  ⊕-elim f g w (inr q) = g w q

  ⊕ᴰ-in : {Y : Type₀} {P : Y → Gr} (y : Y) → P y ⊢ ⊕ᴰ Y P
  ⊕ᴰ-in y w p = y , p

  ⊕ᴰ-elim : {Y : Type₀} {P : Y → Gr} {R : Gr}
          → ((y : Y) → P y ⊢ R) → ⊕ᴰ Y P ⊢ R
  ⊕ᴰ-elim f w (y , p) = f y w p

  liftg : {P : Gr} → P ⊢ (λ m → Lift ℓ-zero (P m))
  liftg _ p = lift p

  ⊗-map : {P P' Q Q' : Gr} → P ⊢ P' → Q ⊢ Q' → (P ⊗' Q) ⊢ (P' ⊗' Q')
  ⊗-map f g w ((u , v , s) , h) = ⊗-mk s (f u (h true)) (g v (h false))

  -- ================================================================
  -- ASSOCIATIVITY OF INTERLEAVING.  w = p ⊎ (q ⊎ r) regrouped as
  -- w = q ⊎ (p ⊎ r).  Used once, by the partition primitive.
  -- ================================================================

  ilvAssoc : ∀ {p q r u w} → Ilv p u w → Ilv q r u
           → Σ[ y ∈ Bag ] (Ilv q y w × Ilv p r y)
  ilvAssoc nil       nil        = [] , nil , nil
  ilvAssoc (left s)  t          =
    let (y , e1 , e2) = ilvAssoc s t in _ , right e1 , left e2
  ilvAssoc (right s) (left t)   =
    let (y , e1 , e2) = ilvAssoc s t in _ , left e1 , e2
  ilvAssoc (right s) (right t)  =
    let (y , e1 , e2) = ilvAssoc s t in _ , right e1 , right e2

  -- Permutations merge along an interleaving.  The only lemma the
  -- intrinsic proof needs, and it is discharged by `ilvAssoc` + `ilvSwap`
  -- -- i.e. entirely by the substrate's own structure.
  permMerge : ∀ {a u b v w} → Perm a u → Perm b v → Ilv u v w → Perm (a ++ b) w
  permMerge nil q s with ilvNilL s
  ... | Eq.refl = q
  permMerge (cons p ins) q s =
    let (y , e1 , e2) = ilvAssoc (ilvSwap s) ins
    in cons (permMerge p q (ilvSwap e2)) e1

  -- ================================================================
  -- THE TWO PRIMITIVES.
  -- ================================================================

  -- (1) DECOMPOSITION.  Every bag is empty or has a distinguished
  -- element and a rest.  This is the bag instance of "⊤ is the initial
  -- algebra of the shape functor" -- no comparison appears in it.
  bagCase : ⊤' ⊢ (⌈ [] ⌉ ⊕ ⊕ᴰ A (λ x → ⌈ x ∷ [] ⌉ ⊗' ⊤'))
  bagCase []       _ = inl Eq.refl
  bagCase (x ∷ xs) _ = inr (x , ⊗-mk (left (ilvApp [] xs)) Eq.refl tt)

  -- (2) PARTITION.  Given the pivot and the rest, split the rest by
  -- comparison and regroup so the pivot sits in the middle.  This is
  -- the ONLY place the ordering `le` is used.
  splitAround : (le : A → A → Bool) (x : A)
              → (⌈ x ∷ [] ⌉ ⊗' ⊤') ⊢ (⊤' ⊗' (⌈ x ∷ [] ⌉ ⊗' ⊤'))
  splitAround le x w ((u , v , s) , h) = go (h true) s
    where
      go : u Eq.≡ x ∷ [] → Ilv u v w → (⊤' ⊗' (⌈ x ∷ [] ⌉ ⊗' ⊤')) w
      go Eq.refl s' =
        let (lo , hi , t) = partition (λ y → le y x) v
            (rest , e1 , e2) = ilvAssoc s' t
        in ⊗-mk e1 tt (⊗-mk e2 Eq.refl tt)

  -- ================================================================
  -- THE INTRINSIC SPECIFICATION.  The motive of the hylomorphism IS the
  -- statement to be proved: "a bag equivalent to the input".  Nothing is
  -- rechecked afterwards -- the algebra produces the proof as it builds
  -- the output, so a wrong implementation cannot be written.
  -- ================================================================

  Spec : Ix → Type₀
  Spec (_ , m) = Σ[ out ∈ Bag ] Perm out m

  specNil : {w : Bag} → w Eq.≡ [] → Spec (tt , w)
  specNil Eq.refl = [] , nil

  specJoin : (piv : A) {lo rest w p1 hi : Bag}
           → Ilv lo rest w → Ilv p1 hi rest → p1 Eq.≡ piv ∷ []
           → Spec (tt , lo) → Spec (tt , hi) → Spec (tt , w)
  specJoin piv e1 e2 Eq.refl (loOut , pl) (hiOut , ph) =
    (loOut ++ (piv ∷ hiOut)) , permMerge pl (cons ph e2) e1

  module Quicksort (le : A → A → Bool) where

    -- Plumbing between two spellings of one type: the description's ⊗e
    -- carries a Lift on the representable, and its arity-family is not
    -- `if`-shaped, so the implicits must be pinned.  Pure coercion.
    intoQ : (x : A) → (⊤' ⊗' (⌈ x ∷ [] ⌉ ⊗' ⊤'))
                    ⊢ ⟦ ⊗e appop (QG x) ⟧c (λ _ → Unit)
    intoQ x w ((lo , rest , e1) , h) =
      ⊗I {P = λ a → ⟦ QG x a ⟧c (λ _ → Unit)} e1 tt
        (⊗E {P = λ a → if a then ⌈ x ∷ [] ⌉ else ⊤'}
            (λ p1 hi e2 pf _ →
               ⊗I {P = λ a → ⟦ QG' x a ⟧c (λ _ → Unit)} e2 (lift pf) tt)
            (h false))

    -- THE COALGEBRA, point-free: decompose, then for each pivot
    -- partition around it and inject.  No list pattern is matched here.
    qcoalg : CoalgC QF (λ _ → Unit)
    qcoalg tt =
      ⊕-elim (⊕ᴰ-in true ∘g liftg)
             (⊕ᴰ-elim (λ x → ⊕ᴰ-in false ∘g ⊕ᴰ-in x
                             ∘g intoQ x ∘g splitAround le x))
      ∘g bagCase

    -- THE ALGEBRA, point-free: the empty branch returns ε, the pivot
    -- branch concatenates around the pivot.
    qalg : AlgC QF (λ _ → Bag)
    qalg tt =
      ⊕ᴰ-elim λ { true  → λ _ _ → []
                ; false → ⊕ᴰ-elim λ piv → λ w t →
                    ⊗E {P = λ a → ⟦ QG piv a ⟧c (λ _ → Bag)} {w = w}
                       (λ _ _ _ sLo inner →
                          sLo ++ (piv ∷ ⊗E {P = λ a → ⟦ QG' piv a ⟧c (λ _ → Bag)}
                                            (λ _ _ _ _ sHi → sHi) inner)) t }

    quicksort : Bag → Bag
    quicksort m = hyloC qfGuarded qcoalg qalg (tt , m) tt

    -- ... and the same coalgebra, run at the SPECIFICATION.
    qalgV : AlgC QF Spec
    qalgV tt =
      ⊕ᴰ-elim λ { true  → λ w e → specNil (lower e)
                ; false → ⊕ᴰ-elim λ piv → λ w t →
                    ⊗E {P = λ a → ⟦ QG piv a ⟧c Spec} {w = w}
                       (λ lo rest e1 sLo inner →
                          ⊗E {P = λ a → ⟦ QG' piv a ⟧c Spec}
                             (λ p1 hi e2 pf sHi →
                                specJoin piv e1 e2 (lower pf) sLo sHi)
                             inner) t }

    -- INTRINSICALLY VERIFIED QUICKSORT.
    quicksortV : (m : Bag) → Σ[ out ∈ Bag ] Perm out m
    quicksortV m = hyloC qfGuarded qcoalg qalgV (tt , m) tt

-- ==================================================================
-- It computes.
-- ==================================================================

module Test where

  open Bags ℕ

  leℕ : ℕ → ℕ → Bool
  leℕ zero    _       = true
  leℕ (suc m) zero    = false
  leℕ (suc m) (suc n) = leℕ m n

  open Quicksort leℕ

  _ : quicksort [] ≡ []
  _ = refl

  _ : quicksort (1 ∷ []) ≡ (1 ∷ [])
  _ = refl

  _ : quicksort (2 ∷ 1 ∷ []) ≡ (1 ∷ 2 ∷ [])
  _ = refl

  _ : quicksort (5 ∷ 3 ∷ 4 ∷ 1 ∷ 2 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
  _ = refl

  -- _ : quicksort (5 ∷ 3 ∷ 4 ∷ 1 ∷ 2 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
  -- _ = refl


  -- the verified version computes to the same answer, and its second
  -- component is the permutation proof, produced by construction
  _ : quicksortV (5 ∷ 3 ∷ 4 ∷ 1 ∷ 2 ∷ []) .fst ≡ (1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
  _ = refl

  _ : quicksortV (2 ∷ 2 ∷ 1 ∷ []) .fst ≡ (1 ∷ 2 ∷ 2 ∷ [])
  _ = refl
