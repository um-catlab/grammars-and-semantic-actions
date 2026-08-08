{-# OPTIONS --lossy-unification #-}
{- THE MONOIDAL LAWS OF `⊗ˢ`, generic in a monoid `Fibered`.

   Every instance in this tree was writing `⊗-comm`, `⊗-assoc` and the
   two unit laws by hand -- as ⊢-terms, but as PRIMITIVE ones, matching
   the splitting.  None of that is instance-specific: the laws follow
   from four facts about the SPLITTING RELATION alone, which is the only
   thing a theory has to supply.

       Sym     the splitting can be swapped        -> ⊗-comm
       Assoc   nested splittings reassociate       -> ⊗-assoc
       UnitL   a nil left part leaves the whole    -> ⊗-unit-l
       UnitR   ... and a nil right part            -> ⊗-unit-r

   The fields are stated with `Eq.≡` and discharged by `coeEq`, so at
   every instance in this tree the coercions are `Eq.refl` and the
   derived terms are transport-free -- which is what keeps the `refl`
   tests downstream computing. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Theories.MonoidStructure where

open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib
open import TheoryGrammar.Precision using (coeEq)
open import TheoryGrammar.Theories.Monoid

-- Levels pinned at ℓ-zero, as in `MonoidSep` and `MonoidStar`.
module MonStr (Fib : Fibered monoidSig ℓ-zero ℓ-zero) where

  private module R = RulesF Fib
  open R using (_⊢_; ⊗ˢ; ⊗ˢ-map; idg; _∘g_)

  Gr : Type₁
  Gr = R.TheoryTy ℓ-zero tt

  infixr 20 _⊗ᵐ_

  _⊗ᵐ_ : Gr → Gr → Gr
  P ⊗ᵐ Q = ⊗ˢ appop (boolΠ {M = λ _ → Gr} P Q)

  εᵐ : Gr
  εᵐ = ⊗ˢ nilop (λ ())

  Car : Type₀
  Car = Fib .carrier tt

  Sp : Car → Type₀
  Sp = Fib .Split appop

  pt : (m : Car) → Sp m → Bool → Car
  pt = Fib .parts appop

  -- intro, once: a splitting and a payload at each side
  ⊗ᵐ-I : {P Q : Gr} (m : Car) (sp : Sp m)
       → P (pt m sp true) → Q (pt m sp false) → (P ⊗ᵐ Q) m
  ⊗ᵐ-I {P} {Q} m sp p q = sp , boolΠ {M = λ b → boolΠ {M = λ _ → Gr} P Q b (pt m sp b)} p q

  -- THE ARITY-η COERCION.  An instance whose binary former is
  -- `λ b → if b then P else Q` does not have it DEFINITIONALLY equal to
  -- `boolΠ P Q` -- arities have no η -- so this moves between the two
  -- spellings.  It is `⊗ˢ-map` with the case split done here rather than
  -- demanded of the caller, and at every instance both arguments are
  -- `idg`.
  ⊗ˢ-recast : {A B : Bool → Gr} → A true ⊢ B true → A false ⊢ B false
            → ⊗ˢ appop A ⊢ ⊗ˢ appop B
  ⊗ˢ-recast {A} {B} f g m (sp , h) =
    sp , boolΠ {M = λ b → B b (pt m sp b)} (f _ (h true)) (g _ (h false))

  -- ================================================================
  -- COMMUTATIVITY.
  -- ================================================================

  record Sym : Type₀ where
    field
      swapSp : (m : Car) → Sp m → Sp m
      swapL  : (m : Car) (sp : Sp m) → pt m (swapSp m sp) true  Eq.≡ pt m sp false
      swapR  : (m : Car) (sp : Sp m) → pt m (swapSp m sp) false Eq.≡ pt m sp true

  open Sym public

  ⊗ᵐ-comm : Sym → {P Q : Gr} → (P ⊗ᵐ Q) ⊢ (Q ⊗ᵐ P)
  ⊗ᵐ-comm S {P} {Q} m (sp , h) =
    ⊗ᵐ-I {P = Q} {Q = P} m (S .swapSp m sp)
      (coeEq Q (Eq.sym (S .swapL m sp)) (h false))
      (coeEq P (Eq.sym (S .swapR m sp)) (h true))

  -- ================================================================
  -- ASSOCIATIVITY.  `reassoc` is the only content: a splitting of `m`
  -- into `p` and (a splitting of the rest into `q` and `r`) is a
  -- splitting of `m` into (`p` and `q`) and `r`.  This is Levi's lemma
  -- at strings, `ilvAssoc` at bags, and `useAssoc` at a usage algebra.
  -- ================================================================

  record Assoc : Type₀ where
    field
      -- from  m = p ⊗ (q ⊗ r)  build  m = (p ⊗ q) ⊗ r
      reOut : (m : Car) (sp : Sp m) (sp' : Sp (pt m sp false)) → Sp m
      reIn  : (m : Car) (sp : Sp m) (sp' : Sp (pt m sp false))
            → Sp (pt m (reOut m sp sp') true)
      reP : (m : Car) (sp : Sp m) (sp' : Sp (pt m sp false))
          → pt (pt m (reOut m sp sp') true) (reIn m sp sp') true Eq.≡ pt m sp true
      reQ : (m : Car) (sp : Sp m) (sp' : Sp (pt m sp false))
          → pt (pt m (reOut m sp sp') true) (reIn m sp sp') false Eq.≡ pt (pt m sp false) sp' true
      reR : (m : Car) (sp : Sp m) (sp' : Sp (pt m sp false))
          → pt m (reOut m sp sp') false Eq.≡ pt (pt m sp false) sp' false

  open Assoc public

  ⊗ᵐ-assoc : Assoc → {P Q S : Gr} → (P ⊗ᵐ (Q ⊗ᵐ S)) ⊢ ((P ⊗ᵐ Q) ⊗ᵐ S)
  ⊗ᵐ-assoc A {P} {Q} {S} m (sp , h) = go (h false)
    where
      go : (Q ⊗ᵐ S) (pt m sp false) → ((P ⊗ᵐ Q) ⊗ᵐ S) m
      go (sp' , k) =
        ⊗ᵐ-I {P = P ⊗ᵐ Q} {Q = S} m (A .reOut m sp sp')
          (⊗ᵐ-I {P = P} {Q = Q} _ (A .reIn m sp sp')
            (coeEq P (Eq.sym (A .reP m sp sp')) (h true))
            (coeEq Q (Eq.sym (A .reQ m sp sp')) (k true)))
          (coeEq S (Eq.sym (A .reR m sp sp')) (k false))

  -- ================================================================
  -- THE UNITS.  `εᵐ` is the nullary tensor, so a left unit says: a
  -- splitting whose left part carries `ε` leaves the right part equal
  -- to the whole.
  -- ================================================================

  record UnitL : Type₀ where
    field
      -- forward: an ε on the left means the right part IS the whole
      nilL : (m : Car) (sp : Sp m) → Fib .Split nilop (pt m sp true)
           → pt m sp false Eq.≡ m
      -- backward: every world splits with an ε on the left
      mkL  : (m : Car) → Sp m
      mkLε : (m : Car) → Fib .Split nilop (pt m (mkL m) true)
      mkLR : (m : Car) → pt m (mkL m) false Eq.≡ m

  open UnitL public

  record UnitR : Type₀ where
    field
      nilR : (m : Car) (sp : Sp m) → Fib .Split nilop (pt m sp false)
           → pt m sp true Eq.≡ m
      mkR  : (m : Car) → Sp m
      mkRε : (m : Car) → Fib .Split nilop (pt m (mkR m) false)
      mkRL : (m : Car) → pt m (mkR m) true Eq.≡ m

  open UnitR public

  ⊗ᵐ-unit-l : UnitL → {P : Gr} → (εᵐ ⊗ᵐ P) ⊢ P
  ⊗ᵐ-unit-l U {P} m (sp , h) = coeEq P (U .nilL m sp (h true .fst)) (h false)

  ⊗ᵐ-unit-l⁻ : UnitL → {P : Gr} → P ⊢ (εᵐ ⊗ᵐ P)
  ⊗ᵐ-unit-l⁻ U {P} m p =
    ⊗ᵐ-I {P = εᵐ} {Q = P} m (U .mkL m) (U .mkLε m , λ ())
      (coeEq P (Eq.sym (U .mkLR m)) p)

  ⊗ᵐ-unit-r : UnitR → {P : Gr} → (P ⊗ᵐ εᵐ) ⊢ P
  ⊗ᵐ-unit-r U {P} m (sp , h) = coeEq P (U .nilR m sp (h false .fst)) (h true)

  ⊗ᵐ-unit-r⁻ : UnitR → {P : Gr} → P ⊢ (P ⊗ᵐ εᵐ)
  ⊗ᵐ-unit-r⁻ U {P} m p =
    ⊗ᵐ-I {P = P} {Q = εᵐ} m (U .mkR m)
      (coeEq P (Eq.sym (U .mkRL m)) p) (U .mkRε m , λ ())

  -- ================================================================
  -- ... and the derived laws that need no new data.
  -- ================================================================

  -- the functorial action
  ⊗ᵐ-map : {A' B' C' D' : Gr} → A' ⊢ B' → C' ⊢ D' → (A' ⊗ᵐ C') ⊢ (B' ⊗ᵐ D')
  ⊗ᵐ-map {A'} {B'} {C'} {D'} f g =
    ⊗ˢ-map appop {A = boolΠ {M = λ _ → Gr} A' C'}
                 {B = boolΠ {M = λ _ → Gr} B' D'}
           (boolΠ {M = λ b → boolΠ {M = λ _ → Gr} A' C' b
                           ⊢ boolΠ {M = λ _ → Gr} B' D' b} f g)

  -- ... and the other associator, which needs NO new data: five
  -- commutations around the one `Assoc`.
  ⊗ᵐ-assoc⁻ : Sym → Assoc → {P Q S : Gr} → ((P ⊗ᵐ Q) ⊗ᵐ S) ⊢ (P ⊗ᵐ (Q ⊗ᵐ S))
  ⊗ᵐ-assoc⁻ Sy A {P} {Q} {S} =
      ⊗ᵐ-map {A' = P} {B' = P} {C' = S ⊗ᵐ Q} {D' = Q ⊗ᵐ S}
             idg (⊗ᵐ-comm Sy {P = S} {Q = Q})
    ∘g ⊗ᵐ-comm Sy {P = S ⊗ᵐ Q} {Q = P}
    ∘g ⊗ᵐ-assoc A {P = S} {Q = Q} {S = P}
    ∘g ⊗ᵐ-map {A' = S} {B' = S} {C' = P ⊗ᵐ Q} {D' = Q ⊗ᵐ P}
             idg (⊗ᵐ-comm Sy {P = P} {Q = Q})
    ∘g ⊗ᵐ-comm Sy {P = P ⊗ᵐ Q} {Q = S}
