{-
  The generic layer, in CONTAINER form.

  Grammar.GenericInductive defined μ over the defined function ⟦_⟧F,
  which cost NO_POSITIVITY_CHECK and TERMINATING.  Here the functor
  syntax is compiled to shapes/positions/next-index, and μ is a genuine
  indexed W-type:

      data μ F : I → Type where
        sup : (sh : Sh …) → ((p : Pos … sh) → μ F (nx … p)) → μ F i

  μ occurs only in the codomain of a function whose domain does not
  mention it, so positivity passes; and `rec` recurses on `f p`, a
  structural subterm, so termination passes.  No pragmas.
-}
module Grammar.GenericContainer where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥*)

record Sig ℓ : Type (ℓ-suc ℓ) where
  field
    Sort    : Type ℓ
    Op      : Type ℓ
    arity   : Op → Type ℓ
    argSort : (o : Op) → arity o → Sort
    resSort : Op → Sort

open Sig

-- A Base is itself a CONTAINER: shapes indexed by the OUTPUT, with the
-- argument components as PROJECTIONS.  Indexing Split by the components
-- (as a function) is what made splittings unmatchable; indexing by the
-- output makes `Split o m` an ordinary inductive family that the
-- substrate can case-split on, and `parts` computes on its constructors.
record Base {ℓ} (Σ : Sig ℓ) : Type (ℓ-suc ℓ) where
  field
    carrier : Σ .Sort → Type ℓ
    Split   : (o : Σ .Op) → carrier (Σ .resSort o) → Type ℓ
    parts   : (o : Σ .Op) (m : carrier (Σ .resSort o))
            → Split o m → (a : Σ .arity o) → carrier (Σ .argSort o a)

open Base

module Generic {ℓ} (Σ : Sig ℓ) (B : Base Σ) where

  Gr : Σ .Sort → Type (ℓ-suc ℓ)
  Gr s = B .carrier s → Type ℓ

  module Fam (X : Type ℓ) (xs : X → Σ .Sort) where

    -- the index of the mutual inductive: a nonterminal and a substrate element
    Ix : Type ℓ
    Ix = Σ[ x ∈ X ] B .carrier (xs x)

    data SPF : Σ .Sort → Type (ℓ-suc ℓ) where
      k   : ∀ {s} → Gr s → SPF s
      Var : (x : X) → SPF (xs x)
      ⊕e  : ∀ {s} (Y : Type ℓ) → (Y → SPF s) → SPF s
      &e  : ∀ {s} (Y : Type ℓ) → (Y → SPF s) → SPF s
      ⊗e  : (o : Σ .Op)
          → ((a : Σ .arity o) → SPF (Σ .argSort o a))
          → SPF (Σ .resSort o)

    -- compile the syntax to container data
    Sh : ∀ {s} → SPF s → B .carrier s → Type ℓ
    Sh (k A)     m = A m
    Sh (Var x)   m = Unit*
    Sh (⊕e Y G)  m = Σ[ y ∈ Y ] Sh (G y) m
    Sh (&e Y G)  m = (y : Y) → Sh (G y) m
    Sh (⊗e o G)  m =
      Σ[ sp ∈ B .Split o m ]
        ((a : Σ .arity o) → Sh (G a) (B .parts o m sp a))

    Pos : ∀ {s} (G : SPF s) (m : B .carrier s) → Sh G m → Type ℓ
    Pos (k A)    m sh            = ⊥*
    Pos (Var x)  m sh            = Unit*
    Pos (⊕e Y G) m (y , sh)      = Pos (G y) m sh
    Pos (&e Y G) m f             = Σ[ y ∈ Y ] Pos (G y) m (f y)
    Pos (⊗e o G) m (sp , shs) =
      Σ[ a ∈ Σ .arity o ] Pos (G a) (B .parts o m sp a) (shs a)

    nx : ∀ {s} (G : SPF s) (m : B .carrier s) (sh : Sh G m) → Pos G m sh → Ix
    nx (Var x)  m sh _            = x , m
    nx (⊕e Y G) m (y , sh) p      = nx (G y) m sh p
    nx (&e Y G) m f (y , p)       = nx (G y) m (f y) p
    nx (⊗e o G) m (sp , shs) (a , p) =
      nx (G a) (B .parts o m sp a) (shs a) p

    -- the container extension: this is ⟦_⟧F, now derived
    ⟦_⟧F : ∀ {s} → SPF s → (Ix → Type ℓ) → B .carrier s → Type ℓ
    ⟦ G ⟧F P m = Σ[ sh ∈ Sh G m ] ((p : Pos G m sh) → P (nx G m sh p))

    -- μ as a genuine indexed W-type.  No pragmas.
    data μ (F : (x : X) → SPF (xs x)) : Ix → Type ℓ where
      sup : ∀ {x m} (sh : Sh (F x) m)
          → ((p : Pos (F x) m sh) → μ F (nx (F x) m sh p))
          → μ F (x , m)

    module _ {F : (x : X) → SPF (xs x)} {A : Ix → Type ℓ}
             (α : ∀ x m (sh : Sh (F x) m)
                → ((p : Pos (F x) m sh) → A (nx (F x) m sh p))
                → A (x , m)) where
      fold : ∀ i → μ F i → A i
      fold (x , m) (sup sh f) = α x m sh (λ p → fold _ (f p))

    -- the initial-algebra isomorphism, ONCE, generically.  Every
    -- instance's "recurrence" is this plus facts about its shapes.
    module _ {F : (x : X) → SPF (xs x)} where
      unroll : ∀ {x m} → μ F (x , m) → ⟦ F x ⟧F (μ F) m
      unroll (sup sh f) = sh , f

      roll : ∀ {x m} → ⟦ F x ⟧F (μ F) m → μ F (x , m)
      roll (sh , f) = sup sh f

      unroll-roll : ∀ {x m} (t : ⟦ F x ⟧F (μ F) m) → unroll {x} {m} (roll t) ≡ t
      unroll-roll (sh , f) = refl

      roll-unroll : ∀ {x m} (t : μ F (x , m)) → roll (unroll t) ≡ t
      roll-unroll (sup sh f) = refl
