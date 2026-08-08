{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- THE DUAL OF A DESCRIPTION -- refutations, as data. -}
module TheoryGrammar.Inductive.Dual where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty as E using (⊥; ⊥*)

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive

private variable ℓS ℓ ℓ' ℓX ℓP ℓA ℓB ℓV ℓM ℓN ℓO : Level

module Dual {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
            (Fib : Fibered σ ℓX ℓP) (ℓA : Level)
            (X : Type ℓV) (xs : X → S) where

  open Ind Fib ℓA X xs public

  private
    Car : (s : S) → Type ℓX
    Car = Fib .carrier

  -- THE DUAL CONTAINER.  Compare `Inductive`'s clauses line for line:
  -- `⊕e`/`&e` swap, `⊗e` dualises, and `⌜ B ⌝` negates.

  ℓPos⁻ : Level
  ℓPos⁻ = ℓ-max ℓP ℓPos           -- see the header: cuts, not slots

  Sh⁻ : {s : S} → Functor s → Car s → Type ℓSh
  Sh⁻ (⌜ A ⌝)   m = Lift (ℓ-max ℓ' ℓP) (A m → ⊥)
  Sh⁻ (Var x)   m = Unit*
  Sh⁻ (⊕e Y G)  m = (y : Y) → Sh⁻ (G y) m
  Sh⁻ (&e Y G)  m = Σ[ y ∈ Y ] Sh⁻ (G y) m
  Sh⁻ (⊗e o G)  m = (sp : Fib .Split o m)
                  → Σ[ a ∈ σ .arities o ] Sh⁻ (G a) (Fib .parts o m sp a)

  Pos⁻ : {s : S} (F : Functor s) (m : Car s) → Sh⁻ F m → Type ℓPos⁻
  Pos⁻ (⌜ A ⌝)  m sh       = ⊥*
  Pos⁻ (Var x)  m sh       = Unit*
  Pos⁻ (⊕e Y G) m sh       = Σ[ y ∈ Y ] Pos⁻ (G y) m (sh y)
  Pos⁻ (&e Y G) m (y , sh) = Pos⁻ (G y) m sh
  Pos⁻ (⊗e o G) m sh       =
    Σ[ sp ∈ Fib .Split o m ] Pos⁻ (G (sh sp .fst)) _ (sh sp .snd)

  nx⁻ : {s : S} (F : Functor s) (m : Car s) (sh : Sh⁻ F m)
      → Pos⁻ F m sh → Ix
  nx⁻ (Var x)  m sh       p        = x , m
  nx⁻ (⊕e Y G) m sh       (y , p)  = nx⁻ (G y) m (sh y) p
  nx⁻ (&e Y G) m (y , sh) p        = nx⁻ (G y) m sh p
  nx⁻ (⊗e o G) m sh       (sp , p) = nx⁻ (G (sh sp .fst)) _ (sh sp .snd) p

  ℓμ⁻ : Level
  ℓμ⁻ = ℓ-max ℓSh (ℓ-max ℓPos⁻ (ℓ-max ℓV ℓX))

  -- THE REFUTATIONS.  A `data`, for the same reason `μ` is one: `Sh⁻`,
  -- `Pos⁻`, `nx⁻` are structural recursions on the description, so no
  -- positivity or termination pragma is needed.
  data μ⁻ (F : (x : X) → Functor (xs x)) : Ix → Type ℓμ⁻ where
    sup⁻ : {x : X} {m : Car (xs x)}
         → (sh : Sh⁻ (F x) m)
         → ((p : Pos⁻ (F x) m sh) → μ⁻ F (nx⁻ (F x) m sh p))
         → μ⁻ F (x , m)

  module _ {F : (x : X) → Functor (xs x)} where

    unroll⁻ : {x : X} {m : Car (xs x)} → μ⁻ F (x , m)
            → Σ[ sh ∈ Sh⁻ (F x) m ]
                ((p : Pos⁻ (F x) m sh) → μ⁻ F (nx⁻ (F x) m sh p))
    unroll⁻ (sup⁻ sh f) = sh , f

    roll⁻ : {x : X} {m : Car (xs x)}
          → Σ[ sh ∈ Sh⁻ (F x) m ]
              ((p : Pos⁻ (F x) m sh) → μ⁻ F (nx⁻ (F x) m sh p))
          → μ⁻ F (x , m)
    roll⁻ (sh , f) = sup⁻ sh f

    roll-unroll⁻ : {x : X} {m : Car (xs x)} (t : μ⁻ F (x , m))
                 → roll⁻ (unroll⁻ t) ≡ t
    roll-unroll⁻ (sup⁻ sh f) = refl

  -- ONE LAYER, both polarities, in the form `sup` / `sup⁻` consume.

  Layer⁺ : {s : S} (F : Functor s) (A : Ix → Type ℓM) (m : Car s) → Type _
  Layer⁺ F A m = Σ[ sh ∈ Sh F m ] ((p : Pos F m sh) → A (nx F m sh p))

  Layer⁻ : {s : S} (F : Functor s) (A : Ix → Type ℓM) (m : Car s) → Type _
  Layer⁻ F A m = Σ[ sh ∈ Sh⁻ F m ] ((p : Pos⁻ F m sh) → A (nx⁻ F m sh p))

  -- THE DIRECT INTERPRETATION, AT A GENERAL MOTIVE LEVEL -- and the one
  -- iso that replaces every ad-hoc Σ-shuffle downstream.

  -- the level is EXPLICIT: the two `Lift`s mention it, and a
  -- generalisable variable is not in scope in a clause body
  DirC : (ℓM : Level) {s : S} → Functor s → (Ix → Type ℓM) → Car s
       → Type (ℓ-max ℓSh ℓM)
  DirC ℓM (⌜ B ⌝)  A m = Lift (ℓ-max ℓSh ℓM) (B m)
  DirC ℓM (Var x)  A m = Lift (ℓ-max ℓSh ℓM) (A (x , m))
  DirC ℓM (⊕e Y G) A m = Σ[ y ∈ Y ] DirC ℓM (G y) A m
  DirC ℓM (&e Y G) A m = (y : Y) → DirC ℓM (G y) A m
  DirC ℓM (⊗e o G) A m = Σ[ sp ∈ Fib .Split o m ]
                           ((a : σ .arities o) → DirC ℓM (G a) A (Fib .parts o m sp a))

  -- THE ISO.  `Inductive.toC` / `fromC` at a general motive; the clauses
  -- are theirs, with the two lifts added.
  layerTo : {A : Ix → Type ℓM} {s : S} (F : Functor s) (m : Car s)
          → Layer⁺ F A m → DirC _ F A m
  layerTo (⌜ B ⌝)  m (b , _)         = lift (lower b)
  layerTo (Var x)  m (sh , f)        = lift (f tt*)
  layerTo (⊕e Y G) m ((y , sh) , f)  = y , layerTo (G y) m (sh , f)
  layerTo (&e Y G) m (sh , f)        = λ y → layerTo (G y) m (sh y , λ p → f (y , p))
  layerTo (⊗e o G) m ((sp , sh) , f) =
    sp , λ a → layerTo (G a) _ (sh a , λ p → f (a , p))

  layerFrom : {A : Ix → Type ℓM} {s : S} (F : Functor s) (m : Car s)
            → DirC _ F A m → Layer⁺ F A m
  layerFrom (⌜ B ⌝)  m b       = lift (lower b) , λ ()
  layerFrom (Var x)  m a       = tt* , λ _ → lower a
  layerFrom (⊕e Y G) m (y , t) =
    (y , layerFrom (G y) m t .fst) , layerFrom (G y) m t .snd
  layerFrom (&e Y G) m g =
    (λ y → layerFrom (G y) m (g y) .fst)
    , λ { (y , p) → layerFrom (G y) m (g y) .snd p }
  layerFrom (⊗e o G) m (sp , h) =
    (sp , λ a → layerFrom (G a) _ (h a) .fst)
    , λ { (a , p) → layerFrom (G a) _ (h a) .snd p }

  -- WHERE A DESCRIPTION'S RECURSIVE POSITIONS LAND, structurally.

  Reaches : {s : S} (F : Functor s) (m : Car s) (Ok : Ix → Type ℓO)
          → Type (ℓ-max ℓSh ℓO)
  Reaches (⌜ A ⌝)  m Ok = Unit*
  Reaches (Var x)  m Ok = Lift ℓSh (Ok (x , m))
  Reaches (⊕e Y G) m Ok = (y : Y) → Reaches (G y) m Ok
  Reaches (&e Y G) m Ok = (y : Y) → Reaches (G y) m Ok
  Reaches (⊗e o G) m Ok =
    (sp : Fib .Split o m)
    → ((a : σ .arities o) → Sh (G a) (Fib .parts o m sp a))
    → (a : σ .arities o) → Reaches (G a) (Fib .parts o m sp a) Ok

  -- ... AND FOR REFUTATIONS.
  Reaches⁻ : {s : S} (F : Functor s) (m : Car s) (Ok : Ix → Type ℓO)
           → Type (ℓ-max ℓSh ℓO)
  Reaches⁻ (⌜ A ⌝)  m Ok = Unit*
  Reaches⁻ (Var x)  m Ok = Lift ℓSh (Ok (x , m))
  Reaches⁻ (⊕e Y G) m Ok = (y : Y) → Reaches⁻ (G y) m Ok
  Reaches⁻ (&e Y G) m Ok = (y : Y) → Reaches⁻ (G y) m Ok
  Reaches⁻ (⊗e o G) m Ok =
    (sp : Fib .Split o m) (a : σ .arities o)
    → Sh⁻ (G a) (Fib .parts o m sp a)
    → Reaches⁻ (G a) (Fib .parts o m sp a) Ok

  -- T1. THE LAYERS ARE EXCLUSIVE.

  excl : {A⁺ : Ix → Type ℓM} {A⁻ : Ix → Type ℓN} {Ok : Ix → Type ℓO}
       → ((i : Ix) → Ok i → A⁺ i → A⁻ i → ⊥)
       → {s : S} (F : Functor s) (m : Car s)
       → Reaches F m Ok → Reaches⁻ F m Ok
       → Layer⁺ F A⁺ m → Layer⁻ F A⁻ m → ⊥

  excl h (⌜ A ⌝) m _ _ (lift a , _) (lift k , _) = k a

  excl h (Var x) m ok _ (_ , f) (_ , g) = h (x , m) (lower ok) (f tt*) (g tt*)

  -- the positive names an alternative; the negative refutes every one
  excl h (⊕e Y G) m rp rn ((y , sh) , f) (shN , g) =
    excl h (G y) m (rp y) (rn y) (sh , f) (shN y , λ p → g (y , p))

  -- dually: the negative names a conjunct; the positive proves every one
  excl h (&e Y G) m rp rn (sh , f) ((y , shN) , g) =
    excl h (G y) m (rp y) (rn y) (sh y , λ p → f (y , p)) (shN , g)

  -- the positive names the splitting `sp`; the negative, applied there,
  -- names the offending slot `a`.
  excl h (⊗e o G) m rp rn ((sp , sh) , f) (shN , g) =
    excl h (G a) _ (rp sp sh a) (rn sp a shNa)
         (sh a , λ p → f (a , p))
         (shNa , λ p → g (sp , p))
    where
      a    = shN sp .fst
      shNa = shN sp .snd
