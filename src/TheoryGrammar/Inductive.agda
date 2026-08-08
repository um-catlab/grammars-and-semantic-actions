{- GENERIC INDUCTIVE TYPES over a `Fibered`. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Inductive where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥*)

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered

private variable ℓS ℓ ℓ' ℓX ℓP ℓA ℓB ℓV ℓA' : Level

module Ind {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
           (Fib : Fibered σ ℓX ℓP) (ℓA : Level)
           (X : Type ℓV) (xs : X → S) where

  open FibNotation Fib

  -- an index is a nonterminal together with a point of its sort
  Ix : Type (ℓ-max ℓV ℓX)
  Ix = Σ[ x ∈ X ] Fib .carrier (xs x)

  private
    ℓF : Level
    ℓF = ℓ-max ℓS (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓV (ℓ-max ℓX (ℓ-suc ℓA)))))

  -- Descriptions.

  data Functor : S → Type ℓF where
    ⌜_⌝  : {s : S} → TheoryTy ℓA s → Functor s          -- constant
    Var  : (x : X) → Functor (xs x)                     -- nonterminal
    ⊕e   : {s : S} (Y : Type ℓA) → (Y → Functor s) → Functor s
    &e   : {s : S} (Y : Type ℓA) → (Y → Functor s) → Functor s
    ⊗e   : (o : σ .ops) → ((a : σ .arities o) → Functor (σ .sortOf o a))
         → Functor (σ .resultSort o)

  ℓSh ℓPos ℓμ : Level
  ℓSh  = ℓ-max ℓ' (ℓ-max ℓP ℓA)
  ℓPos = ℓ-max ℓ' ℓA
  ℓμ   = ℓ-max ℓSh (ℓ-max ℓV ℓX)

  -- Container semantics: shapes, positions, next index.

  Sh : {s : S} → Functor s → Fib .carrier s → Type ℓSh
  Sh (⌜ A ⌝)   m = Lift (ℓ-max ℓ' ℓP) (A m)
  Sh (Var x)   m = Unit*
  Sh (⊕e Y G)  m = Σ[ y ∈ Y ] Sh (G y) m
  Sh (&e Y G)  m = (y : Y) → Sh (G y) m
  Sh (⊗e o G)  m = Σ[ sp ∈ Fib .Split o m ]
                     ((a : σ .arities o) → Sh (G a) (Fib .parts o m sp a))

  Pos : {s : S} (F : Functor s) (m : Fib .carrier s) → Sh F m → Type ℓPos
  Pos (⌜ A ⌝)  m sh        = ⊥*
  Pos (Var x)  m sh        = Unit*
  Pos (⊕e Y G) m (y , sh)  = Pos (G y) m sh
  Pos (&e Y G) m sh        = Σ[ y ∈ Y ] Pos (G y) m (sh y)
  Pos (⊗e o G) m (sp , sh) = Σ[ a ∈ σ .arities o ] Pos (G a) _ (sh a)

  nx : {s : S} (F : Functor s) (m : Fib .carrier s) (sh : Sh F m)
     → Pos F m sh → Ix
  nx (Var x)  m sh        p       = x , m
  nx (⊕e Y G) m (y , sh)  p       = nx (G y) m sh p
  nx (&e Y G) m sh        (y , p) = nx (G y) m (sh y) p
  nx (⊗e o G) m (sp , sh) (a , p) = nx (G a) _ (sh a) p

  -- The least fixed point.  No pragmas.

  data μ (F : (x : X) → Functor (xs x)) : Ix → Type ℓμ where
    sup : {x : X} {m : Fib .carrier (xs x)}
        → (sh : Sh (F x) m)
        → ((p : Pos (F x) m sh) → μ F (nx (F x) m sh p))
        → μ F (x , m)

  module _ {F : (x : X) → Functor (xs x)} where

    -- one-step unfolding: μ is an algebra, definitionally
    unroll : {x : X} {m : Fib .carrier (xs x)} → μ F (x , m)
           → Σ[ sh ∈ Sh (F x) m ] ((p : Pos (F x) m sh) → μ F (nx (F x) m sh p))
    unroll (sup sh f) = sh , f

    roll : {x : X} {m : Fib .carrier (xs x)}
         → Σ[ sh ∈ Sh (F x) m ] ((p : Pos (F x) m sh) → μ F (nx (F x) m sh p))
         → μ F (x , m)
    roll (sh , f) = sup sh f

    roll-unroll : {x : X} {m : Fib .carrier (xs x)} (t : μ F (x , m))
                → roll (unroll t) ≡ t
    roll-unroll (sup sh f) = refl

    unroll-roll : {x : X} {m : Fib .carrier (xs x)}
                  (t : Σ[ sh ∈ Sh (F x) m ] _)
                → unroll (roll t) ≡ t
    unroll-roll t = refl

    -- the recursor: an algebra over an arbitrary motive
    fold : {ℓM : Level} (M : Ix → Type ℓM)
         → ((x : X) (m : Fib .carrier (xs x)) (sh : Sh (F x) m)
            → ((p : Pos (F x) m sh) → M (nx (F x) m sh p)) → M (x , m))
         → (i : Ix) → μ F i → M i
    fold M α (x , m) (sup sh f) = α x m sh (λ p → fold M α _ (f p))

  -- The description AS AN ENDOFUNCTOR on families over Ix, with algebras
  -- and coalgebras.

  ⟦_⟧ : {ℓM : Level} {s : S} → Functor s → (Ix → Type ℓM)
      → Fib .carrier s → Type (ℓ-max ℓSh (ℓ-max ℓPos ℓM))
  ⟦ F ⟧ A m = Σ[ sh ∈ Sh F m ] ((p : Pos F m sh) → A (nx F m sh p))

  Fmap : {ℓM ℓN : Level} {A : Ix → Type ℓM} {B : Ix → Type ℓN} {s : S}
         (F : Functor s)
       → ((i : Ix) → A i → B i)
       → (m : Fib .carrier s) → ⟦ F ⟧ A m → ⟦ F ⟧ B m
  Fmap F h m (sh , f) = sh , λ p → h _ (f p)

  Fmap-id : {ℓM : Level} {A : Ix → Type ℓM} {s : S} (F : Functor s)
            (m : Fib .carrier s) (t : ⟦ F ⟧ A m)
          → Fmap {A = A} {B = A} F (λ _ x → x) m t ≡ t
  Fmap-id F m t = refl

  Fmap-∘ : {ℓM ℓN ℓO : Level}
           {A : Ix → Type ℓM} {B : Ix → Type ℓN} {C : Ix → Type ℓO}
           {s : S} (F : Functor s)
           (g : (i : Ix) → B i → C i) (h : (i : Ix) → A i → B i)
           (m : Fib .carrier s) (t : ⟦ F ⟧ A m)
         → Fmap F (λ i x → g i (h i x)) m t ≡ Fmap F g m (Fmap F h m t)
  Fmap-∘ F g h m t = refl

  -- algebras and coalgebras, internal to families over Ix
  module _ (F : (x : X) → Functor (xs x)) where

    Alg : {ℓM : Level} → (Ix → Type ℓM) → Type _
    Alg A = (x : X) (m : Fib .carrier (xs x)) → ⟦ F x ⟧ A m → A (x , m)

    Coalg : {ℓM : Level} → (Ix → Type ℓM) → Type _
    Coalg A = (x : X) (m : Fib .carrier (xs x)) → A (x , m) → ⟦ F x ⟧ A m

    -- μ is an algebra, definitionally, and `fold` is the map out of it
    μ-alg : Alg (μ F)
    μ-alg x m (sh , f) = sup sh f

    μ-coalg : Coalg (μ F)
    μ-coalg x m (sup sh f) = sh , f

  -- THE CONNECTIVE INTERPRETATION. `⟦_⟧` above is the CONTAINER form: it
  -- names the recursive positions, which is what lets guardedness be
  -- stated, but it is not something a user should ever write a term
  -- against -- doing so means matching on `Sh`/`Pos` and threading `tt*`
  -- by hand.

  ⟦_⟧c : {s : S} → Functor s → (Ix → Type ℓSh) → Fib .carrier s → Type ℓSh
  ⟦ ⌜ B ⌝  ⟧c A m = Lift (ℓ-max ℓ' ℓP) (B m)
  ⟦ Var x  ⟧c A m = A (x , m)
  ⟦ ⊕e Y G ⟧c A m = Σ[ y ∈ Y ] ⟦ G y ⟧c A m
  ⟦ &e Y G ⟧c A m = (y : Y) → ⟦ G y ⟧c A m
  ⟦ ⊗e o G ⟧c A m = Σ[ sp ∈ Fib .Split o m ]
                      ((a : σ .arities o) → ⟦ G a ⟧c A (Fib .parts o m sp a))

  toC : {A : Ix → Type ℓSh} {s : S} (F : Functor s) (m : Fib .carrier s)
      → ⟦ F ⟧ A m → ⟦ F ⟧c A m
  toC ⌜ B ⌝    m (b , _)        = b
  toC (Var x)  m (sh , f)       = f tt*
  toC (⊕e Y G) m ((y , sh) , f) = y , toC (G y) m (sh , f)
  toC (&e Y G) m (sh , f)       = λ y → toC (G y) m (sh y , λ p → f (y , p))
  toC (⊗e o G) m ((sp , sh) , f) =
    sp , λ a → toC (G a) _ (sh a , λ p → f (a , p))

  fromC : {A : Ix → Type ℓSh} {s : S} (F : Functor s) (m : Fib .carrier s)
        → ⟦ F ⟧c A m → ⟦ F ⟧ A m
  fromC ⌜ B ⌝    m b       = b , λ ()
  fromC (Var x)  m a       = tt* , λ _ → a
  fromC (⊕e Y G) m (y , t) = (y , fromC (G y) m t .fst) , fromC (G y) m t .snd
  fromC (&e Y G) m g =
    (λ y → fromC (G y) m (g y) .fst) , λ { (y , p) → fromC (G y) m (g y) .snd p }
  fromC (⊗e o G) m (sp , h) =
    (sp , λ a → fromC (G a) _ (h a) .fst) , λ { (a , p) → fromC (G a) _ (h a) .snd p }

  -- algebras and coalgebras stated INTERNALLY
  AlgC : (F : (x : X) → Functor (xs x)) → (Ix → Type ℓSh) → Type _
  AlgC F B = (x : X) (m : Fib .carrier (xs x)) → ⟦ F x ⟧c B m → B (x , m)

  CoalgC : (F : (x : X) → Functor (xs x)) → (Ix → Type ℓSh) → Type _
  CoalgC F A = (x : X) (m : Fib .carrier (xs x)) → A (x , m) → ⟦ F x ⟧c A m

  -- THE INTERNAL INTERFACE. `AlgC`/`CoalgC` above are stated pointfully --
  -- they take an element of the carrier and an element of the motive.

  Fam : Type (ℓ-max ℓV (ℓ-max ℓX (ℓ-suc ℓSh)))
  Fam = (x : X) → TheoryTy ℓSh (xs x)

  ⌞_⌟ : Fam → (Ix → Type ℓSh)
  ⌞ A ⌟ i = A (i .fst) (i .snd)

  -- the description's action ON GRAMMARS.  This is the functor.
  ⟦_⟧ᴳ : {s : S} → Functor s → Fam → TheoryTy ℓSh s
  ⟦ F ⟧ᴳ A = ⟦ F ⟧c ⌞ A ⌟

  Algᴳ : ((x : X) → Functor (xs x)) → Fam → Type _
  Algᴳ F A = (x : X) → ⟦ F x ⟧ᴳ A ⊢ A x

  Coalgᴳ : ((x : X) → Functor (xs x)) → Fam → Type _
  Coalgᴳ F A = (x : X) → A x ⊢ ⟦ F x ⟧ᴳ A

  -- the two presentations are the same data, on the nose
  Algᴳ≡ : {F : (x : X) → Functor (xs x)} {A : Fam} → Algᴳ F A ≡ AlgC F ⌞ A ⌟
  Algᴳ≡ = refl

  Coalgᴳ≡ : {F : (x : X) → Functor (xs x)} {A : Fam} → Coalgᴳ F A ≡ CoalgC F ⌞ A ⌟
  Coalgᴳ≡ = refl

  -- the terminal grammar at the motive's level: `⊤G` is the ℓ-zero one,
  -- and this is its lift.  A coalgebra carried by ⊤ is carried by THIS
  -- -- a grammar -- not by a bare `Unit*`.
  ⊤ᴳ : {s : S} → TheoryTy ℓSh s
  ⊤ᴳ _ = Unit*

  ⊤ᴳ-I : {s : S} {A : TheoryTy ℓA' s} → A ⊢ ⊤ᴳ
  ⊤ᴳ-I _ _ = tt*

  -- THE RECURSOR, against a connective-form algebra.
  foldC : {F : (x : X) → Functor (xs x)} (B : Ix → Type ℓSh)
        → AlgC F B → (i : Ix) → μ F i → B i
  foldC {F = F} B α = fold B λ x m sh f → α x m (toC (F x) m (sh , f))

  -- μ IS THE INITIAL ALGEBRA, for every theory.

  μᴳ : ((x : X) → Functor (xs x)) → (x : X) → TheoryTy ℓμ (xs x)
  μᴳ F x m = μ F (x , m)

  foldᴳ : {F : (x : X) → Functor (xs x)} {A : Fam}
        → Algᴳ F A → (x : X) → μᴳ F x ⊢ A x
  foldᴳ {A = A} α x m t = foldC ⌞ A ⌟ α (x , m) t

  fold-unique : {F : (x : X) → Functor (xs x)} {A : Fam}
                (α : Algᴳ F A) (h : (x : X) → μᴳ F x ⊢ A x)
              → ((x : X) (m : Fib .carrier (xs x)) (sh : Sh (F x) m)
                 (f : (p : Pos (F x) m sh) → μ F (nx (F x) m sh p))
                 → h x m (sup sh f)
                 ≡ α x m (toC (F x) m (sh , λ p → h _ _ (f p))))
              → (x : X) (m : Fib .carrier (xs x)) (t : μᴳ F x m)
              → h x m t ≡ foldᴳ α x m t
  fold-unique {F = F} α h hh x m (sup sh f) =
    hh x m sh f
    ∙ cong (λ g → α x m (toC (F x) m (sh , g)))
           (funExt λ p → fold-unique α h hh _ _ (f p))

  -- The shape underlying a connective-form element (the payload erased).
  shapeOf : {A : Ix → Type ℓSh} {s : S} (F : Functor s) (m : Fib .carrier s)
          → ⟦ F ⟧c A m → Sh F m
  shapeOf ⌜ B ⌝    m b       = b
  shapeOf (Var x)  m a       = tt*
  shapeOf (⊕e Y G) m (y , t) = y , shapeOf (G y) m t
  shapeOf (&e Y G) m h       = λ y → shapeOf (G y) m (h y)
  shapeOf (⊗e o G) m (sp , h) = sp , λ a → shapeOf (G a) _ (h a)

  -- WHY `rollg` / `unrollg` CANNOT BE STATED *HERE* -- and where they are
  -- stated instead.

  -- THE GREATEST FIXED POINT. Same container, dualised.

  record ν (F : (x : X) → Functor (xs x)) (i : Ix) : Type ℓμ where
    coinductive
    field
      shOf : Sh (F (i .fst)) (i .snd)
      nxOf : (p : Pos (F (i .fst)) (i .snd) shOf)
           → ν F (nx (F (i .fst)) (i .snd) shOf p)

  open ν public

  module _ {F : (x : X) → Functor (xs x)} where

    -- ν is a coalgebra, definitionally
    νout : (i : Ix) → ν F i → ⟦ F (i .fst) ⟧ (ν F) (i .snd)
    νout i t = t .shOf , t .nxOf

    νinto : (i : Ix) → ⟦ F (i .fst) ⟧ (ν F) (i .snd) → ν F i
    νinto i (sh , f) .shOf = sh
    νinto i (sh , f) .nxOf = f

    νout-νinto : (i : Ix) (t : ⟦ F (i .fst) ⟧ (ν F) (i .snd))
             → νout i (νinto i t) ≡ t
    νout-νinto i t = refl

    νinto-νout : (i : Ix) (t : ν F i) → νinto i (νout i t) ≡ t
    νinto-νout i t j .shOf   = t .shOf
    νinto-νout i t j .nxOf p = t .nxOf p

    -- THE CORECURSOR, against a coalgebra over an arbitrary motive.
    -- Dual to `fold`, and productive by copatterns rather than
    -- terminating by structural descent.
    νunfold : {ℓM : Level} (M : Ix → Type ℓM)
           → ((x : X) (m : Fib .carrier (xs x))
              → M (x , m)
              → Σ[ sh ∈ Sh (F x) m ]
                  ((p : Pos (F x) m sh) → M (nx (F x) m sh p)))
           → (i : Ix) → M i → ν F i
    νunfold M γ i a .shOf   = γ (i .fst) (i .snd) a .fst
    νunfold M γ i a .nxOf p = νunfold M γ _ (γ (i .fst) (i .snd) a .snd p)

    -- ... and its computation rule, on the nose
    νunfold-β : {ℓM : Level} (M : Ix → Type ℓM) (γ : _) (i : Ix) (a : M i)
             → νout i (νunfold M γ i a)
             ≡ Fmap (F (i .fst)) (λ j → νunfold M γ j) (i .snd)
                    (γ (i .fst) (i .snd) a)
    νunfold-β M γ i a = refl

    -- UNIQUENESS OF THE CORECURSOR lives in `Hylo` as `ν-η`, because it
    -- needs guardedness -- and it needs NO pragma.

  -- The corecursor against a CONNECTIVE-form coalgebra -- dual to
  -- `foldC`, and `fromC` where that used `toC`.  Same rationale: a
  -- coalgebra should never be written against `Sh`/`Pos`.
  νunfoldC : {F : (x : X) → Functor (xs x)} (A : Ix → Type ℓSh)
          → CoalgC F A → (i : Ix) → A i → ν F i
  νunfoldC {F = F} A γ =
    νunfold A (λ x m a → fromC (F x) m (γ x m a))
