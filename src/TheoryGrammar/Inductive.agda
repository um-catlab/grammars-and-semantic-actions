{-
  GENERIC INDUCTIVE TYPES over a substrate.

  The functor language: a `Functor s` is a description built from
  constants, nonterminal references, indexed sums and products, and the
  MULTIPLICATIVES OF THE THEORY -- one `⊗e` per operation, of that
  operation's arity.  So the grammar-functor language is generic in the
  theory exactly as the connectives are.

  `μ` is presented in CONTAINER form -- shapes, positions, next-index as
  three mutually-defined functions, rather than as a datatype over the
  defined interpretation `⟦_⟧`.  That is what buys the absence of
  pragmas: `Grammar/Inductive/Indexed.agda` needs NO_POSITIVITY_CHECK
  (its `μ` is over the opaque, defined `⟦_⟧`) and TERMINATING on the
  recursor; neither is needed here, because `Sh`/`Pos`/`nx` are
  structural recursions on the description and `μ` is a plain indexed
  datatype over them.

  Kleene star, list-like grammars, and every other recursive grammar are
  instances -- see `TheoryGrammar.Instances.Strings.KleeneStar`, where `KL*` is
  `μ` of `ε ⊕ (A ⊗ Var)` and NOT a hand-written datatype.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Inductive where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty using (⊥*)

open import TheoryGrammar.Base
open import TheoryGrammar.Substrate

private variable ℓS ℓ ℓ' ℓX ℓP ℓA ℓB ℓV : Level

module Ind {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
           (Sub : Substrate σ ℓX ℓP) (ℓA : Level)
           (X : Type ℓV) (xs : X → S) where

  open SubNotation Sub

  -- an index is a nonterminal together with a point of its sort
  Ix : Type (ℓ-max ℓV ℓX)
  Ix = Σ[ x ∈ X ] Sub .carrier (xs x)

  private
    ℓF : Level
    ℓF = ℓ-max ℓS (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓV (ℓ-max ℓX (ℓ-suc ℓA)))))

  -- ================================================================
  -- Descriptions.
  -- ================================================================

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

  -- ================================================================
  -- Container semantics: shapes, positions, next index.
  -- ================================================================

  Sh : {s : S} → Functor s → Sub .carrier s → Type ℓSh
  Sh (⌜ A ⌝)   m = Lift (ℓ-max ℓ' ℓP) (A m)
  Sh (Var x)   m = Unit*
  Sh (⊕e Y G)  m = Σ[ y ∈ Y ] Sh (G y) m
  Sh (&e Y G)  m = (y : Y) → Sh (G y) m
  Sh (⊗e o G)  m = Σ[ sp ∈ Sub .Split o m ]
                     ((a : σ .arities o) → Sh (G a) (Sub .parts o m sp a))

  Pos : {s : S} (F : Functor s) (m : Sub .carrier s) → Sh F m → Type ℓPos
  Pos (⌜ A ⌝)  m sh        = ⊥*
  Pos (Var x)  m sh        = Unit*
  Pos (⊕e Y G) m (y , sh)  = Pos (G y) m sh
  Pos (&e Y G) m sh        = Σ[ y ∈ Y ] Pos (G y) m (sh y)
  Pos (⊗e o G) m (sp , sh) = Σ[ a ∈ σ .arities o ] Pos (G a) _ (sh a)

  nx : {s : S} (F : Functor s) (m : Sub .carrier s) (sh : Sh F m)
     → Pos F m sh → Ix
  nx (Var x)  m sh        p       = x , m
  nx (⊕e Y G) m (y , sh)  p       = nx (G y) m sh p
  nx (&e Y G) m sh        (y , p) = nx (G y) m (sh y) p
  nx (⊗e o G) m (sp , sh) (a , p) = nx (G a) _ (sh a) p

  -- ================================================================
  -- The least fixed point.  No pragmas.
  -- ================================================================

  data μ (F : (x : X) → Functor (xs x)) : Ix → Type ℓμ where
    sup : {x : X} {m : Sub .carrier (xs x)}
        → (sh : Sh (F x) m)
        → ((p : Pos (F x) m sh) → μ F (nx (F x) m sh p))
        → μ F (x , m)

  module _ {F : (x : X) → Functor (xs x)} where

    -- one-step unfolding: μ is an algebra, definitionally
    unroll : {x : X} {m : Sub .carrier (xs x)} → μ F (x , m)
           → Σ[ sh ∈ Sh (F x) m ] ((p : Pos (F x) m sh) → μ F (nx (F x) m sh p))
    unroll (sup sh f) = sh , f

    roll : {x : X} {m : Sub .carrier (xs x)}
         → Σ[ sh ∈ Sh (F x) m ] ((p : Pos (F x) m sh) → μ F (nx (F x) m sh p))
         → μ F (x , m)
    roll (sh , f) = sup sh f

    roll-unroll : {x : X} {m : Sub .carrier (xs x)} (t : μ F (x , m))
                → roll (unroll t) ≡ t
    roll-unroll (sup sh f) = refl

    unroll-roll : {x : X} {m : Sub .carrier (xs x)}
                  (t : Σ[ sh ∈ Sh (F x) m ] _)
                → unroll (roll t) ≡ t
    unroll-roll t = refl

    -- the recursor: an algebra over an arbitrary motive
    fold : {ℓM : Level} (M : Ix → Type ℓM)
         → ((x : X) (m : Sub .carrier (xs x)) (sh : Sh (F x) m)
            → ((p : Pos (F x) m sh) → M (nx (F x) m sh p)) → M (x , m))
         → (i : Ix) → μ F i → M i
    fold M α (x , m) (sup sh f) = α x m sh (λ p → fold M α _ (f p))

  -- ================================================================
  -- The description AS AN ENDOFUNCTOR on families over Ix, with
  -- algebras and coalgebras.  This is what `Functor Fam Fam` needs to
  -- be fed in ccl's `LocallyContractiveFam`, whose `Fam` is families
  -- over the objects of a category -- here, over `Ix`.
  --
  -- Note the map action does NOT touch shapes: for a container,
  -- `Fmap h (sh , f) = (sh , h ∘ f)`.  So functoriality is refl, and --
  -- more importantly -- the strength needed for local contractivity
  -- has to supply nothing except a proof that each position's next
  -- index is STRICTLY smaller.  See `Guarded` below.
  -- ================================================================

  ⟦_⟧ : {ℓM : Level} {s : S} → Functor s → (Ix → Type ℓM)
      → Sub .carrier s → Type (ℓ-max ℓSh (ℓ-max ℓPos ℓM))
  ⟦ F ⟧ A m = Σ[ sh ∈ Sh F m ] ((p : Pos F m sh) → A (nx F m sh p))

  Fmap : {ℓM ℓN : Level} {A : Ix → Type ℓM} {B : Ix → Type ℓN} {s : S}
         (F : Functor s)
       → ((i : Ix) → A i → B i)
       → (m : Sub .carrier s) → ⟦ F ⟧ A m → ⟦ F ⟧ B m
  Fmap F h m (sh , f) = sh , λ p → h _ (f p)

  Fmap-id : {ℓM : Level} {A : Ix → Type ℓM} {s : S} (F : Functor s)
            (m : Sub .carrier s) (t : ⟦ F ⟧ A m)
          → Fmap {A = A} {B = A} F (λ _ x → x) m t ≡ t
  Fmap-id F m t = refl

  Fmap-∘ : {ℓM ℓN ℓO : Level}
           {A : Ix → Type ℓM} {B : Ix → Type ℓN} {C : Ix → Type ℓO}
           {s : S} (F : Functor s)
           (g : (i : Ix) → B i → C i) (h : (i : Ix) → A i → B i)
           (m : Sub .carrier s) (t : ⟦ F ⟧ A m)
         → Fmap F (λ i x → g i (h i x)) m t ≡ Fmap F g m (Fmap F h m t)
  Fmap-∘ F g h m t = refl

  -- algebras and coalgebras, internal to families over Ix
  module _ (F : (x : X) → Functor (xs x)) where

    Alg : {ℓM : Level} → (Ix → Type ℓM) → Type _
    Alg A = (x : X) (m : Sub .carrier (xs x)) → ⟦ F x ⟧ A m → A (x , m)

    Coalg : {ℓM : Level} → (Ix → Type ℓM) → Type _
    Coalg A = (x : X) (m : Sub .carrier (xs x)) → A (x , m) → ⟦ F x ⟧ A m

    -- μ is an algebra, definitionally, and `fold` is the map out of it
    μ-alg : Alg (μ F)
    μ-alg x m (sh , f) = sup sh f

    μ-coalg : Coalg (μ F)
    μ-coalg x m (sup sh f) = sh , f

  -- ================================================================
  -- THE CONNECTIVE INTERPRETATION.
  --
  -- `⟦_⟧` above is the CONTAINER form: it names the recursive positions,
  -- which is what lets guardedness be stated, but it is not something a
  -- user should ever write a term against -- doing so means matching on
  -- `Sh`/`Pos` and threading `tt*` by hand.
  --
  -- `⟦_⟧c` is the same functor spelled in the CONNECTIVES of the
  -- calculus: a description's ⊕e really is ⊕ᴰ, its ⊗e really is ⊗ˢ.  So
  -- coalgebras and algebras get written with the intro and elim rules --
  -- internally -- and `toC`/`fromC` move between the two presentations.
  --
  -- Motives sit at ℓSh so that `Var` needs no coercion; only the
  -- constant former carries a `Lift`, exactly as `Sh` does.
  -- ================================================================

  ⟦_⟧c : {s : S} → Functor s → (Ix → Type ℓSh) → Sub .carrier s → Type ℓSh
  ⟦ ⌜ B ⌝  ⟧c A m = Lift (ℓ-max ℓ' ℓP) (B m)
  ⟦ Var x  ⟧c A m = A (x , m)
  ⟦ ⊕e Y G ⟧c A m = Σ[ y ∈ Y ] ⟦ G y ⟧c A m
  ⟦ &e Y G ⟧c A m = (y : Y) → ⟦ G y ⟧c A m
  ⟦ ⊗e o G ⟧c A m = Σ[ sp ∈ Sub .Split o m ]
                      ((a : σ .arities o) → ⟦ G a ⟧c A (Sub .parts o m sp a))

  toC : {A : Ix → Type ℓSh} {s : S} (F : Functor s) (m : Sub .carrier s)
      → ⟦ F ⟧ A m → ⟦ F ⟧c A m
  toC ⌜ B ⌝    m (b , _)        = b
  toC (Var x)  m (sh , f)       = f tt*
  toC (⊕e Y G) m ((y , sh) , f) = y , toC (G y) m (sh , f)
  toC (&e Y G) m (sh , f)       = λ y → toC (G y) m (sh y , λ p → f (y , p))
  toC (⊗e o G) m ((sp , sh) , f) =
    sp , λ a → toC (G a) _ (sh a , λ p → f (a , p))

  fromC : {A : Ix → Type ℓSh} {s : S} (F : Functor s) (m : Sub .carrier s)
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
  AlgC F B = (x : X) (m : Sub .carrier (xs x)) → ⟦ F x ⟧c B m → B (x , m)

  CoalgC : (F : (x : X) → Functor (xs x)) → (Ix → Type ℓSh) → Type _
  CoalgC F A = (x : X) (m : Sub .carrier (xs x)) → A (x , m) → ⟦ F x ⟧c A m

  -- THE RECURSOR, against a connective-form algebra.  `fold` is stated
  -- with `Sh`/`Pos`, which is not what an algebra should ever be written
  -- against, so every consumer was re-deriving this one line by hand --
  -- `Dirichlet.Factorization.foldC`, `Lambda.Passes.Framework.runPass`,
  -- `Lambda.DeBruijn.toDB`, `SimplyTyped.Unique`.  It is `fold` composed
  -- with `toC`, and nothing else.
  foldC : {F : (x : X) → Functor (xs x)} (B : Ix → Type ℓSh)
        → AlgC F B → (i : Ix) → μ F i → B i
  foldC {F = F} B α = fold B λ x m sh f → α x m (toC (F x) m (sh , f))

  -- The shape underlying a connective-form element (the payload erased).
  -- This is what lets guardedness -- which is stated with Pos/nx -- be
  -- applied to a term written against the connectives, WITHOUT the
  -- container round trip (which is not definitionally the identity: the
  -- ⊗e case rebuilds a function over the arity, and arities have no η).
  shapeOf : {A : Ix → Type ℓSh} {s : S} (F : Functor s) (m : Sub .carrier s)
          → ⟦ F ⟧c A m → Sh F m
  shapeOf ⌜ B ⌝    m b       = b
  shapeOf (Var x)  m a       = tt*
  shapeOf (⊕e Y G) m (y , t) = y , shapeOf (G y) m t
  shapeOf (&e Y G) m h       = λ y → shapeOf (G y) m (h y)
  shapeOf (⊗e o G) m (sp , h) = sp , λ a → shapeOf (G a) _ (h a)
