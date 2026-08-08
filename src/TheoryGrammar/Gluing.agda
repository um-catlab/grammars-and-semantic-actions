{- GLUING TWO `Fibered` ALONG A RELATION. A type of the calculus is a
   family over ONE carrier, so a derivation combining two instances is not
   a new connective: it is `&` over a NEW CARRIER. -}
module TheoryGrammar.Gluing where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.RulesFib
open import TheoryGrammar.CarrierMap

private variable ℓS ℓ ℓ' ℓX ℓX' ℓX₀ ℓP ℓP' ℓP₀ ℓR ℓA ℓA' ℓB ℓB' ℓC : Level

-- A CORRELATION: what the two instances are glued along.

Corr : {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
     → Fibered σ ℓX ℓP → Fibered σ ℓX' ℓP' → (ℓR : Level)
     → Type (ℓ-max ℓS (ℓ-max ℓX (ℓ-max ℓX' (ℓ-suc ℓR))))
Corr {S = S} Fib Fib' ℓR = (s : S) → Fib .carrier s → Fib' .carrier s → Type ℓR

-- THE GLUED `Fibered`.

module Glue {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
            (Fib : Fibered σ ℓX ℓP) (Fib' : Fibered σ ℓX' ℓP')
            (R : Corr Fib Fib' ℓR) where

  -- A splitting of the RIGHT factor DISPLAYED over one of the left: a
  -- right splitting together with the relatedness of the corresponding
  -- parts.
  Splitᴰ : (o : σ .ops) (m : Fib .carrier (σ .resultSort o))
           (m' : Fib' .carrier (σ .resultSort o))
         → Fib .Split o m → Type (ℓ-max ℓP' (ℓ-max ℓ' ℓR))
  Splitᴰ o m m' sp =
    Σ[ sp' ∈ Fib' .Split o m' ]
      ((a : σ .arities o) → R (σ .sortOf o a) (Fib  .parts o m  sp  a)
                                              (Fib' .parts o m' sp' a))

  -- An element is a related pair; a splitting is a left one and a
  -- displayed right one.
  glue : Fibered σ (ℓ-max ℓX (ℓ-max ℓX' ℓR))
                   (ℓ-max ℓP (ℓ-max ℓP' (ℓ-max ℓ' ℓR)))
  glue .carrier s = Σ[ m ∈ Fib .carrier s ] Σ[ m' ∈ Fib' .carrier s ] R s m m'
  glue .Split o g =
    Σ[ sp ∈ Fib .Split o (g .fst) ] Splitᴰ o (g .fst) (g .snd .fst) sp
  glue .parts o g sq a =
      Fib  .parts o (g .fst)      (sq .fst)       a
    , Fib' .parts o (g .snd .fst) (sq .snd .fst)  a
    , sq .snd .snd a

  -- The projections, and the fact that they preserve splittings ON THE
  -- NOSE.  `homParts` is `Eq.refl` -- the reason everything below is
  -- transport-free.

  π₁ : Reindex glue Fib
  π₁ .hom _ g = g .fst

  π₂ : Reindex glue Fib'
  π₂ .hom _ g = g .snd .fst

  π₁-pres : (o : σ .ops) → SplitPresAt π₁ o
  π₁-pres o .homSplit _ sq  = sq .fst
  π₁-pres o .homParts _ _ _ = Eq.refl

  π₂-pres : (o : σ .ops) → SplitPresAt π₂ o
  π₂-pres o .homSplit _ sq  = sq .snd .fst
  π₂-pres o .homParts _ _ _ = Eq.refl

  module F₁ = FibNotation Fib
  module F₂ = FibNotation Fib'
  module G  = RulesF glue

  open Along π₁ using () renaming
    (pull to pull₁; pullTerm to pullTerm₁; push⊗ to push⊗₁; pull⊗ to pull⊗₁;
     ReflectsSplitAt to Reflects₁) public
  open Along π₂ using () renaming
    (pull to pull₂; pullTerm to pullTerm₂; push⊗ to push⊗₂; pull⊗ to pull⊗₂;
     ReflectsSplitAt to Reflects₂) public

  -- THE COMBINATION.  `A ⊛ B` holds a derivation of `A` over the left
  -- instance and one of `B` over the right, AT RELATED ELEMENTS -- the
  -- relation is what the shared index enforces.

  infixr 6 _⊛_

  _⊛_ : {s : S} → F₁.TheoryTy ℓA s → F₂.TheoryTy ℓB s
      → G.TheoryTy (ℓ-max ℓA ℓB) s
  A ⊛ B = pull₁ A G.& pull₂ B

  module _ {s : S} (A : F₁.TheoryTy ℓA s) (A' : F₁.TheoryTy ℓA' s)
                   (B : F₂.TheoryTy ℓB s) (B' : F₂.TheoryTy ℓB' s) where

    ⊛-map : A F₁.⊢ A' → B F₂.⊢ B' → (A ⊛ B) G.⊢ (A' ⊛ B')
    ⊛-map f g =
      G.&-I (pullTerm₁ f G.∘g G.&-E₁ {A = pull₁ A} {B = pull₂ B})
            (pullTerm₂ g G.∘g G.&-E₂ {A = pull₁ A} {B = pull₂ B})

  -- ⊛ IS LAX MONOIDAL, UNCONDITIONALLY.  A glued splitting already IS a
  -- pair of splittings, so `zip` is `push⊗` at each projection -- no
  -- hypothesis, and no transport, because `homParts` was `Eq.refl`.

  module _ (o : σ .ops)
           (A : (a : σ .arities o) → F₁.TheoryTy ℓA (σ .sortOf o a))
           (B : (a : σ .arities o) → F₂.TheoryTy ℓB (σ .sortOf o a)) where

    zip : G.⊗ˢ o (λ a → A a ⊛ B a) G.⊢ ((F₁.⊗ˢ o A) ⊛ (F₂.⊗ˢ o B))
    zip =
      G.&-I (push⊗₁ o (π₁-pres o) {B = A}
               G.∘g G.⊗ˢ-map o {A = λ a → A a ⊛ B a} {B = λ a → pull₁ (A a)}
                       (λ a → G.&-E₁ {A = pull₁ (A a)} {B = pull₂ (B a)}))
            (push⊗₂ o (π₂-pres o) {B = B}
               G.∘g G.⊗ˢ-map o {A = λ a → A a ⊛ B a} {B = λ a → pull₂ (B a)}
                       (λ a → G.&-E₂ {A = pull₁ (A a)} {B = pull₂ (B a)}))

  -- ... AND STRONG exactly when the relation is SPLIT-AGNOSTIC: any two
  -- splittings of related wholes have related parts.

  Coherent : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓX (ℓ-max ℓX'
                  (ℓ-max ℓP (ℓ-max ℓP' ℓR))))))
  Coherent = (o : σ .ops) (g : glue .carrier (σ .resultSort o))
             (sp  : Fib  .Split o (g .fst))
             (sp' : Fib' .Split o (g .snd .fst))
             (a : σ .arities o)
           → R (σ .sortOf o a) (Fib  .parts o (g .fst)      sp  a)
                               (Fib' .parts o (g .snd .fst) sp' a)

  module _ (c : Coherent) (o : σ .ops)
           (A : (a : σ .arities o) → F₁.TheoryTy ℓA (σ .sortOf o a))
           (B : (a : σ .arities o) → F₂.TheoryTy ℓB (σ .sortOf o a)) where

    -- PHASE 1: builds a splitting, so it is pointful by necessity.
    unzip : ((F₁.⊗ˢ o A) ⊛ (F₂.⊗ˢ o B)) G.⊢ G.⊗ˢ o (λ a → A a ⊛ B a)
    unzip m x =
        (x .fst .fst , x .snd .fst , λ a → c o m (x .fst .fst) (x .snd .fst) a)
      , λ a → x .fst .snd a , x .snd .snd a

    -- One composite is definitional; Σ- and Π-η do all the work.
    zip∘unzip : (zip o A B G.∘g unzip) ≡ G.idg
    zip∘unzip = refl

    -- The other is not, and cannot be: `unzip` REPLACES the relatedness
    -- datum a glued splitting carried with the one `Coherent` supplies.
    unzip∘zip : ((s : S) (m : Fib .carrier s) (m' : Fib' .carrier s)
                 → isProp (R s m m'))
              → (unzip G.∘g zip o A B) ≡ G.idg
    unzip∘zip prop i m x =
        ( x .fst .fst
        , x .fst .snd .fst
        , funExt (λ a → prop _ _ _
                    (c o m (x .fst .fst) (x .fst .snd .fst) a)
                    (x .fst .snd .snd a)) i )
      , x .snd

  -- THE OTHER STRENGTH CONDITION, and the useful one.

  Determined : Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓX (ℓ-max ℓX'
                    (ℓ-max ℓP (ℓ-max ℓP' ℓR))))))
  -- i.e. every base splitting has a DISPLAYED LIFT.  `glue` is then a
  -- fibration over `Fib`, in the sense `Fibered` cares about.
  Determined = (o : σ .ops) (g : glue .carrier (σ .resultSort o))
               (sp : Fib .Split o (g .fst))
             → Splitᴰ o (g .fst) (g .snd .fst) sp

  determined→reflects : Determined → (o : σ .ops) → Reflects₁ o
  determined→reflects d o g sp = (sp , d o g sp) , λ _ → Eq.refl

  -- `Coherent` is the special case where the choice does not depend on
  -- the left splitting at all -- given ANY right splitting to start from.
  coherent→determined : Coherent
                      → ((o : σ .ops) (g : glue .carrier (σ .resultSort o))
                         → Fib' .Split o (g .snd .fst))
                      → Determined
  coherent→determined c pick o g sp = pick o g , λ a → c o g sp (pick o g) a

-- THE THREE DEGENERATE CORRELATIONS.

-- the terminal `Fibered`: one element, one splitting, at every sort
oneFib : {S : Type ℓS} (σ : SortedSig S ℓ ℓ') → Fibered σ ℓ-zero ℓ-zero
oneFib σ .carrier _   = Unit
oneFib σ .Split _ _   = Unit
oneFib σ .parts _ _ _ _ = tt

-- (1) PRODUCT: no correlation at all.  Both `Coherent` and `Determined`
-- hold, so `⊛` is strong monoidal and `zip` is an isomorphism -- the
-- product theory's `⊗` is exactly the pair of the two `⊗`s.
module Product {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
               (Fib : Fibered σ ℓX ℓP) (Fib' : Fibered σ ℓX' ℓP') where

  open Glue Fib Fib' (λ _ _ _ → Unit) public

  coherent : Coherent
  coherent _ _ _ _ _ = tt

  propR : (s : S) (m : Fib .carrier s) (m' : Fib' .carrier s) → isProp Unit
  propR _ _ _ = isPropUnit

-- (2) SUBOBJECT: the right factor is terminal, so the relation is a
-- PREDICATE and the glue is `Σ P` with the splittings all of whose parts
-- satisfy `P`.  A refinement of one theory, for free.
module Sub {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
           (Fib : Fibered σ ℓX ℓP)
           (P : (s : S) → Fib .carrier s → Type ℓR) where

  open Glue Fib (oneFib σ) (λ s m _ → P s m) public

-- (3) COMMA / PULLBACK: two reindexings into a common `Fibered`, glued
-- along agreement of their images.
module Pullback {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
                {Fib₀ : Fibered σ ℓX₀ ℓP₀}
                (Fib : Fibered σ ℓX ℓP) (Fib' : Fibered σ ℓX' ℓP')
                (h : Reindex Fib Fib₀) (k : Reindex Fib' Fib₀) where

  open Glue Fib Fib' (λ s m m' → h .hom s m Eq.≡ k .hom s m') public

  -- PRIMITIVE: transport of a splitting along a strict equality of
  -- wholes, and what it does to the parts.  The two `Eq.refl` matches of
  -- this file, and the only ones the comma case needs.
  private
    coeSplit : (o : σ .ops) {x y : Fib₀ .carrier (σ .resultSort o)}
             → x Eq.≡ y → Fib₀ .Split o x → Fib₀ .Split o y
    coeSplit o Eq.refl sp = sp

    coeParts : (o : σ .ops) {x y : Fib₀ .carrier (σ .resultSort o)}
               (e : x Eq.≡ y) (sp : Fib₀ .Split o x) (a : σ .arities o)
             → Fib₀ .parts o y (coeSplit o e sp) a Eq.≡ Fib₀ .parts o x sp a
    coeParts o Eq.refl sp a = Eq.refl

  -- THE THEOREM. If `h` PRESERVES splittings and `k` REFLECTS them then
  -- the comma object is `Determined`: push the left splitting down to
  -- `Fib₀`, lift it back up the right leg.
  pullbackDetermined : ((o : σ .ops) → SplitPresAt h o)
                     → ((o : σ .ops) → Along.ReflectsSplitAt k o)
                     → Determined
  pullbackDetermined pres refl' o g sp = up .fst , rel
    where
    down : Fib₀ .Split o (h .hom _ (g .fst))
    down = pres o .homSplit (g .fst) sp

    over : Fib₀ .Split o (k .hom _ (g .snd .fst))
    over = coeSplit o (g .snd .snd) down

    up : Σ[ sp' ∈ Fib' .Split o (g .snd .fst) ]
             ((a : σ .arities o)
              → Fib₀ .parts o (k .hom _ (g .snd .fst)) over a
                Eq.≡ k .hom _ (Fib' .parts o (g .snd .fst) sp' a))
    up = refl' o (g .snd .fst) over

    rel : (a : σ .arities o)
        → h .hom _ (Fib  .parts o (g .fst)      sp           a)
          Eq.≡ k .hom _ (Fib' .parts o (g .snd .fst) (up .fst) a)
    rel a =
      Eq.sym (pres o .homParts (g .fst) sp a)
        Eq.∙ (Eq.sym (coeParts o (g .snd .snd) down a) Eq.∙ up .snd a)

-- WHAT IS *NOT* THE POINT: the pullback of two types over ONE instance.

module Fibre {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (Fib : Fibered σ ℓX ℓP) where

  open FibNotation Fib

  fibre : {s : S} (A : TheoryTy ℓA s) (B : TheoryTy ℓB s) (C : TheoryTy ℓC s)
        → A ⊢ C → B ⊢ C → TheoryTy (ℓ-max ℓA (ℓ-max ℓB ℓC)) s
  fibre A B C f g m = Σ[ x ∈ A m ] Σ[ y ∈ B m ] (f m x Eq.≡ g m y)

  module _ {s : S} (A : TheoryTy ℓA s) (B : TheoryTy ℓB s) (C : TheoryTy ℓC s)
           (f : A ⊢ C) (g : B ⊢ C) where

    fibre-π₁ : fibre A B C f g ⊢ A
    fibre-π₁ _ x = x .fst

    fibre-π₂ : fibre A B C f g ⊢ B
    fibre-π₂ _ x = x .snd .fst

    fibre-I : {D : TheoryTy ℓA' s} (p : D ⊢ A) (q : D ⊢ B)
            → ((m : Fib .carrier s) (d : D m) → f m (p m d) Eq.≡ g m (q m d))
            → D ⊢ fibre A B C f g
    fibre-I p q e m d = p m d , q m d , e m d
