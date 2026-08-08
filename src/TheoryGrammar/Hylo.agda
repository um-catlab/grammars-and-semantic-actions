{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Recursion over a guarded description: the strength, the container
   hylomorphism, and the fused connective-form `hyloC`. -}
module TheoryGrammar.Hylo where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Unit
open import Cubical.Induction.WellFounded

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
open import TheoryGrammar.Later
open import TheoryGrammar.Grading

private variable ℓS ℓ ℓ' ℓX ℓP ℓA ℓM ℓN ℓV : Level

module HyloM {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
             (GS : GradedFib σ ℓX ℓP) (ℓA : Level)
             (X : Type ℓV) (xs : X → S) where

  open Grade GS ℓA X xs public
  open FibNotation (GS .fib)

  -- THE STRENGTH.  This is ccl's `▷HomActionFam`, derived rather than
  -- assumed: a guarded description can transport a LATER function
  -- across its positions, because every position is strictly smaller.

  mapGuarded : {s : S} (F : Functor s) → Guarded F
             → {A : Ix → Type ℓM} {B : Ix → Type ℓN}
               (m : GS .fib .carrier s)
             → ((j : Ix) → degIx j < GS .deg s m → A j → B j)
             → ⟦ F ⟧ A m → ⟦ F ⟧ B m
  mapGuarded F gF m r (sh , f) = sh , λ p → r _ (gF m sh p) (f p)

  -- HYLOMORPHISM.  coalgebra + algebra + guardedness, by löb.

  module _ {F : (x : X) → Functor (xs x)} (gF : (x : X) → Guarded (F x))
           {A : Ix → Type ℓM} {B : Ix → Type ℓN}
           (c : Coalg F A) (alg : Alg F B) where

    hylo : (i : Ix) → A i → B i
    hylo = löb step
      where
        step : (i : Ix) → ▷ (λ j → A j → B j) i → A i → B i
        step (x , m) rec ai =
          alg x m (mapGuarded (F x) (gF x) m (λ j q → rec j q) (c x m ai))

  -- Per-slot guardedness certificates. `<⊗e` above requires EVERY
  -- recursive slot to be a proper part.

  private
    <≤-tr : {x y z : ℕ} → x < y → y ≤ z → x < z
    <≤-tr p q = ≤-trans p q

    ≤<-tr : {x y z : ℕ} → x ≤ y → y < z → x < z
    ≤<-tr p q = ≤-trans (suc-≤-suc p) q

  ⊗-guard : (o : σ .ops) (G : (a : σ .arities o) → Functor (σ .sortOf o a))
          → ((m : GS .fib .carrier (σ .resultSort o)) (sp : GS .fib .Split o m)
             (sh : (a : σ .arities o) → Sh (G a) (GS .fib .parts o m sp a))
             (a : σ .arities o) (p : Pos (G a) _ (sh a))
             → degIx (nx (G a) _ (sh a) p) < GS .deg _ m)
          → Guarded (⊗e o G)
  ⊗-guard o G h m (sp , sh) (a , p) = h m sp sh a p

  -- Way 1: the slot's own description already strictly decreases.
  slotGuarded : (o : σ .ops) (m : GS .fib .carrier (σ .resultSort o))
                (sp : GS .fib .Split o m) (a : σ .arities o)
                {G : Functor (σ .sortOf o a)} → Guarded G
              → (sh : Sh G (GS .fib .parts o m sp a)) (p : Pos G _ sh)
              → degIx (nx G _ sh p) < GS .deg _ m
  slotGuarded o m sp a g sh p = <≤-tr (g _ sh p) (GS .deg≤ o m sp a)

  -- Way 2: the slot does not grow, and IS a proper part.
  slotProper : (o : σ .ops) (m : GS .fib .carrier (σ .resultSort o))
               (sp : GS .fib .Split o m) (a : σ .arities o)
               {G : Functor (σ .sortOf o a)} → Guarded≤ G → Proper GS o m sp a
             → (sh : Sh G (GS .fib .parts o m sp a)) (p : Pos G _ sh)
             → degIx (nx G _ sh p) < GS .deg _ m
  slotProper o m sp a g pr sh p = ≤<-tr (g _ sh p) (GS .deg< o m sp a pr)

  -- strict versions of the additive formers
  <⌜⌝ : {s : S} (A : FibNotation.TheoryTy (GS .fib) ℓA⁺ s) → Guarded ⌜ A ⌝
  <⌜⌝ A m sh ()

  <⊕e : {s : S} (Y : Type ℓA⁺) (G : Y → Functor s)
      → ((y : Y) → Guarded (G y)) → Guarded (⊕e Y G)
  <⊕e Y G g m (y , sh) p = g y m sh p

  <&e : {s : S} (Y : Type ℓA⁺) (G : Y → Functor s)
      → ((y : Y) → Guarded (G y)) → Guarded (&e Y G)
  <&e Y G g m sh (y , p) = g y m (sh y) p

  -- THE INTERNAL HYLOMORPHISM, fused. `mapC` transports a later-function
  -- across a CONNECTIVE-form element directly, by recursion on the
  -- description.

  GuardedAt : {s : S} (F : Functor s) (m : GS .fib .carrier s)
            → Sh F m → ℕ → Type ℓPos
  GuardedAt F m sh n = (p : Pos F m sh) → degIx (nx F m sh p) < n

  mapC : {A B : Ix → Type ℓSh} {s : S} (F : Functor s)
         (m : GS .fib .carrier s) (n : ℕ) (t : ⟦ F ⟧c A m)
       → GuardedAt F m (shapeOf F m t) n
       → ((j : Ix) → degIx j < n → A j → B j)
       → ⟦ F ⟧c B m
  mapC ⌜ B ⌝    m n b       g r = b
  mapC (Var x)  m n a       g r = r (x , m) (g tt*) a
  mapC (⊕e Y G) m n (y , t) g r = y , mapC (G y) m n t g r
  mapC (&e Y G) m n h       g r = λ y → mapC (G y) m n (h y) (λ p → g (y , p)) r
  mapC (⊗e o G) m n (sp , h) g r =
    sp , λ a → mapC (G a) _ n (h a) (λ p → g (a , p)) r

  -- the hom of Ix-families
  _⊢ᴵ_ : (A B : Ix → Type ℓSh) → Type (ℓ-max (ℓ-max ℓV ℓX) ℓSh)
  A ⊢ᴵ B = (i : Ix) → A i → B i

  module _ {F : (x : X) → Functor (xs x)} (gF : (x : X) → Guarded (F x))
           {A B : Ix → Type ℓSh}
           (c : CoalgC F A) (alg : AlgC F B) where

    hyloC : A ⊢ᴵ B
    hyloC = löb λ { (x , m) rec ai →
      alg x m (mapC (F x) m (GS .deg (xs x) m) (c x m ai)
                    (λ p → gF x m _ p) (λ j q → rec j q)) }

  -- ... and the same thing as an INTERNAL TERM.  `hyloC` is stated with
  -- `Ix` and an element; `hyloᴳ` is the `⊢` a use site actually wants.
  -- Definitionally the same map -- only the presentation differs.

  hyloᴳ : {F : (x : X) → Functor (xs x)} (gF : (x : X) → Guarded (F x))
          {A B : Fam} → Coalgᴳ F A → Algᴳ F B → (x : X) → A x ⊢ B x
  hyloᴳ gF c α x m a = hyloC gF c α (x , m) a

  -- LOCAL CONTRACTIVITY, asked for directly.

  LocallyContractive : ((x : X) → Functor (xs x)) → Type _
  LocallyContractive F =
    {A B : Ix → Type ℓSh} (x : X) (m : GS .fib .carrier (xs x))
    → ▷ (λ j → A j → B j) (x , m)
    → ⟦ F x ⟧c A m → ⟦ F x ⟧c B m

  guarded→LC : {F : (x : X) → Functor (xs x)}
             → ((x : X) → Guarded (F x)) → LocallyContractive F
  guarded→LC {F = F} gF x m rec t =
    mapC (F x) m (GS .deg (xs x) m) t (λ p → gF x m _ p) (λ j q → rec j q)

  -- THE HYLOMORPHISM FROM LOCAL CONTRACTIVITY ALONE.  löb supplies the
  -- recursive call as a `▷`, the strength pushes it under the functor,
  -- and the algebra closes it up.  Nothing else happens.
  module _ {F : (x : X) → Functor (xs x)} (lc : LocallyContractive F)
           {A B : Fam} (c : Coalgᴳ F A) (α : Algᴳ F B) where

    hyloStep : (i : Ix) → ▷ (λ j → ⌞ A ⌟ j → ⌞ B ⌟ j) i → (⌞ A ⌟ i → ⌞ B ⌟ i)
    hyloStep (x , m) rec a = α x m (lc x m rec (c x m a))

    hyloLC : (x : X) → A x ⊢ B x
    hyloLC x m = löb hyloStep (x , m)

    -- THE UNIVERSAL PROPERTY, for every theory.

    hyloLC-unfold : (i : Ix) → löb hyloStep i ≡ hyloStep i (λ j _ → löb hyloStep j)
    hyloLC-unfold = löb-unfold hyloStep

    hyloLC-unique : (h : (i : Ix) → ⌞ A ⌟ i → ⌞ B ⌟ i)
                  → ((i : Ix) → h i ≡ hyloStep i (λ j _ → h j))
                  → (i : Ix) → h i ≡ löb hyloStep i
    hyloLC-unique = löb-unique hyloStep

  -- INITIAL/FINAL COINCIDENCE -- the guarded fixed-point theorem.

  μ→ν : {F : (x : X) → Functor (xs x)} → (i : Ix) → μ F i → ν F i
  μ→ν {F = F} = fold (ν F) λ x m sh f → νinto (x , m) (sh , f)

  module _ {F : (x : X) → Functor (xs x)} (gF : (x : X) → Guarded (F x)) where

    ν→μStep : (i : Ix) → ▷ (λ j → ν F j → μ F j) i → (ν F i → μ F i)
    ν→μStep (x , m) rec t =
      sup (t .shOf) (λ p → rec _ (gF x m (t .shOf) p) (t .nxOf p))

    ν→μ : (i : Ix) → ν F i → μ F i
    ν→μ = löb ν→μStep

    -- ONE ROUND TRIP IS PROVABLE, and it is the μ one: recursion on the
    -- finite tree, with `löb-unfold` supplying the single step.
    ν→μ-μ→ν : (i : Ix) (t : μ F i) → ν→μ i (μ→ν i t) ≡ t
    ν→μ-μ→ν (x , m) (sup sh f) =
      funExt⁻ (löb-unfold ν→μStep (x , m)) (μ→ν (x , m) (sup sh f))
      ∙ cong (sup sh) (funExt λ p → ν→μ-μ→ν _ (f p))

    -- ... AND SO IS THE OTHER, without a pragma.
    μ→ν-ν→μ : (i : Ix) (u : ν F i) → μ→ν i (ν→μ i u) ≡ u
    μ→ν-ν→μ = löb λ { (x , m) rec u →
        cong (μ→ν (x , m)) (funExt⁻ (löb-unfold ν→μStep (x , m)) u)
      ∙ cong (λ g → νinto (x , m) (u .shOf , g))
             (funExt λ p → rec _ (gF x m (u .shOf) p) (u .nxOf p))
      ∙ νinto-νout (x , m) u }

    -- THE SAME TRICK KILLS `coind`. Uniqueness of the corecursor was the
    -- other thing upstream needed `{-# TERMINATING #-}` for, and it is
    -- blocked for an ARBITRARY functor.
    ν-η : {ℓM : Level} (M : Ix → Type ℓM)
          (γ : (x : X) (m : GS .fib .carrier (xs x)) → M (x , m)
             → Σ[ sh ∈ Sh (F x) m ] ((p : Pos (F x) m sh) → M (nx (F x) m sh p)))
          (ϕ : (i : Ix) → M i → ν F i)
        → ((i : Ix) (a : M i)
           → νout i (ϕ i a)
           ≡ (γ (i .fst) (i .snd) a .fst
             , λ p → ϕ _ (γ (i .fst) (i .snd) a .snd p)))
        → (i : Ix) (a : M i) → ϕ i a ≡ νunfold M γ i a
    ν-η M γ ϕ hom = löb λ { (x , m) rec a →
        sym (νinto-νout (x , m) (ϕ (x , m) a))
      ∙ cong (νinto (x , m)) (hom (x , m) a)
      ∙ cong (λ g → νinto (x , m) (γ x m a .fst , g))
             (funExt λ p → rec _ (gF x m (γ x m a .fst) p) (γ x m a .snd p))
      ∙ νinto-νout (x , m) (νunfold M γ (x , m) a) }

    -- Hence the coincidence is a genuine ISOMORPHISM, for every theory.
    μ≅ν : (i : Ix) → Iso (μ F i) (ν F i)
    μ≅ν i .Iso.fun = μ→ν i
    μ≅ν i .Iso.inv = ν→μ i
    μ≅ν i .Iso.sec = μ→ν-ν→μ i
    μ≅ν i .Iso.ret = ν→μ-μ→ν i

    -- HOW TO USE THE COINCIDENCE, in any theory.

    ana : {ℓM : Level} (M : Ix → Type ℓM)
          (γ : (x : X) (m : GS .fib .carrier (xs x)) → M (x , m)
             → Σ[ sh ∈ Sh (F x) m ] ((p : Pos (F x) m sh) → M (nx (F x) m sh p)))
        → (i : Ix) → M i → μ F i
    ana M γ i a = ν→μ i (νunfold M γ i a)

  -- THE GENERIC ▷-APP. A `later` may be consumed at any position of a
  -- GUARDED description, because guardedness is precisely the strictness
  -- the `later` demands.

  ▷pos : {A : Ix → Type ℓM} {s : S} (F : Functor s) → Guarded F
       → (m : GS .fib .carrier s) (sh : Sh F m) (p : Pos F m sh)
       → ((j : Ix) → degIx j < GS .deg s m → A j) → A (nx F m sh p)
  ▷pos F g m sh p r = r (nx F m sh p) (g m sh p)

