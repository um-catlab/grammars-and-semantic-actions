{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- GENERATION, generic in the theory and in the description. -}
module TheoryGrammar.Generate where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; _·_)
open import Cubical.Data.Maybe using (Maybe; just; nothing; map-Maybe)
open import Cubical.Data.List
open import Cubical.Data.Empty as E using (⊥*)
open import Agda.Builtin.Nat using (mod-helper; div-helper)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
open import TheoryGrammar.Enumerable
open import TheoryGrammar.Enumerable.Listed

private variable ℓS ℓ ℓ' ℓX ℓP ℓA ℓB ℓI ℓV : Level

-- 0.  LIST PLUMBING.  Two functions, both level-heterogeneous, which is
-- why `Enumerable.cmap` (same level on both sides) cannot serve.

bindL : {A : Type ℓA} {B : Type ℓB} → List A → (A → List B) → List B
bindL []       f = []
bindL (a ∷ as) f = f a ++ bindL as f

-- THE Π OVER A LISTED INDEX, AS A SEARCH SPACE. `AllYes'` is
-- `Enumerable`'s nested product; this is its cartesian product, and
-- `lookupYes'` turns the tuple back into the dependent function.
allYes : {I : Type ℓI} {B : I → Type ℓB}
       → ((i : I) → List (B i)) → (is : List I) → List (AllYes' B is)
allYes g []       = tt* ∷ []
allYes g (i ∷ is) = bindL (g i) λ b → map (λ r → b , r) (allYes g is)

seqΠ : {I : Type ℓI} {B : I → Type ℓB}
     → Listed I → ((i : I) → List (B i)) → List ((i : I) → B i)
seqΠ L g = map (λ all i → lookupYes' (L .elts) i (L .complete i) all)
               (allYes g (L .elts))

-- 1. PSEUDORANDOMNESS.

Seed : Type₀
Seed = ℕ

_%_ : ℕ → ℕ → ℕ
n % zero    = n
n % (suc m) = mod-helper 0 m n m

_/_ : ℕ → ℕ → ℕ
n / zero    = zero
n / (suc m) = div-helper 0 m n m

-- glibc's constants, modulus 2³¹
next : Seed → Seed
next s = (1103515245 · s + 12345) % 2147483648

nth : {A : Type ℓA} → List A → ℕ → Maybe A
nth []       _       = nothing
nth (a ∷ _)  zero    = just a
nth (_ ∷ as) (suc k) = nth as k

-- A KNUTH MULTIPLICATIVE HASH, then the high half.
mix : Seed → ℕ
mix s = ((2654435761 · s) % 4294967296) / 65536

-- ONE DRAW from a search space.  `[]` gives `nothing`: a generator that
-- offers nothing does not get to pretend otherwise.
sample : {A : Type ℓA} → List A → Seed → Maybe A
sample xs s = nth xs (mix s % length xs)

-- THE STREAM: `n` draws, one seed apart.
stream : {A : Type ℓA} → ℕ → List A → Seed → List (Maybe A)
stream zero    xs s = []
stream (suc n) xs s = sample xs s ∷ stream n xs (next s)

-- the seeds themselves, for threading into a sampling generator
seeds : ℕ → Seed → List Seed
seeds zero    s = []
seeds (suc n) s = s ∷ seeds n (next s)

-- Maybe plumbing, level-heterogeneous
bindM : {A : Type ℓA} {B : Type ℓB} → Maybe A → (A → Maybe B) → Maybe B
bindM nothing  f = nothing
bindM (just a) f = f a

mapM : {A : Type ℓA} {B : Type ℓB} → (A → B) → Maybe A → Maybe B
mapM f = map-Maybe f

-- the successes of a stream, for reading a fuzz run
catMaybes : {A : Type ℓA} → List (Maybe A) → List A
catMaybes []              = []
catMaybes (nothing ∷ xs)  = catMaybes xs
catMaybes (just a  ∷ xs)  = a ∷ catMaybes xs

-- THE SEEDED Π. `allYes`'s counterpart when only ONE tuple is wanted: fill
-- every slot with a single draw, advancing the seed between slots.
allYesS : {I : Type ℓI} {B : I → Type ℓB}
        → ((i : I) → Seed → Maybe (B i)) → (is : List I)
        → Seed → Maybe (AllYes' B is)
allYesS g []       s = just tt*
allYesS g (i ∷ is) s =
  bindM (g i s) λ b → mapM (λ r → b , r) (allYesS g is (next s))

seqΠS : {I : Type ℓI} {B : I → Type ℓB}
      → Listed I → ((i : I) → Seed → Maybe (B i)) → Seed → Maybe ((i : I) → B i)
seqΠS L g s = mapM (λ all i → lookupYes' (L .elts) i (L .complete i) all)
                   (allYesS g (L .elts) s)

-- 2. `⋁`, THE SEARCH-SPACE CONNECTIVE, and `Seek`.

module GenNotation {S : Type ℓS} (Car : S → Type ℓX) where

  open CarrierNotation Car public

  ⋁ : {s : S} → TheoryTy ℓA s → TheoryTy ℓA s
  ⋁ A m = List (A m)

  -- the monad structure, internally
  ⋁-η : {s : S} {A : TheoryTy ℓA s} → A ⊢ ⋁ A
  ⋁-η m a = a ∷ []

  ⋁-map : {s : S} {A : TheoryTy ℓA s} {B : TheoryTy ℓB s} → A ⊢ B → ⋁ A ⊢ ⋁ B
  ⋁-map f m = map (f m)

  ⋁-μ : {s : S} {A : TheoryTy ℓA s} → ⋁ (⋁ A) ⊢ ⋁ A
  ⋁-μ m xs = bindL xs (λ x → x)

  -- ... and its finite joins.  `⋁-∪` is why weighting is multiplicity.
  ⋁-⊥ : {s : S} {A : TheoryTy ℓA s} → ⊤G ⊢ ⋁ A
  ⋁-⊥ m _ = []

  ⋁-∪ : {s : S} {A : TheoryTy ℓA s} → (⋁ A & ⋁ A) ⊢ ⋁ A
  ⋁-∪ m (xs , ys) = xs ++ ys

  -- A GENERATOR AT A GRAMMAR.  Dual to `View.Probe P = ⊤G ⊢ Dec⟨ P ⟩`.
  Seek : {s : S} → TheoryTy ℓA s → Type (ℓ-max ℓX ℓA)
  Seek A = ⊤G ⊢ ⋁ A

  -- ... and a generator at a plain type, for the index sets that are
  -- not indexed by a world (`⊕e`'s tag).  `Listed` minus `complete`.
  Gen : Type ℓA → Type ℓA
  Gen A = List A

-- 2b. A STRICT TOTAL POINT.

record StrictPoint {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (Fib : Fibered σ ℓX ℓP)
  : Type (ℓ-max ℓS (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓX ℓP)))) where
  field
    opU    : (o : σ .ops)
           → ((a : σ .arities o) → Fib .carrier (σ .sortOf o a))
           → Fib .carrier (σ .resultSort o)
    splitU : (o : σ .ops)
             (m⃗ : (a : σ .arities o) → Fib .carrier (σ .sortOf o a))
           → Fib .Split o (opU o m⃗)
    partsU : (o : σ .ops)
             (m⃗ : (a : σ .arities o) → Fib .carrier (σ .sortOf o a))
             (a : σ .arities o)
           → Fib .parts o (opU o m⃗) (splitU o m⃗) a Eq.≡ m⃗ a

open StrictPoint public

-- 3. THE CORE.

module GenInd {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
              (Fib : Fibered σ ℓX ℓP) (ℓA : Level)
              (X : Type ℓV) (xs : X → S)
              -- THE THEORY'S OBLIGATION.  Read it as `Seek (Fib .Split o)`
              -- -- see `oblig-is-Seek` below, which is `refl`.
              (seekSplit : (o : σ .ops) (m : Fib .carrier (σ .resultSort o))
                         → Unit → List (Fib .Split o m))
              -- ... and the one place completeness survives.
              (enumAr : (o : σ .ops) → Listed (σ .arities o))
              where

  open Ind Fib ℓA X xs public
  open GenNotation (Fib .carrier) public

  private
    Car : (s : S) → Type ℓX
    Car = Fib .carrier

  -- the obligation, stated internally
  oblig-is-Seek : ((o : σ .ops) → Seek (Fib .Split o))
                ≡ ((o : σ .ops) (m : Car (σ .resultSort o))
                   → Unit → List (Fib .Split o m))
  oblig-is-Seek = refl

  -- WHAT A GRAMMAR OWES.  Compare `DecInd.DecDesc`: `Probe` becomes
  -- `Seek`, and `Listed Y` becomes `Gen Y` at `⊕e` ONLY.

  GenDesc : {s : S} → Functor s → Type (ℓ-max ℓX (ℓ-max ℓA ℓ'))
  GenDesc (⌜ B ⌝)  = Lift ℓ' (Seek B)
  GenDesc (Var x)  = Unit*
  GenDesc (⊕e Y G) = Gen Y × ((y : Y) → GenDesc (G y))     -- Σ: no completeness
  GenDesc (&e Y G) = Listed Y × ((y : Y) → GenDesc (G y))  -- Π: completeness
  GenDesc (⊗e o G) = (a : σ .arities o) → GenDesc (G a)

  -- The bottom-up counterpart, which mentions no fixed point and so sits
  -- outside the module below.  Its constant clause is the whole
  -- difference: a world BESIDE each witness.
  UpDesc : {s : S} → Functor s → Type (ℓ-max ℓX (ℓ-max ℓA ℓ'))
  UpDesc {s} (⌜ B ⌝) = Lift ℓ' (List (Σ[ m ∈ Car s ] B m))
  UpDesc (Var x)     = Unit*
  UpDesc (⊕e Y G)    = Gen Y × ((y : Y) → UpDesc (G y))
  -- NOT SUPPORTED: the branches of an additive conjunction must agree on
  -- the world, and bottom-up has each of them inventing its own.
  -- `Unit*` records that no data would help; see the header.
  UpDesc (&e Y G)    = Unit*
  UpDesc (⊗e o G)    = (a : σ .arities o) → UpDesc (G a)

  -- `F` is EXPLICIT. It occurs in the arguments below only under `GenDesc
  -- (F x)` / `UpDesc (F x)`, and those are functions defined by matching
  -- on the description, so `GenDesc (F x) = Σ (Gen Y) _` does not
  -- determine `F x`.
  module _ (F : (x : X) → Functor (xs x)) where

    -- ONE LAYER: a shape together with a subterm at every position.
    Layer : {s : S} (G : Functor s) → Car s → Type ℓμ
    Layer G m = Σ[ sh ∈ Sh G m ] ((p : Pos G m sh) → μ F (nx G m sh p))

    -- PRIMITIVE (phase 1): a constant clause has no positions.  Stated
    -- once so no clause below has to eliminate `⊥*` inline.
    noPos : {s : S} {B : TheoryTy ℓA s} {m : Car s} {sh : Sh (⌜ B ⌝) m}
          → (p : Pos {s} (⌜ B ⌝) m sh) → μ F (nx (⌜ B ⌝) m sh p)
    noPos ()

    -- 3a.  EXHAUSTIVE TOP-DOWN GENERATION.  Every layer at `m`, then
    -- every subterm at every part.  `SmallCheck`, not `QuickCheck`.

    genLayer : ((ix : Ix) → List (μ F ix))
             → {s : S} (G : Functor s) → GenDesc G → (m : Car s) → List (Layer G m)

    genLayer rec (⌜ B ⌝) dB m =
      map (λ b → lift b , noPos) (lower dB m tt)

    genLayer rec (Var x) _ m =
      map (λ t → tt* , λ _ → t) (rec (x , m))

    -- `Sh (⊕e Y G) m` IS `Σ y, Sh (G y) m` and `Pos`/`nx` at `(y , sh)`
    -- ARE those at `sh`, so the retag is the identity on the second
    -- component -- no reshuffle, exactly as in `decSh`.
    genLayer rec (⊕e Y G) (gY , dG) m =
      bindL gY λ y →
        map (λ l → (y , l .fst) , l .snd) (genLayer rec (G y) (dG y) m)

    genLayer rec (&e Y G) (lY , dG) m =
      map (λ l → (λ y → l y .fst) , λ p → l (p .fst) .snd (p .snd))
          (seqΠ lY λ y → genLayer rec (G y) (dG y) m)

    -- THE ONLY CLAUSE THAT CONSUMES THE THEORY.  Choose a splitting
    -- (`bindL`, no completeness), then fill every slot (`seqΠ`,
    -- completeness).
    genLayer rec (⊗e o G) dG m =
      bindL (seekSplit o m tt) λ sp →
        map (λ l → (sp , λ a → l a .fst) , λ p → l (p .fst) .snd (p .snd))
            (seqΠ (enumAr o) λ a → genLayer rec (G a) (dG a) (Fib .parts o m sp a))

    genμ : ((x : X) → GenDesc (F x)) → ℕ → (ix : Ix) → List (μ F ix)
    genμ gd zero    ix      = []
    genμ gd (suc n) (x , m) =
      map (λ l → sup (l .fst) (l .snd)) (genLayer (genμ gd n) (F x) (gd x) m)

    -- 3b. BOTTOM-UP SAMPLING -- THE FUZZER.

    -- PRIMITIVE (phase 1): move a layer along a STRICT equation of worlds.
    coeLayer : {s : S} (G : Functor s) {m m' : Car s}
             → m Eq.≡ m' → Layer G m' → Layer G m
    coeLayer G Eq.refl l = l

    -- a draw: a world together with a term at it
    Draw : (x : X) → Type (ℓ-max ℓX ℓμ)
    Draw x = Σ[ m ∈ Car (xs x) ] μ F (x , m)

    upLayer : StrictPoint Fib → ((x : X) → Seed → Maybe (Draw x))
            → {s : S} (G : Functor s) → UpDesc G
            → Seed → Maybe (Σ[ m ∈ Car s ] Layer G m)

    upLayer P rec (⌜ B ⌝) dB sd =
      mapM (λ mb → mb .fst , lift (mb .snd) , noPos) (sample (lower dB) sd)

    upLayer P rec (Var x) _ sd =
      mapM (λ mt → mt .fst , tt* , λ _ → mt .snd) (rec x sd)

    upLayer P rec (⊕e Y G) (gY , dG) sd =
      bindM (sample gY sd) λ y →
        mapM (λ ml → ml .fst , (y , ml .snd .fst) , ml .snd .snd)
             (upLayer P rec (G y) (dG y) (next sd))

    upLayer P rec (&e Y G) _ sd = nothing

    -- Generate every slot, then COMBINE: the world is `opU` of the slots'
    -- worlds and the splitting is the canonical one, so there is no choice
    -- to make and nothing to reject.
    upLayer P rec (⊗e o G) dG sd =
      mapM mk (seqΠS (enumAr o) (λ a → upLayer P rec (G a) (dG a)) sd)
      where
        mk : ((a : σ .arities o) → Σ[ m ∈ Car (σ .sortOf o a) ] Layer (G a) m)
           → Σ[ m ∈ Car (σ .resultSort o) ] Layer (⊗e o G) m
        mk l = P .opU o (λ a → l a .fst)
             , (P .splitU o (λ a → l a .fst) , λ a → lay a .fst)
             , λ p → lay (p .fst) .snd (p .snd)
          where
            lay : (a : σ .arities o)
                → Layer (G a) (Fib .parts o (P .opU o (λ b → l b .fst))
                                            (P .splitU o (λ b → l b .fst)) a)
            lay a = coeLayer (G a) (P .partsU o (λ b → l b .fst) a) (l a .snd)

    -- THE FUZZER.  `n` is QuickCheck's size.
    upμ : StrictPoint Fib → ((x : X) → UpDesc (F x)) → ℕ
        → (x : X) → Seed → Maybe (Draw x)
    upμ P gd zero    x sd = nothing
    upμ P gd (suc n) x sd =
      mapM (λ ml → ml .fst , sup (ml .snd .fst) (ml .snd .snd))
           (upLayer P (upμ P gd n) (F x) (gd x) sd)

    -- ... and the stream of draws: `k` of them at size `sz`.
    upStream : StrictPoint Fib → ((x : X) → UpDesc (F x)) → ℕ → ℕ
             → (x : X) → Seed → List (Maybe (Draw x))
    upStream P gd sz k x sd = map (upμ P gd sz x) (seeds k sd)

