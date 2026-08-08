{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Automata, theory-generically.  See the note inside: an automaton is
   an algebra, ⊤ carries a coalgebra, and running one is the hylo. -}
module TheoryGrammar.Automaton where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
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
open import TheoryGrammar.Hylo

private variable ℓS ℓ ℓ' ℓX ℓP ℓA ℓM ℓN ℓV : Level

-- `Guard` keeps its name and its parameters: it is what every instance
-- opens, and the split above is invisible to them.
module Guard {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
             (GS : GradedFib σ ℓX ℓP) (ℓA : Level)
             (X : Type ℓV) (xs : X → S) where

  open HyloM GS ℓA X xs public
  open FibNotation (GS .fib)

  -- AUTOMATA ARE ALGEBRAS, and running one is a hylomorphism.

  -- PROGRAMS OUT OF ⊤. There is no "automaton" structure to define.

  -- ⊤'s coalgebra for a description -- the theory's decomposition axiom.
  Scanner : ((x : X) → Functor (xs x)) → Type _
  Scanner F = Coalgᴳ F (λ _ → ⊤ᴳ)

  runAut : {F : (x : X) → Functor (xs x)} {A : Fam}
         → LocallyContractive F → Scanner F → Algᴳ F A
         → (x : X) → ⊤G ⊢ A x
  runAut lc sc α x = hyloLC lc sc α x ∘⊢ ⊤ᴳ-I

  -- ⊤ ≅ μ(shape), the generic replacement for `⊤ ≅ String`.

  scanμ : {F : (x : X) → Functor (xs x)} → ((x : X) → Guarded (F x))
        → Scanner F → (x : X) → ⊤G ⊢ μᴳ F x
  scanμ {F = F} gF sc x m _ = go (x , m)
    where
      go : (i : Ix) → μ F i
      go = löb λ { (x' , m') rec →
             sup (shapeOf (F x') m' (sc x' m' tt*))
                 (λ p → rec _ (gF x' m' _ p)) }

  Free : ((x : X) → Functor (xs x)) → Type _
  Free F = (i : Ix) → isContr (μ F i)

  -- given freeness, the parse is unique ...
  free→isProp : {F : (x : X) → Functor (xs x)} → Free F
              → (i : Ix) (s t : μ F i) → s ≡ t
  free→isProp fr i = isContr→isProp (fr i)

  -- ... and in particular INDEPENDENT OF THE SCANNER, which is the
  -- caveat discharged.
  scanμ-scanner-irrelevant :
      {F : (x : X) → Functor (xs x)} → Free F
    → (gF : (x : X) → Guarded (F x)) (sc sc' : Scanner F)
    → (x : X) (m : GS .fib .carrier (xs x)) (u : ⊤G m)
    → scanμ gF sc x m u ≡ scanμ gF sc' x m u
  scanμ-scanner-irrelevant fr gF sc sc' x m u = free→isProp fr (x , m) _ _

  -- A USABLE CRITERION FOR FREENESS. `Free` as stated is a property of `μ
  -- F`, which nothing can discharge directly.

  shapeContr→Free : {F : (x : X) → Functor (xs x)}
                  → ((x : X) (m : GS .fib .carrier (xs x)) → isContr (Sh (F x) m))
                  → ((x : X) → Guarded (F x))
                  → Free F
  shapeContr→Free {F = F} shc gF = löb λ { (x , m) rec →
    isContrRetract unroll roll roll-unroll
      (isContrΣ (shc x m) (λ sh → isContrΠ λ p → rec _ (gF x m sh p))) }

  -- VIEWS, FREENESS, AND EQUIDIVISIBILITY -- one story.
