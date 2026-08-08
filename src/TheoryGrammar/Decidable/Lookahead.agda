{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- LOOKAHEAD, THEORY-GENERICALLY -- and the LL collapse. -}
module TheoryGrammar.Decidable.Lookahead where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
-- NOTE: `inl` / `inr` are deliberately NOT imported.  A decision is
-- eliminated by `dec-elim` and introduced by `dec-yes` / `dec-no`; this
-- module cannot match on a sum even by accident.
open import Cubical.Data.Sum using (_⊎_)
open import Cubical.Data.Unit
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order using (_<_)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded
open import TheoryGrammar.Enumerable
open import TheoryGrammar.Enumerable.Listed
open import TheoryGrammar.Inductive.Dual
open import TheoryGrammar.Inductive.Consistent
open import TheoryGrammar.Decidable.Additive
open import TheoryGrammar.Decidable.Inductive

private variable ℓS ℓ ℓ' ℓX ℓP ℓA ℓV ℓO : Level

module Look {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
            (GS : GradedFib σ ℓX ℓP) (ℓA : Level)
            (X : Type ℓV) (xs : X → S)
            (enumSplit : (o : σ .ops) (m : GS .fib .carrier (σ .resultSort o))
                       → Listed (GS .fib .Split o m))
            (enumAr    : (o : σ .ops) → Listed (σ .arities o))
            where

  open DecInd GS ℓA X xs enumSplit enumAr public

  private
    Car : (s : S) → Type ℓX
    Car = GS .fib .carrier

  -- A GRAMMAR IN ALTERNATIVES FORM. Every nonterminal is a sum of
  -- productions; this is the shape an LL table is indexed by, and it is no
  -- loss -- a description that is not a sum at the top is the one-
  -- alternative case.

  record Alts : Type (ℓ-max (ℓ-suc ℓA) (ℓ-max ℓV (ℓ-max ℓS (ℓ-max ℓ (ℓ-max ℓ' ℓX))))) where
    field
      Alt  : X → Type ℓA
      body : (x : X) → Alt x → Functor (xs x)

  open Alts public

  descOf : (As : Alts) (x : X) → Functor (xs x)
  descOf As x = ⊕e (As .Alt x) (As .body x)

  -- THE LOOKAHEAD AUTOMATON. `St` is the state type -- finite in every
  -- intended instance, but finiteness is NOT needed for the collapse
  -- below, only for DECIDING the separation condition when one builds a
  -- `Lookahead`.

  -- THE LAYER OF A DESCRIPTION, AS A GRAMMAR -- so that everything below
  -- is a `⊢`-term between FIXED grammars rather than a function on
  -- layers.  This is what lets the lookahead be stated internally.

  Layerᴳ : (As : Alts) {s : S} → Functor s → TheoryTy ℓμ s
  Layerᴳ As F m = Layer⁺ F (μ (descOf As)) m

  -- "this world's lookahead state is `st`" -- a grammar, indexed by the
  -- state.  The whole lookahead layer is phrased against this.
  LookAt : {St : Type ℓA} (look : (s : S) → Car s → St) {s : S}
         → St → TheoryTy ℓA s
  LookAt look {s} st m = look s m Eq.≡ st

  record Lookahead (As : Alts)
    : Type (ℓ-suc (ℓ-max ℓA (ℓ-max ℓV (ℓ-max ℓX
              (ℓ-max ℓS (ℓ-max ℓ (ℓ-max ℓ' ℓP))))))) where
    field
      St   : Type ℓA
      look : (s : S) → Car s → St
      sel  : (x : X) → St → As .Alt x
      -- SOUNDNESS, INTERNALLY. At a world whose lookahead state is `st`,
      -- any alternative's layer entails the SELECTED one's.
      sound : (x : X) (a : As .Alt x) (st : St)
            → (Layerᴳ As (As .body x a) & LookAt look st)
              ⊢ Layerᴳ As (As .body x (sel x st))

  open Lookahead public

  -- THE COLLAPSE.  A sum of alternatives IS its selected branch.

  module _ {As : Alts} (L : Lookahead As) where

    private
      chosen : (x : X) (m : Car (xs x)) → Functor (xs x)
      chosen x m = As .body x (L .sel x (L .look (xs x) m))

    -- THE LOOKAHEAD IS A COMPLETE VIEW OF THE WORLD BY ITS STATE, and both
    -- halves are DERIVED rather than assumed: every world has a state
    -- (`Eq.refl`), and no world has two.

    lookTotal : {s : S} → ⊤G {s} ⊢ ⊕ᴰ (L .St) (LookAt (L .look))
    lookTotal m _ = L .look _ m , Eq.refl

    lookUnique : {s : S} (st st' : L .St) (m : Car s)
               → LookAt (L .look) st m → LookAt (L .look) st' m → st ≡ st'
    lookUnique st st' m p q = sym (Eq.eqToPath p) ∙ Eq.eqToPath q

    -- `A` is EXPLICIT: the motive is not recoverable from a layer, since
    -- `Layer⁺ F A m` unfolds to a Σ whose second component is a Π, and a
    -- metavariable cannot be read back out of one.
    toSelᴳ : (x : X) (st : L .St)
           → (Layerᴳ As (descOf As x) & LookAt (L .look) st)
             ⊢ Layerᴳ As (As .body x (L .sel x st))
    toSelᴳ x st m (((a , sh) , f) , lk) = L .sound x a st m ((sh , f) , lk)

    fromSelᴳ : (x : X) (st : L .St)
             → Layerᴳ As (As .body x (L .sel x st)) ⊢ Layerᴳ As (descOf As x)
    fromSelᴳ x st m (sh , f) = ((L .sel x st , sh) , f)

    -- ... and their instances at the world's OWN state, which is where
    -- `lookTotal`'s `Eq.refl` is spent.
    toSel : (x : X) (m : Car (xs x))
          → Layer⁺ (descOf As x) (μ (descOf As)) m
          → Layer⁺ (chosen x m) (μ (descOf As)) m
    toSel x m l = toSelᴳ x (L .look (xs x) m) m (l , Eq.refl)

    fromSel : (x : X) (m : Car (xs x))
            → Layer⁺ (chosen x m) (μ (descOf As)) m
            → Layer⁺ (descOf As x) (μ (descOf As)) m
    fromSel x m l = fromSelᴳ x (L .look (xs x) m) m l

    -- ... AND THE PARSER.

    -- PER-ALTERNATIVE, deliberately. Asking for `DecDesc (chosen x m)`
    -- would be stuck at a variable `m`: `sel x (look m)` does not reduce
    -- until the world is concrete, so no instance could case-split to
    -- supply it.
    module _ (dF : (x : X) (a : As .Alt x) → DecDesc (As .body x a))
             (gF : (x : X) (a : As .Alt x) (m : Car (xs x))
                 → GuardedD (As .body x a) m)
      where

      LLMot : Ix → Type ℓμ
      LLMot i = μ (descOf As) i ⊎ No (μ (descOf As) i)

      -- THE FIXPOINT, as terms. `Inductive`'s header explains why these
      -- cannot be stated generically (`⟦_⟧c` and `μ` sit at different
      -- levels) and must be given where the levels are concrete.
      MuL : (x : X) → TheoryTy ℓμ (xs x)
      MuL x m = μ (descOf As) (x , m)

      rollL : (x : X) → Layerᴳ As (descOf As x) ⊢ MuL x
      rollL x m (sh , f) = sup sh f

      unrollL : (x : X) → MuL x ⊢ Layerᴳ As (descOf As x)
      unrollL x m t = unroll t

      -- THE STEP. The decision is eliminated with `dec-elim` and
      -- reintroduced with `dec-yes` / `dec-no` -- the sanctioned rules of
      -- `Decidable.Additive`.
      llStep : (i : Ix) → ▷g LLMot i → LLMot i
      llStep (x , m) rec =
        dec-elim (Layerᴳ As (chosen x m)) m
          (λ l → dec-yes (MuL x) m (rollL x m (fromSel x m l)))
          (λ k → dec-no  (MuL x) m λ t → k (toSel x m (unrollL x m t)))
          (decLayer (chosen x m) (dF x _) m (gF x _ m) (λ j q → rec j q))

      decLL : (i : Ix) → LLMot i
      decLL = löb llStep

      -- the same uniqueness as `decμ`, for the same reason
      decLL-unfold : (i : Ix) → decLL i ≡ llStep i (λ j _ → decLL j)
      decLL-unfold = löb-unfold llStep

      decLL-unique : (h : (i : Ix) → LLMot i)
                   → ((i : Ix) → h i ≡ llStep i (λ j _ → h j))
                   → (i : Ix) → h i ≡ decLL i
      decLL-unique = löb-unique llStep
