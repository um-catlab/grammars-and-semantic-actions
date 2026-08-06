{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  ONE GENERATING-FUNCTION IDENTITY, DONE INTERNALLY: CATALAN.

  ------------------------------------------------------------------
  WHAT IS BEING CLAIMED
  ------------------------------------------------------------------

  A ℕ-graded type is a power series with type coefficients
  (`Instances/Nat/Base.agda`).  The Dyck grammar is the least fixed point

      D  =  1  ⊕  x ⊗ D ⊗ x ⊗ D

  and reading it off coefficientwise is exactly

      C(x)  =  1 + x² C(x)²,       C₀ = 1,  C_{n+1} = Σ_{i+j=n} Cᵢ Cⱼ

  the Catalan recurrence.  So the two terms `dyck-roll` / `dyck-unroll`
  below ARE that recurrence -- not a statement about it, and not a proof
  that some numbers satisfy it, but the bijection itself, at every degree
  at once.  Degrees here are lengths of bracket words, so the coefficient
  at 2k is Catalan(k) and the coefficient at 2k+1 is empty; the grammar
  knows that because the description consumes TWO generators per node.

  ------------------------------------------------------------------
  HOW IT IS BUILT
  ------------------------------------------------------------------

  `D` is NOT a hand-written datatype.  It is `μ` of a DESCRIPTION, in the
  generic functor language of `TheoryGrammar.Inductive`, exactly as
  `Strings/KleeneStar.agda` builds `KL*` as `μ (ε ⊕ (A ⊗ Var))`.  What
  has to be supplied, and all that has to be supplied, is:

    * the description `dyckF`  (four lines, no proofs)
    * `dyckGuarded`, i.e. every recursive occurrence sits at a strictly
      smaller degree.  This is where the two generators earn their keep:
      the recursive slots are guarded because their SIBLING is `x`, and
      `x` forces the sibling to have degree 1.  `slotProper` is exactly
      that argument, and `degNT` is the one primitive that turns "the
      left factor is the generator" into "the right factor is smaller".

  Guardedness is what makes `hyloC` available, so any fold or unfold over
  Dyck words -- counting, evaluating, re-bracketing -- is a term of the
  calculus and terminates by construction.

  ------------------------------------------------------------------
  PHASE DISCIPLINE
  ------------------------------------------------------------------

  Everything after the description is phase 2: `toDesc` / `fromDesc` are
  composites of `⊕-E`, `⊕ᴰ-in`, `⊗ˢ-map`, `idg`, `liftg`, `lowerg`, and
  the two fixpoint primitives `rollg` / `unrollg`.  Compare
  `Strings/KleeneStar.agda`, where `nil*` / `cons*` / `unroll*` are
  written pointfully, matching `sup` and threading `tt*` and `lower` by
  hand.  Those are avoidable: the only real content in crossing between
  `⟦ F ⟧c` and the surface connectives is (a) `⊕e` versus `⊕`, discharged
  by `⊕ᴰ-in` / `⊕-E`, and (b) the `Lift` that `⟦ ⌜ A ⌝ ⟧c` puts on
  constants, discharged by `liftg` / `lowerg`.  Both are bookkeeping, and
  both compose.

  `rollg` / `unrollg` are generic in the description and in the
  nonterminal, so they BELONG UPSTREAM in `TheoryGrammar.Inductive`
  alongside `roll` / `unroll`; they are defined here only because this
  file may not edit the core.

  ------------------------------------------------------------------
  AND ITS IMAGE AT STRINGS
  ------------------------------------------------------------------

  `Instances/Nat/Length.agda` shows `length` reflects splittings, so
  `pull` carries a ℕ-level ⊗-isomorphism to a string-level one
  (`transportGF`).  Applied here, the Catalan bijection above becomes an
  isomorphism of STRING grammars over any alphabet: `pull D` is "the
  strings whose LENGTH admits a Dyck bracketing", and the recurrence
  transports verbatim.  (`pull D` is of course not the string Dyck
  language itself -- `length` forgets which letters were used, so the
  transported statement is the length-graded shadow.  Getting the
  language on the nose is a change of SIGNATURE, not of model.)

  One friction, recorded rather than papered over: `Length.agda` works at
  `Strings/Base.agda`'s copy of `monSig`, while this file works at
  `Nat/Base.agda`'s copy.  The two `MonOp` datatypes are identical and
  definitionally distinct, so the composite cannot be written down
  without the shared-signature refactor described in `Length.agda`'s
  header.
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Nat.Species where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Substrate
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded

open import TheoryGrammar.Instances.Nat.Graded public

-- ==================================================================
-- THE DESCRIPTION.  `⊗e` is binary (its arity is `Bool`), so the
-- four-factor body  x ⊗ D ⊗ x ⊗ D  is three nested `⊗e`s, read
-- right-associated exactly as `_⊗'_` is.
-- ==================================================================

-- x ⊗ D
dyck₄ : Bool → Functor tt
dyck₄ true  = ⌜ x ⌝
dyck₄ false = Var tt

-- D ⊗ (x ⊗ D)
dyck₃ : Bool → Functor tt
dyck₃ true  = Var tt
dyck₃ false = ⊗e appop dyck₄

-- x ⊗ (D ⊗ (x ⊗ D))
dyck₂ : Bool → Functor tt
dyck₂ true  = ⌜ x ⌝
dyck₂ false = ⊗e appop dyck₃

dyckAlt : Bool → Functor tt
dyckAlt true  = ⌜ ε' ⌝
dyckAlt false = ⊗e appop dyck₂

dyckF : Unit → Functor tt
dyckF _ = ⊕e Bool dyckAlt

-- ==================================================================
-- GUARDEDNESS.  The recursive slots are `dyck₃ true` (the first D) and
-- `dyck₄ false` (the second D); both live inside the right factor of a
-- product whose LEFT factor is the generator `x`, and `x` at degree i
-- forces i = 1.  So `slotProper` fires once, at the outermost ⊗, and
-- everything under it merely has to not grow.
-- ==================================================================

dyckGuarded : (u : Unit) → Guarded (dyckF u)
dyckGuarded tt = <⊕e Bool dyckAlt alt
  where
    ≤₄ : Guarded≤ (⊗e appop dyck₄)
    ≤₄ = ≤⊗e appop dyck₄ (λ { true → ≤⌜⌝ x ; false → ≤Var tt })

    ≤₃ : Guarded≤ (⊗e appop dyck₃)
    ≤₃ = ≤⊗e appop dyck₃ (λ { true → ≤Var tt ; false → ≤₄ })

    go : (n : ℕ) (sp : MonSplit appop n)
         (sh : (a : Bool) → Sh (dyck₂ a) (MonParts appop n sp a))
         (a : Bool) (p : Pos (dyck₂ a) _ (sh a))
       → degIx (nx (dyck₂ a) _ (sh a) p) < n
    go n sp sh true ()
    go n (i , j , a) sh false p =
      slotProper appop n (i , j , a) false ≤₃ (degNT (lower (sh true))) (sh false) p

    alt : (b : Bool) → Guarded (dyckAlt b)
    alt true  = <⌜⌝ ε'
    alt false = ⊗-guard appop dyck₂ go

-- ==================================================================
-- THE GRAMMAR, and the fixpoint primitives.
-- ==================================================================

D : Gr
D n = μ dyckF (tt , n)

-- PRIMITIVE (phase 1), and GENERIC -- belongs upstream in
-- `TheoryGrammar.Inductive`.  `roll`/`unroll` there are stated in the
-- CONTAINER form `⟦ F ⟧`; these are the same two maps in the CONNECTIVE
-- form `⟦ F ⟧c`, which is the one programs are written against.
rollg : (F : (u : Unit) → Functor tt)
      → ⟦ F tt ⟧c (μ F) ⊢ (λ n → μ F (tt , n))
rollg F n t = roll (fromC (F tt) n t)

unrollg : (F : (u : Unit) → Functor tt)
        → (λ n → μ F (tt , n)) ⊢ ⟦ F tt ⟧c (μ F)
unrollg F n t = toC (F tt) n (unroll t)

-- ==================================================================
-- The description's body, spelled in the connectives.  Each `Bodyₖ` is
-- DEFINITIONALLY `⟦ dyckₖ _ ⟧c (μ dyckF)`; the names exist only so the
-- families can be passed explicitly to `⊗ˢ-map`, which cannot infer them
-- (the CLAUDE.md trap: grammar-valued implicits are not recoverable).
-- ==================================================================

Body : Gr
Body n = ⟦ dyckF tt ⟧c (μ dyckF) n

BodyAlt : Bool → Gr
BodyAlt b n = ⟦ dyckAlt b ⟧c (μ dyckF) n

Body₂ : Bool → Gr
Body₂ a n = ⟦ dyck₂ a ⟧c (μ dyckF) n

Body₃ : Bool → Gr
Body₃ a n = ⟦ dyck₃ a ⟧c (μ dyckF) n

Body₄ : Bool → Gr
Body₄ a n = ⟦ dyck₄ a ⟧c (μ dyckF) n

-- THE SURFACE FORM.  `_⊗'_` is infixr 20, so this reads
-- `x ⊗ (D ⊗ (x ⊗ D))` -- the same association as the description.
DyckBody : Gr
DyckBody = ε' ⊕ (x ⊗' D ⊗' x ⊗' D)

-- ==================================================================
-- Crossing between the surface form and the description, in phase 2.
-- ==================================================================

to₄ : (x ⊗' D) ⊢ ⊗ˢ appop Body₄
to₄ = ⊗ˢ-map appop {A = λ b → if b then x else D} {B = Body₄}
        (λ { true → liftg ; false → idg })

to₃ : (D ⊗' x ⊗' D) ⊢ ⊗ˢ appop Body₃
to₃ = ⊗ˢ-map appop {A = λ b → if b then D else (x ⊗' D)} {B = Body₃}
        (λ { true → idg ; false → to₄ })

to₂ : (x ⊗' D ⊗' x ⊗' D) ⊢ ⊗ˢ appop Body₂
to₂ = ⊗ˢ-map appop {A = λ b → if b then x else (D ⊗' x ⊗' D)} {B = Body₂}
        (λ { true → liftg ; false → to₃ })

toDesc : DyckBody ⊢ Body
toDesc = ⊕-E (⊕ᴰ-in {A = BodyAlt} true  ∘g liftg)
             (⊕ᴰ-in {A = BodyAlt} false ∘g to₂)

from₄ : ⊗ˢ appop Body₄ ⊢ (x ⊗' D)
from₄ = ⊗ˢ-map appop {A = Body₄} {B = λ b → if b then x else D}
          (λ { true → lowerg ; false → idg })

from₃ : ⊗ˢ appop Body₃ ⊢ (D ⊗' x ⊗' D)
from₃ = ⊗ˢ-map appop {A = Body₃} {B = λ b → if b then D else (x ⊗' D)}
          (λ { true → idg ; false → from₄ })

from₂ : ⊗ˢ appop Body₂ ⊢ (x ⊗' D ⊗' x ⊗' D)
from₂ = ⊗ˢ-map appop {A = Body₂} {B = λ b → if b then x else (D ⊗' x ⊗' D)}
          (λ { true → lowerg ; false → from₃ })

fromDesc : Body ⊢ DyckBody
fromDesc = ⊕ᴰ-elim {A = BodyAlt} (λ { true  → ⊕-I₁ ∘g lowerg
                                    ; false → ⊕-I₂ ∘g from₂ })

-- ==================================================================
-- THE CATALAN RECURRENCE, as two terms.
--
--     D  ≅  1 ⊕ x·D·x·D            i.e.   C(x) = 1 + x²C(x)²
--
-- Both directions are composites of combinators and the two fixpoint
-- primitives.  No `Add3` and no `sup` appears after the description.
-- ==================================================================

dyck-roll : DyckBody ⊢ D
dyck-roll = rollg dyckF ∘g toDesc

dyck-unroll : D ⊢ DyckBody
dyck-unroll = fromDesc ∘g unrollg dyckF

-- The three constructors, as corollaries, so the grammar can be USED
-- without ever mentioning its description again.

dyck-nil : ε' ⊢ D
dyck-nil = dyck-roll ∘g ⊕-I₁

dyck-node : (x ⊗' D ⊗' x ⊗' D) ⊢ D
dyck-node = dyck-roll ∘g ⊕-I₂
