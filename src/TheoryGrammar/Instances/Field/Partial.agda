{-
  PARTIALITY, VISIBLE IN THE CALCULUS.

  One primitive, `dec-inv : ⊤G ⊢ Imgˢ invOp ⊕ ⌈ f0 ⌉` -- "every element
  is an inverse, or is zero" -- and everything else is a composite of
  `Rules`/`DecAdd` combinators.  The two sharp statements:

      Imgˢ invOp   ⊣⊢  ¬G ⌈ f0 ⌉        (invertible  ⟺  nonzero)
      Domˢ invOp _ ⊣⊢  ¬G ⌈ f0 ⌉        (in the domain of inv, ditto)

  The right-hand sides are internal negations, not metalanguage ones, so
  "inv is undefined at 0" is a THEOREM OF THE CALCULUS.

  DEFINES `Nonzero`, the primitive `dec-inv`, the four one-directional
  theorems `img-inv⊢nonzero`/`nonzero⊢img-inv`/`dom-inv⊢nonzero`/
  `nonzero⊢dom-inv`, their pairings `img-inv⊣⊢nonzero`/`dom-inv⊣⊢nonzero`,
  and the decisions `invDecision`/`dec-invOp`/`dec-nonzero`.

  ONE THEOREM OR TWO?  Two.  Each direction is proved and named on its
  own, and every consumer -- `NoPoint`, `Joint`, `Tests` -- takes a
  single direction.  The `⊣⊢` pairings below are DERIVED, kept only
  because "invertibility IS nonzeroness" is the claim being made and a
  conjunctive conclusion is the honest way to say `is`.
-}
{-# OPTIONS --lossy-unification #-}
module TheoryGrammar.Instances.Field.Partial where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Domain
open import TheoryGrammar.Instances.Field.Base

-- Brings in the two grammars this file is about, at `fldFib`:
--   `Imgˢ o`    DENOTES "this element IS an o-composite"   (`⊗ˢ o ⊤`)
--   `Domˢ o i`  DENOTES "this element OCCURS in slot i of one"
-- At the unary `invOp` they read "m is somebody's inverse" and "m has
-- an inverse"; `inv` is an involution on 𝔽₃, so §2 proves they agree.
open DomainOf fldFib public

-- `Gr` DENOTES a predicate on field elements -- the only sort there is.
Gr : Type₁
Gr = TheoryTy ℓ-zero tt

-- `_⊣⊢_`, internal logical equivalence, is `Decidable.Additive`'s: it
-- mentions only `_⊢_`, so it was never a field notion, and it arrives
-- here through `DomainOf`'s re-export.  Its fixity (`infix 1`) is
-- declared there.

-- ==================================================================
-- The one primitive: the domain of definition is DECIDED, and its
-- complement is exactly the representable at zero.
-- ==================================================================

-- `Nonzero` DENOTES "this element is not zero", internally: a map out of
-- the representable at f0 into ⊥G.  Not a `Dec`, not a `Bool` -- the
-- refutation itself is the inhabitant, so downstream uses spend it
-- rather than re-testing.
Nonzero : Gr
Nonzero = ¬G ⌈ f0 ⌉

dec-inv : ⊤G ⊢ (Imgˢ invOp ⊕ ⌈ f0 ⌉)          -- PRIMITIVE
dec-inv f0 _ = ⊕-I₂ {B = ⌈ f0 ⌉} {A = Imgˢ invOp} f0 Eq.refl
dec-inv f1 _ = ⊕-I₁ {A = Imgˢ invOp} {B = ⌈ f0 ⌉} f1 (tt , λ _ → tt)
dec-inv f2 _ = ⊕-I₁ {A = Imgˢ invOp} {B = ⌈ f0 ⌉} f2 (tt , λ _ → tt)

-- ==================================================================
-- 1.  BEING INVERTIBLE REFUTES BEING ZERO.
--
-- The statement asked for: `⊗ˢ invOp ⊤ ⊢ ¬G ⌈ 0 ⌉`, with `¬G` the
-- internal negation.  `Imgˢ invOp` IS `⊗ˢ invOp (λ _ → ⊤G)`.
-- ==================================================================

img-inv⊢nonzero : Imgˢ invOp ⊢ Nonzero
img-inv⊢nonzero m (sp , _) e = E.rec (nz-transport e sp)

-- ... and the converse, which is where the primitive is spent.  Note
-- the sum is eliminated with `⊕-E-at`, never matched.
nonzero⊢img-inv : Nonzero ⊢ Imgˢ invOp
nonzero⊢img-inv m k =
  ⊕-E-at (Imgˢ invOp) ⌈ f0 ⌉ m (λ x → x) (λ e → ⊥-E {A = Imgˢ invOp} m (k e)) (dec-inv m tt)

-- THE DOMAIN OF DEFINITION OF inv, INTERNALLY: exactly the nonzero
-- elements.  DERIVED pairing of the two theorems above; the relation is
-- `⊣⊢`, not `≡`, and the name now says so.
img-inv⊣⊢nonzero : Imgˢ invOp ⊣⊢ Nonzero
img-inv⊣⊢nonzero = img-inv⊢nonzero , nonzero⊢img-inv

-- ==================================================================
-- 2.  THE SAME AT THE ARGUMENT SIDE.  `Imgˢ` says which elements ARE
-- inverses; `Domˢ` says which elements HAVE one.  For a general partial
-- operation these differ; here `inv` is an involution, so they agree,
-- and it is `Domˢ` that the no-total-point theorem needs.
-- ==================================================================

dom-inv⊢nonzero : Domˢ invOp tt ⊢ Nonzero
dom-inv⊢nonzero x (m , sp , e) ze =
  E.rec (nz-transport ze (nz-transport e (inv-nz m sp)))

nonzero⊢dom-inv : Nonzero ⊢ Domˢ invOp tt
nonzero⊢dom-inv x k = x , sp , inv-fix x sp
  where sp : Nz x
        sp = nonzero⊢img-inv x k .fst

-- DERIVED pairing, as above.
dom-inv⊣⊢nonzero : Domˢ invOp tt ⊣⊢ Nonzero
dom-inv⊣⊢nonzero = dom-inv⊢nonzero , nonzero⊢dom-inv

-- ==================================================================
-- 3.  AND SO INVERTIBILITY IS A DECISION, in the sense of
-- `Decidable.Additive`: a map to the sum TOGETHER with the exclusion.
-- Without `exclude` the sum would decide nothing.
-- ==================================================================

invDecision : Decision (Imgˢ invOp) ⌈ f0 ⌉
invDecision .decide  = dec-inv
invDecision .exclude = ⇒-app ∘⊢ &-I (img-inv⊢nonzero ∘⊢ &-E₁) &-E₂

dec-invOp : ⊤G ⊢ Dec⟨ Imgˢ invOp ⟩
dec-invOp = toDec invDecision

dec-nonzero : ⊤G ⊢ Dec⟨ Nonzero ⟩
dec-nonzero = dec-map (Imgˢ invOp) Nonzero img-inv⊢nonzero nonzero⊢img-inv
            ∘⊢ dec-invOp
