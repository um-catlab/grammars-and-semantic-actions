{-
  PARTIALITY, VISIBLE IN THE CALCULUS.

  One primitive, `dec-inv : ⊤G ⊢ Imgˢ invOp ⊕ ⌈ f0 ⌉` -- "every element
  is an inverse, or is zero" -- and everything else is a composite of
  `Rules`/`DecAdd` combinators.  The two sharp statements:

      Imgˢ invOp   ⊣⊢  ¬G ⌈ f0 ⌉        (invertible  ⟺  nonzero)
      Domˢ invOp _ ⊣⊢  ¬G ⌈ f0 ⌉        (in the domain of inv, ditto)

  The right-hand sides are internal negations, not metalanguage ones, so
  "inv is undefined at 0" is a THEOREM OF THE CALCULUS.
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
open import TheoryGrammar.Instances.Field.Base
open import TheoryGrammar.Instances.Field.Domain

open DomainOf fldFib public

Gr : Type₁
Gr = TheoryTy ℓ-zero tt

-- internal logical equivalence: the two maps, nothing else
_⊣⊢_ : Gr → Gr → Type₀
A ⊣⊢ B = (A ⊢ B) × (B ⊢ A)

infix 1 _⊣⊢_

-- ==================================================================
-- The one primitive: the domain of definition is DECIDED, and its
-- complement is exactly the representable at zero.
-- ==================================================================

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
-- elements.
img-inv≡nonzero : Imgˢ invOp ⊣⊢ Nonzero
img-inv≡nonzero = img-inv⊢nonzero , nonzero⊢img-inv

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

dom-inv≡nonzero : Domˢ invOp tt ⊣⊢ Nonzero
dom-inv≡nonzero = dom-inv⊢nonzero , nonzero⊢dom-inv

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
