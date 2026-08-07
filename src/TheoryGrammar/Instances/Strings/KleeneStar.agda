{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- A * as the generic μ, guarded exactly when A is non-nullable. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Strings.KleeneStar (Char : Type₀) where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.List
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded
open import TheoryGrammar.Theories.MonoidStar

open import TheoryGrammar.Instances.Strings.Decomposition Char public

-- The description and its guardedness are NOT string-specific: they
-- are the generic monoid star (TheoryGrammar.Theories.MonoidStar) at
-- this promodel.  Opened SELECTIVELY, so `MonStar`'s own `Guard` and
-- `ε'` re-exports do not collide with the ones this chain already has.
open MonStar strGraded using (starSlot; starAlt; starF; ProperBody) public

-- non-nullability, internally: a non-nullable grammar entails the
-- resource predicate.  This is the string spelling of the generic
-- `ProperBody`, and `nn→proper` is the whole difference between them --
-- `StrProper` at the right slot IS `NonTrivial` of the left part.
NonNullable : Gr → Type₀
NonNullable A = A ⊢ NonTrivial

nn→proper : {A : Gr} → NonNullable A → ProperBody A
nn→proper nn m sp a = nn _ a

-- THE UNIT versus GUARDEDNESS.  `A *` is guarded exactly when `A` is
-- NON-NULLABLE.  If `A` accepts ε then the splitting `(ε , w)` puts
-- the recursive occurrence back at `w`, and the star has infinitely
-- many parses at every index -- the classic `(ε)*` problem.  The type
-- `μ (starF A)` still exists and every tree in it is finite; it is
-- enumeration and `hyloC` that fail.
starGuarded : (A : Gr) → NonNullable A → (x : Unit) → Guarded (starF A x)
starGuarded A nn = MonStar.starGuarded strGraded A (nn→proper nn)

-- literals are non-nullable, so `literal c *` is guarded
literalNN : (c : Char) → NonNullable (literal c)
literalNN c = ⌈⌉-E (c , ⊗-mk (cons nil) Eq.refl tt)

KL* : Gr → Gr
KL* A w = μ (starF A) (tt , w)

module _ {A : Gr} where

  nil* : ε' ⊢ KL* A
  nil* w e = sup (true , lift e) λ ()

  cons* : (A ⊗' KL* A) ⊢ KL* A
  cons* w ((u , v , s) , h) =
    sup (false , (u , v , s) , λ { true → lift (h true) ; false → tt* })
        λ { (true  , ()) ; (false , _) → h false }

  unroll* : KL* A ⊢ (ε' ⊕ (A ⊗' KL* A))
  unroll* w t with unroll t
  ... | (true  , e)        , f = inl (lower e)
  ... | (false , sp , sh)  , f =
    inr (sp , λ { true → lower (sh true) ; false → f (false , tt*) })

-- The star algebra, point-free: this is `roll` for the star.
roll* : {A : Gr} → (ε' ⊕ (A ⊗' KL* A)) ⊢ KL* A
roll* = ⊕-E nil* cons*
