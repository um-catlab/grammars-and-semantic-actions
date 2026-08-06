{-
  The connectives of the semimodule theory: one tensor per operation,
  and THE GRADED EXPONENTIAL as the action tensor with a representable
  in its scalar slot.

      OneG          = ⊗ˢ oneOp ()                the scalar unit
      R ·ᵍ S        = ⊗ˢ mulOp (R , S)           scalar multiplication
      A ⊗ᵃ B        = ⊗ˢ catOp (A , B)           the multiplicative of elements
      ActG R A      = ⊗ˢ actOp (R , A)           the action, R a GRAMMAR of scalars
      !⟨ r ⟩ A      = ActG ⌈ r ⌉ A               the action at a FIXED scalar

  `!⟨ r ⟩ A` holds of exactly the strings that are `r` copies of a string
  satisfying `A`.  That is the multiplicity modality: `!⟨ 2 ⟩ A` is "an A,
  twice, and the two copies are the same".  Note this is strictly finer
  than `A ⊗ᵃ A`, which allows two DIFFERENT A's -- the whole content of
  the graded exponential is that its two copies are forced equal, and
  that is exactly why its laws are non-trivial.

  Two things to note about the spelling.

  ARITIES HAVE NO η.  `⊗ˢ actOp (pairB R A)` cannot be
  written `⊗ˢ actOp (if_then_else_ ...)`, because the two slots have
  different SORTS; and `λ a → f a` is not definitionally `f`, so every
  round-trip below ends in `etaBool`.  This is the tax the many-sorted
  presentation charges, and it is charged once per Iso, not once per
  use.

  REPRESENTABLES ARE THE PARAMETERS.  `⌈ r ⌉ n = (n Eq.≡ r)` is
  subterminal: it pins the scalar slot to a single natural number.  A
  general `R : Scl` does not.  The difference between the two is what
  the non-linear laws in `Graded.agda` turn on, so `ActG` is kept
  primitive and `!⟨_⟩_` is defined from it rather than the other way
  round.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Semimodule.Connectives (Char : Type₀) where

open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Nat
open import Cubical.Data.List
open import Cubical.Data.Empty using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Substrate
open import TheoryGrammar.Instances.Semimodule.Base Char public

-- ==================================================================
-- One tensor per operation.
-- ==================================================================

OneG : Scl
OneG = ⊗ˢ oneOp (λ ())

_·ᵍ_ : Scl → Scl → Scl
R ·ᵍ S = ⊗ˢ mulOp (λ b → if b then R else S)

_⊗ᵃ_ : Elt → Elt → Elt
A ⊗ᵃ B = ⊗ˢ catOp (λ b → if b then A else B)

-- THE ACTION.  Its arity family cannot be an `if_then_else_`: the two
-- slots live in different grammar sorts.
ActG : Scl → Elt → Elt
ActG R A = ⊗ˢ actOp (pairB R A)

-- THE GRADED EXPONENTIAL.
-- (spelled `!⟨ r ⟩ A`: a bare prefix `!` cannot work, since juxtaposition
-- binds tighter than any operator and `! r A` would parse as `! (r A)`.)
!⟨_⟩_ : ℕ → Elt → Elt
!⟨ r ⟩ A = ActG ⌈ r ⌉ A

infixr 20 _·ᵍ_
infixr 20 _⊗ᵃ_
infix  25 !⟨_⟩_

-- ==================================================================
-- PRIMITIVES (phase 1): intro and elim for each tensor.  Everything
-- downstream is a composite of these together with the combinators of
-- `RulesS`.
-- ==================================================================

-- PRIMITIVE: intro for the action.
act-I : {R : Scl} {A : Elt} (r : ℕ) (w : String) → R r → A w → ActG R A (rep r w)
act-I r w x a = mkRep r w , pairB x a

-- PRIMITIVE: elim for the action.
act-E : {R : Scl} {A : Elt} {C : Elt}
      → ((r : ℕ) (w : String) → R r → A w → C (rep r w)) → ActG R A ⊢ C
act-E f _ (mkRep r w , h) = f r w (h true) (h false)

-- PRIMITIVE: intro for the element tensor.
cat-I : {A B : Elt} {u v w : String} → Split3 u v w → A u → B v → (A ⊗ᵃ B) w
cat-I {u = u} {v} s a b = (u , v , s) , pairB a b

-- PRIMITIVE: elim for the element tensor.
cat-E : {A B : Elt} {C : Elt}
      → (∀ {u v w} → Split3 u v w → A u → B v → C w) → (A ⊗ᵃ B) ⊢ C
cat-E f w ((u , v , s) , h) = f s (h true) (h false)

-- PRIMITIVE: intro for scalar multiplication.
mul-I : {R S : Scl} (a b : ℕ) → R a → S b → (R ·ᵍ S) (a · b)
mul-I a b x y = mkFac a b , pairB x y

-- PRIMITIVE: elim for scalar multiplication.
mul-E : {R S : Scl} {C : Scl}
      → ((a b : ℕ) → R a → S b → C (a · b)) → (R ·ᵍ S) ⊢ C
mul-E f _ (mkFac a b , h) = f a b (h true) (h false)

-- PRIMITIVE: the scalar unit.
one-I : OneG 1
one-I = mk1 , λ ()

-- ==================================================================
-- The scalar unit IS the representable at 1, and the tensor of two
-- representables IS the representable at the product.  These are
-- statements about the SUBSTRATE (its splittings at `oneOp`/`mulOp`
-- are singletons), not about any equation of the theory, which is why
-- they are proved here rather than in `Graded.agda`.
-- ==================================================================

OneG≅⌈1⌉ : (p : ℕ) → Iso (OneG p) (⌈ 1 ⌉ p)
OneG≅⌈1⌉ p .Iso.fun (mk1 , _) = Eq.refl
OneG≅⌈1⌉ p .Iso.inv Eq.refl   = one-I
OneG≅⌈1⌉ p .Iso.sec Eq.refl   = refl
OneG≅⌈1⌉ p .Iso.ret (mk1 , z) = ΣPathP (refl , funExt λ ())

private
  mulcong : {a b r s : ℕ} → a Eq.≡ r → b Eq.≡ s → (a · b) Eq.≡ (r · s)
  mulcong Eq.refl Eq.refl = Eq.refl

  ⌈⌉·fwd : (r s n : ℕ) → (⌈ r ⌉ ·ᵍ ⌈ s ⌉) n → ⌈ r · s ⌉ n
  ⌈⌉·fwd r s n (mkFac a b , h) = mulcong (h true) (h false)

  ⌈⌉·back : (r s n : ℕ) → ⌈ r · s ⌉ n → (⌈ r ⌉ ·ᵍ ⌈ s ⌉) n
  ⌈⌉·back r s _ Eq.refl = mul-I r s Eq.refl Eq.refl

  -- the round trip, once the two representables have been matched
  ⌈⌉·ret : (r s a b : ℕ) (p : a Eq.≡ r) (q : b Eq.≡ s)
         → ⌈⌉·back r s (a · b) (⌈⌉·fwd r s (a · b) (mkFac a b , pairB p q))
           ≡ (mkFac a b , pairB p q)
  ⌈⌉·ret r s _ _ Eq.refl Eq.refl =
    ΣPathP (refl , funExt λ { true → refl ; false → refl })

⌈⌉·⌈⌉≅⌈·⌉ : (r s : ℕ) (n : ℕ) → Iso ((⌈ r ⌉ ·ᵍ ⌈ s ⌉) n) (⌈ r · s ⌉ n)
⌈⌉·⌈⌉≅⌈·⌉ r s n .Iso.fun = ⌈⌉·fwd r s n
⌈⌉·⌈⌉≅⌈·⌉ r s n .Iso.inv = ⌈⌉·back r s n
⌈⌉·⌈⌉≅⌈·⌉ r s n .Iso.sec Eq.refl = refl
-- the arity's missing η is supplied by `etaBool`
⌈⌉·⌈⌉≅⌈·⌉ r s n .Iso.ret (mkFac a b , h) =
    cong (λ k → ⌈⌉·back r s (a · b) (⌈⌉·fwd r s (a · b) (mkFac a b , k))) (sym (etaBool h))
  ∙ ⌈⌉·ret r s a b (h true) (h false)
  ∙ ΣPathP (refl , etaBool h)

-- ==================================================================
-- Congruence of the action in either slot.  An `Iso` at every carrier
-- point lifts to an `Iso` of the tensors, because `⊗ˢ` is a Σ over the
-- splittings and a Π over the slots and neither sees the payload.
-- ==================================================================

ActG-congˡ : {R S : Scl} (A : Elt) → ((n : ℕ) → Iso (R n) (S n))
           → (m : String) → Iso (ActG R A m) (ActG S A m)
ActG-congˡ A I m = go
  where
    go : _
    go .Iso.fun (mkRep r w , h) = mkRep r w , pairB (I r .Iso.fun (h true)) (h false)
    go .Iso.inv (mkRep r w , h) = mkRep r w , pairB (I r .Iso.inv (h true)) (h false)
    go .Iso.sec (mkRep r w , h) =
      ΣPathP (refl , funExt λ { true → I r .Iso.sec (h true) ; false → refl })
    go .Iso.ret (mkRep r w , h) =
      ΣPathP (refl , funExt λ { true → I r .Iso.ret (h true) ; false → refl })

ActG-congʳ : (R : Scl) {A B : Elt} → ((w : String) → Iso (A w) (B w))
           → (m : String) → Iso (ActG R A m) (ActG R B m)
ActG-congʳ R I m = go
  where
    go : _
    go .Iso.fun (mkRep r w , h) = mkRep r w , pairB (h true) (I w .Iso.fun (h false))
    go .Iso.inv (mkRep r w , h) = mkRep r w , pairB (h true) (I w .Iso.inv (h false))
    go .Iso.sec (mkRep r w , h) =
      ΣPathP (refl , funExt λ { true → refl ; false → I w .Iso.sec (h false) })
    go .Iso.ret (mkRep r w , h) =
      ΣPathP (refl , funExt λ { true → refl ; false → I w .Iso.ret (h false) })
