{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- Derivative PARSING with the later modality: an intrinsically-typed
-- decision  ⊤ ⊢ (a* ⊕ ¬G a*)  built as a Löb fixed point whose body is
-- the Brzozowski derivative step:
--
--   ε        ↦ inl NIL                       (nullability of a*)
--   a-headed ↦ interrogate the later at [a]  (recurse at Dl a* a = a*),
--              CONS on a parse, extend on a refutation
--   b-headed ↦ inr                           (Dl a* b = ⊥)
--
-- a* is derivative-closed, so a single grammar suffices — no family.
-- The body is an internal combinator pipeline driven by the first-char
-- decision atom; the two refutation-extension lemmas are the holes.
module Examples.DerivativeLobTest where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool)
open import Cubical.Data.List
open import Cubical.Data.List.Properties using (¬cons≡nil)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Sum as Sum using ()
open import Cubical.Data.Empty as Empty using ()
import Cubical.Data.Equality as Eq

Alphabet : hSet ℓ-zero
Alphabet = (Bool , isSetBool)

open import Grammar.Base Alphabet
open import Grammar.Top Alphabet
open import Grammar.String Alphabet
open import Grammar.Literal Alphabet
open import Grammar.Epsilon Alphabet using (ε)
open import Grammar.LinearProduct Alphabet
open import Grammar.Function Alphabet using (_⇒_ ; ⇒-app)
open import Grammar.Negation Alphabet
open import Grammar.Product Alphabet using (π)
open import Grammar.Product.Binary.AsPrimitive Alphabet
  using (_&_ ; &-intro ; π₁ ; π₂)
open import Grammar.Sum.Binary.AsPrimitive Alphabet
  using (_⊕_ ; inl ; inr ; ⊕-elim ; ⊗⊕-distL)
open import Grammar.Distributivity Alphabet using (&⊕-distL)
open import Grammar.KleeneStar.Inductive Alphabet
open import Grammar.Later.Base Alphabet
open import Term.Base Alphabet

private
  a b : Bool
  a = true
  b = false

  A* : Grammar ℓ-zero
  A* = (literal a) *

  -- the decision grammar: a parse or a refutation, by type
  G : Grammar ℓ-zero
  G = A* ⊕ ¬G A*

  [a]ne : NonEmptyString
  [a]ne = (a ∷ []) , (λ p → Empty.rec (¬cons≡nil p))

opaque
  unfolding _⊗_ _⇒_ _⊕_ ε ⊤ literal

  -- First-character decision atom (pointwise once, like dec-ε):
  -- every string is empty, a-headed, or b-headed.
  dec-first : ⊤ ⊢ (ε ⊕ ((literal a ⊗ ⊤) ⊕ (literal b ⊗ ⊤)))
  dec-first [] _ = Sum.inl Eq.refl
  dec-first (true ∷ v) _ =
    Sum.inr (Sum.inl ((((true ∷ []) , v) , Eq.refl) , Eq.refl , tt))
  dec-first (false ∷ v) _ =
    Sum.inr (Sum.inr ((((false ∷ []) , v) , Eq.refl) , Eq.refl , tt))

-- ⌈ [a] ⌉ is definitionally literal a ⊗ ε, so the reshapes are unitors.
lit→⌈⌉⊗⊤ : (literal a ⊗ ⊤) ⊢ (⌈ a ∷ [] ⌉ ⊗ ⊤)
lit→⌈⌉⊗⊤ = ⊗-unit-r⁻ ,⊗ id

⌈⌉→lit : ⌈ a ∷ [] ⌉ ⊢ literal a
⌈⌉→lit = ⊗-unit-r

-- The two refutation-extension lemmas — the genuine content, both
-- provable from the star-unrolling iso plus literal-prefix alignment
-- (unique splitting of a single-character prefix / disjoint literals).
extend-¬ : (⌈ a ∷ [] ⌉ ⊗ ¬G A*) ⊢ ¬G A*
extend-¬ = {!!}

refute-b : (literal b ⊗ ⊤) ⊢ ¬G A*
refute-b = {!!}

-- The derivative step, as an internal Löb body: pair with the first-char
-- decision, distribute, and act per case.  The single ⇒-app against the
-- projected later IS the recursive call at the derivative.
body : ▷ G ⊢ G
body =
  ⊕-elim
    (inl ∘g NIL ∘g π₂)
    (⊕-elim
      (⊕-elim
         (inl ∘g CONS ∘g (⌈⌉→lit ,⊗ id))
         (inr ∘g extend-¬)
       ∘g ⊗⊕-distL
       ∘g ⇒-app
       ∘g &-intro (π [a]ne ∘g π₁) (lit→⌈⌉⊗⊤ ∘g π₂))
      (inr ∘g refute-b ∘g π₂)
     ∘g &⊕-distL)
  ∘g &⊕-distL
  ∘g &-intro id (dec-first ∘g ⊤-intro)

-- The parser: total by lob, intrinsically sound by type.
parseA* : ⊤ ⊢ (A* ⊕ ¬G A*)
parseA* = lob body
