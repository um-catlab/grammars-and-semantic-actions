open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Par.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure
open import Cubical.Data.List
open import Cubical.Data.Sigma

open import Grammar.Base Alphabet
open import Grammar.Bottom Alphabet
open import Grammar.Epsilon Alphabet using (ε)
open import Grammar.Top Alphabet
open import Grammar.Function Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.Product Alphabet
open import Grammar.Product.Binary.AsPrimitive Alphabet
open import Grammar.Sum.Binary.AsPrimitive Alphabet
open import Grammar.String Alphabet
open import Term.Base Alphabet

private
  variable
    ℓA ℓB ℓC ℓD : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD

-- The multiplicative disjunction, internally.
--
-- Semantically  (A ⅋ B) w  ≃  ∀ (u , v). w ≡ u ++ v → A u ⊎ B v :
-- a ⅋-inhabitant chooses, for EVERY way of splitting w, a disjunct that
-- holds on its part of the split.  This is the pointwise De Morgan dual
-- of ⊗ (which CHOOSES one split and inhabits both parts).
--
-- The encoding is the same external-quantifier + ⌈⌉-localization pattern
-- as √l-string (Grammar.Derivative.String):
--   √l-string w A = (⌈ w ⌉ ⊗ ⊤) ⇒ (⌈ w ⌉ ⊗ A)
-- Here the antecedent ⌈ u ⌉ ⊗ ⌈ v ⌉ pins the index to w ≡ u ++ v, and the
-- consequent carries each disjunct at its own substring, re-anchored by
-- the other side's ⌈⌉:
--   left  disjunct:  A ⊗ ⌈ v ⌉   (A holds at u)
--   right disjunct:  ⌈ u ⌉ ⊗ B   (B holds at v)
-- No new SPFunctor code and no positivity extension: ⅋ is derived from
-- &ᴰ, ⇒, ⊗, ⊕, ⌈⌉.
_⅋_ : Grammar ℓA → Grammar ℓB → Grammar (ℓ-max ℓA ℓB)
A ⅋ B =
  &[ uv ∈ String × String ]
    ((⌈ uv .fst ⌉ ⊗ ⌈ uv .snd ⌉) ⇒ ((A ⊗ ⌈ uv .snd ⌉) ⊕ (⌈ uv .fst ⌉ ⊗ B)))

infixr 6 _⅋_

-- Introduction: supply, for each candidate split (u , v), a choice of
-- disjunct.  This is the only general intro form — a ⅋-inhabitant is a
-- choice function over splits, which is why ⅋ never preserves isLang.
⅋-intro :
  (∀ u v → (C & (⌈ u ⌉ ⊗ ⌈ v ⌉)) ⊢ ((A ⊗ ⌈ v ⌉) ⊕ (⌈ u ⌉ ⊗ B)))
  → C ⊢ (A ⅋ B)
⅋-intro f = &ᴰ-intro λ uv → ⇒-intro (f (uv .fst) (uv .snd))

-- Elimination: interrogate a ⅋ at one chosen split.
⅋-app :
  ∀ u v → ((A ⅋ B) & (⌈ u ⌉ ⊗ ⌈ v ⌉)) ⊢ ((A ⊗ ⌈ v ⌉) ⊕ (⌈ u ⌉ ⊗ B))
⅋-app u v = ⇒-app ∘g &-intro (π (u , v) ∘g π₁) π₂

-- Functoriality (covariant in both arguments).
⅋-map : A ⊢ C → B ⊢ D → (A ⅋ B) ⊢ (C ⅋ D)
⅋-map f g =
  &ᴰ-intro λ uv →
    ⇒-intro
      (⊕-elim (inl ∘g (f ,⊗ id)) (inr ∘g (id ,⊗ g))
       ∘g ⇒-app
       ∘g &-intro (π uv ∘g π₁) π₂)

-- Both-sides injections: a total refutation of the left factor refutes
-- every split, regardless of the right side (and symmetrically).
⅋-inl : (⊤ ⊢ A) → ⊤ ⊢ (A ⅋ B)
⅋-inl a =
  ⅋-intro (λ u v → inl ∘g ((a ∘g ⊤-intro) ,⊗ id) ∘g π₂)

⅋-inr : (⊤ ⊢ B) → ⊤ ⊢ (A ⅋ B)
⅋-inr b =
  ⅋-intro (λ u v → inr ∘g (id ,⊗ (b ∘g ⊤-intro)) ∘g π₂)

-- The guarded core: quantify only over splits with BOTH parts nonempty.
-- Every position then sits at a strictly shorter string (each part misses
-- the other, nonempty, part) — the FactorsThroughLater condition — so
-- functors built from ⅋∘ are locally contractive by construction.
-- NOTE: ⅋∘ is deliberately a SECOND connective, not a restriction baked
-- into ⅋.  The proper-split par is unitless (its right part never covers
-- the whole index, so no U can satisfy U ⅋∘ A ≃ A — same reason ▷ has no
-- counit), while NES is a lax unit for the full ⅋: extraction via the
-- (ε , w) instance, embedding by EXTERNAL case on the &ᴰ index (no
-- decidability needed).
_⅋∘_ : Grammar ℓA → Grammar ℓB → Grammar (ℓ-max ℓA ℓB)
A ⅋∘ B =
  &[ uv ∈ NonEmptyString × NonEmptyString ]
    ((⌈ uv .fst .fst ⌉ ⊗ ⌈ uv .snd .fst ⌉) ⇒
      ((A ⊗ ⌈ uv .snd .fst ⌉) ⊕ (⌈ uv .fst .fst ⌉ ⊗ B)))

infixr 6 _⅋∘_

-- Restriction: forget the boundary splits.
⅋-restrict : (A ⅋ B) ⊢ (A ⅋∘ B)
⅋-restrict = &ᴰ-intro λ uv → π (uv .fst .fst , uv .snd .fst)

-- The nullability bridge ⅋∘-complete (recovering the full ⅋ from the
-- guarded core when both operands cover ε) and the Chu consistency lemma
-- ⊗⅋-disjoint live in Grammar.Par.Properties, keeping this module
-- hole-free and importable.
