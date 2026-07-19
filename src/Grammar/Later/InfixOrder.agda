{- The strict infix (proper substring) order on strings.

   u <ⁱ w iff u occurs inside w with a nonempty context l, r: l ++ u ++ r ≡ w
   where l and r are not both empty.  A string may occur at several positions,
   so the occurrence witness must be truncated for the order to be
   prop-valued (as WFOrder requires).

   Well-foundedness is inherited from ℕ along the length measure: a proper
   infix is strictly shorter.  Equalities in the occurrence witness live in
   Eq-world, following the convention of Grammar.Later.SuffixOrder. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Later.InfixOrder (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.List.MoreMore using (++-assoc-Eq)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Induction.WellFounded
import Cubical.Data.Equality as Eq

open import String.Base Alphabet using (String)

private
  Str : Type ℓ-zero
  Str = String

-- One occurrence of u inside w, with its (not-both-empty) context.
Occ : Str → Str → Type ℓ-zero
Occ u w =
  Σ[ l ∈ Str ] Σ[ r ∈ Str ]
    ((l Eq.≡ [] → r Eq.≡ [] → ⊥) × (l ++ u ++ r Eq.≡ w))

_<ⁱ_ : Str → Str → Type ℓ-zero
u <ⁱ w = ∥ Occ u w ∥₁

isProp<ⁱ : ∀ u w → isProp (u <ⁱ w)
isProp<ⁱ _ _ = PT.isPropPropTrunc

private
  -- an append is empty only if both parts are
  ++nil : ∀ (l r : Str) → l ++ r Eq.≡ [] → (l Eq.≡ []) × (r Eq.≡ [])
  ++nil [] r p = Eq.refl , p
  ++nil (c ∷ l) r p = Empty.rec (¬cons≡nil (Eq.eqToPath p))

  composeOcc : ∀ {u v w} → Occ u v → Occ v w → Occ u w
  composeOcc {u} {v} {w} (l₁ , r₁ , ne₁ , e₁) (l₂ , r₂ , ne₂ , e₂) =
    (l₂ ++ l₁) , (r₁ ++ r₂) , ne , e
    where
      ne : (l₂ ++ l₁) Eq.≡ [] → (r₁ ++ r₂) Eq.≡ [] → ⊥
      ne pl pr =
        ne₂ (++nil l₂ l₁ pl .fst) (++nil r₁ r₂ pr .snd)

      inner : l₁ ++ (u ++ (r₁ ++ r₂)) Eq.≡ v ++ r₂
      inner =
        Eq.ap (l₁ ++_) (Eq.sym (++-assoc-Eq u r₁ r₂))
        Eq.∙ Eq.sym (++-assoc-Eq l₁ (u ++ r₁) r₂)
        Eq.∙ Eq.ap (_++ r₂) e₁

      e : (l₂ ++ l₁) ++ u ++ (r₁ ++ r₂) Eq.≡ w
      e =
        ++-assoc-Eq l₂ l₁ (u ++ (r₁ ++ r₂))
        Eq.∙ Eq.ap (l₂ ++_) inner
        Eq.∙ e₂

trans<ⁱ : ∀ {u v w} → u <ⁱ v → v <ⁱ w → u <ⁱ w
trans<ⁱ = PT.map2 composeOcc

private
  -- a proper infix is strictly shorter
  <ⁱ-len : ∀ {u w} → Occ u w → length u < length w
  <ⁱ-len {u} {w} (l , r , ne , e) =
    subst (length u <_) (cong length (Eq.eqToPath e)) (go l r ne)
    where
      go : ∀ l r → (l Eq.≡ [] → r Eq.≡ [] → ⊥)
        → length u < length (l ++ u ++ r)
      go [] [] ne' = Empty.rec (ne' Eq.refl Eq.refl)
      go [] (c ∷ r') ne' =
        subst (suc (length u) ≤_)
          (sym (length++ u (c ∷ r') ∙ +-suc (length u) (length r')))
          (suc-≤-suc ≤SumLeft)
      go (c ∷ l') r ne' =
        suc-≤-suc
          (subst (length u ≤_)
            (sym (length++ l' (u ++ r) ∙ cong (length l' +_) (length++ u r)))
            (≤-trans (≤SumLeft {n = length u} {k = length r})
                     (≤SumRight {n = length u + length r} {k = length l'})))

len<ⁱ : ∀ {u w} → u <ⁱ w → length u < length w
len<ⁱ = PT.rec isProp≤ <ⁱ-len

wf<ⁱ : WellFounded _<ⁱ_
wf<ⁱ u = fromLen u (<-wellfounded (length u))
  where
    fromLen : ∀ v → Acc _<_ (length v) → Acc _<ⁱ_ v
    fromLen v (acc r) = acc λ x x<v → fromLen x (r (length x) (len<ⁱ x<v))
