open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Later.SuffixOrder (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ ; suc ; zero ; _+_)
open import Cubical.Data.Nat.Order.Recursive as NatOrd using (_<_ ; ≤-+k)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_ ; length)
open import Cubical.Data.List.Properties using (isOfHLevelList)
open import Cubical.Data.Empty as Empty
import Cubical.Data.Equality as Eq
open import Cubical.Induction.WellFounded

open import Cubical.Categories.Direct.Base using (WFOrder)
open import String.Base Alphabet using (String ; isSetEqString)
open import Cubical.Data.List.MoreMore using (++-assoc-Eq ; ++-cancelʳEq)

private
  Str : Type ℓ-zero
  Str = String

-- Eq-world strict suffix order: w is a proper suffix of w'.
--
-- The equation `u ++ w ≡ w'` lives in *Eq-world* (`Cubical.Data.Equality`),
-- not as a cubical Path.  This is the crux: `transp`/`subst` over a Path does
-- NOT reduce definitionally (`transpRefl` is only propositional), whereas
-- `Eq.≡` is an inductive identity type and `transp` over it reduces
-- structurally.  c-c-l's abstract Löb (`löbWF`/`down`) `subst`s over the order
-- relation when it composes, so a Path-carrying order wedges on a stuck
-- `transp` the first time the fixpoint is used (mirroring why the recursive,
-- `Unit`/`⊥`-valued ℕ order computes but a Σ-with-Path order does not).
_<ˢ_ : Str → Str → Type ℓ-zero
w <ˢ w' = Σ[ u ∈ Str ] (u Eq.≡ [] → Empty.⊥) × (u ++ w Eq.≡ w')

private
  length++Eq : (xs ys : Str) → length (xs ++ ys) Eq.≡ length xs + length ys
  length++Eq []       ys = Eq.refl
  length++Eq (x ∷ xs) ys = Eq.ap suc (length++Eq xs ys)

  shorter : ∀ (u w : Str) → (u Eq.≡ [] → Empty.⊥) → length w < length u + length w
  shorter []       w ne = Empty.rec (ne Eq.refl)
  shorter (a ∷ u') w _  = ≤-+k {m = 0} {n = length u'} {k = length w} _

<ˢ→length< : ∀ {w w'} → w <ˢ w' → length w < length w'
<ˢ→length< {w} (u , ne , e) =
  Eq.transport (length w <_)
    (Eq.sym (length++Eq u w) Eq.∙ Eq.ap length e)
    (shorter u w ne)

private
  suffixAcc : ∀ w → Acc _<_ (length w) → Acc _<ˢ_ w
  suffixAcc w (acc f) = acc (λ w' r → suffixAcc w' (f (length w') (<ˢ→length< r)))

wf<ˢ : WellFounded _<ˢ_
wf<ˢ w = suffixAcc w (NatOrd.WellFounded.wf-< (length w))

private
  ¬cons≡nil-Eq : ∀ {x : ⟨ Alphabet ⟩} {xs : Str} → x ∷ xs Eq.≡ [] → Empty.⊥
  ¬cons≡nil-Eq ()

  ++≡[]ˡ-Eq : {xs ys : Str} → xs ++ ys Eq.≡ [] → xs Eq.≡ []
  ++≡[]ˡ-Eq {[]}     p = Eq.refl
  ++≡[]ˡ-Eq {x ∷ xs} p = Empty.rec (¬cons≡nil-Eq p)

trans<ˢ : ∀ {w w' w''} → w <ˢ w' → w' <ˢ w'' → w <ˢ w''
trans<ˢ {w} {w'} {w''} (u₁ , ne₁ , e₁) (u₂ , ne₂ , e₂) =
  (u₂ ++ u₁) , ne , eq
  where
    ne : u₂ ++ u₁ Eq.≡ [] → Empty.⊥
    ne p = ne₂ (++≡[]ˡ-Eq p)
    eq : (u₂ ++ u₁) ++ w Eq.≡ w''
    eq = ++-assoc-Eq u₂ u₁ w Eq.∙ Eq.ap (u₂ ++_) e₁ Eq.∙ e₂

-- Only needs to typecheck; never forced during reduction.  The right
-- cancellation is done in Eq-world with gsa's own `++-cancelʳEq` (from
-- `Cubical.Data.List.MoreMore`) and only then converted to a path, so this file no
-- longer depends on c-c-l's (deleted) `Direct.Instances.Suffix`.
isProp<ˢ : ∀ w w' → isProp (w <ˢ w')
isProp<ˢ w w' (u₁ , ne₁ , e₁) (u₂ , ne₂ , e₂) =
  Σ≡Prop
    (λ u → isProp× (isPropΠ (λ _ → Empty.isProp⊥)) (isSetEqString _ _))
    (Eq.eqToPath (++-cancelʳEq w (e₁ Eq.∙ Eq.sym e₂)))

SuffixWFOrder : WFOrder ℓ-zero ℓ-zero
SuffixWFOrder = record
  { D       = Str
  ; isSetD  = isOfHLevelList 0 (Alphabet .snd)
  ; _<_     = _<ˢ_
  ; isProp< = isProp<ˢ
  ; trans<  = λ {a} {b} {c} → trans<ˢ {a} {b} {c}
  ; wf<     = wf<ˢ
  }
