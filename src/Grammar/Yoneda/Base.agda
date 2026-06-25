{-
  Yoneda-slice: the single, reusable "name the string" primitive.

  The representable grammar ⌈ w ⌉ is the Yoneda embedding of the
  discrete category String.  Slicing any grammar D by ⌈ w ⌉ collapses
  it to its *value at w*, tagged onto the canonical ⌈ w ⌉ witness:

      D & ⌈ w ⌉  ≅  ⊕[ _ ∈ D w ] ⌈ w ⌉

  This is Axiom A (Yoneda / representability) in iso form.  Everything
  the External.String / SplittingTrichotomy layer proves by hand via
  Splitting surgery + `subst`/`Eq.transport` is meant to factor through
  this one lemma:  to reason about ⊗/& over a *named* string you slice,
  land in plain `String`/`++` data, and transport back.

  The forward map is the only place we touch the model (one `_&_`
  unfold); the inverse is `pick-parse` (already the Yoneda map), and the
  round-trips are just cancellation of `Eq.transport`.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Yoneda.Base (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Grammar.Base Alphabet
open import Grammar.String.Base Alphabet
open import Grammar.Sum.Base Alphabet
open import Grammar.Product.Binary.AsPrimitive.Base Alphabet
open import Grammar.Equivalence.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓD : Level
    w : String
    D : Grammar ℓD

open StrongEquivalence

-- Cancellation of `Eq.transport` along an Eq-path and its symmetric.
-- Both hold by Eq.J: along `Eq.refl` transport is definitionally id.
Eq-transport-cancel : ∀ {w'} → (e : w Eq.≡ w') → (d : D w')
  → Eq.transport D e (Eq.transport D (Eq.sym e) d) ≡ d
Eq-transport-cancel {D = D} e d =
  Eq.J (λ w'' e'' → (d'' : D w'') → Eq.transport D e'' (Eq.transport D (Eq.sym e'') d'') ≡ d'')
       (λ _ → refl) e d

Eq-transport-cancel' : ∀ {w'} → (e : w Eq.≡ w') → (d : D w)
  → Eq.transport D (Eq.sym e) (Eq.transport D e d) ≡ d
Eq-transport-cancel' {D = D} e d =
  Eq.J (λ _ e'' → Eq.transport D (Eq.sym e'') (Eq.transport D e'' d) ≡ d)
       refl e

module _ (D : Grammar ℓD) (w : String) where

  opaque
    unfolding _&_ &-intro
    -- forward: read the string off the ⌈ w ⌉ witness, transport the
    -- D-parse back to its home fiber D w.
    slice-fun : (D & ⌈ w ⌉) ⊢ ⊕[ _ ∈ D w ] ⌈ w ⌉
    slice-fun w' (d , p) =
      Eq.transport D (Eq.sym (uniquely-supported-⌈⌉Eq w w' p)) d , p

    -- inverse: pick-parse is exactly the Yoneda map A w → (⌈ w ⌉ ⊢ A).
    slice-inv : (⊕[ _ ∈ D w ] ⌈ w ⌉) ⊢ D & ⌈ w ⌉
    slice-inv = ⊕ᴰ-elim (λ d → pick-parse w D d ,& id)

    slice-sec : slice-fun ∘g slice-inv ≡ id
    slice-sec = funExt λ w' → funExt λ (d , p) →
      ΣPathP (Eq-transport-cancel' (uniquely-supported-⌈⌉Eq w w' p) d , refl)

    slice-ret : slice-inv ∘g slice-fun ≡ id
    slice-ret = funExt λ w' → funExt λ (d , p) →
      ΣPathP (Eq-transport-cancel (uniquely-supported-⌈⌉Eq w w' p) d , refl)

  slice≅ : (D & ⌈ w ⌉) ≅ (⊕[ _ ∈ D w ] ⌈ w ⌉)
  slice≅ .fun = slice-fun
  slice≅ .inv = slice-inv
  slice≅ .sec = slice-sec
  slice≅ .ret = slice-ret
