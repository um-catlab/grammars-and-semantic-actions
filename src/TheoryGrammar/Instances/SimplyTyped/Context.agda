{-
  Contexts, as grammars over names.

  `Lookup Γ A` is "this name is bound to A in Γ", built from `⌈ n ⌉`,
  `&`, `⊕` and `¬G` -- the later binding carries a REFUTATION of the
  earlier name, which is what makes shadowing deterministic and is
  therefore what `lookupUnique` needs.

  `Look Γ = ⊕ᴰ Ty (Lookup Γ)` is the synthesis judgment for names: it is
  the same `⊕ᴰ`-over-types shape the term judgment will have, one level
  down, and the same two facts are proved about it -- it is decidable,
  and its index is unique.

  Everything here is a composite; `dec-⌈⌉ⁿ` is the only place `Discrete
  Name` is used, and it is used to BUILD an internal map.
-}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.SimplyTyped.Context where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (_×_; _,_)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Unit
open import Cubical.Data.Empty as E using (⊥)
open import Cubical.Relation.Nullary.Base using (yes; no; Discrete)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Decidable
open import TheoryGrammar.Instances.SimplyTyped.Signature
open import TheoryGrammar.Instances.SimplyTyped.Substrate
open import TheoryGrammar.Instances.SimplyTyped.Base
open import TheoryGrammar.Instances.SimplyTyped.Readable
open import TheoryGrammar.Instances.SimplyTyped.Types

module StContext (Name : Type₀) (_≟_ : Discrete Name) where

  open StBase Name
  open StReadable Name
  open StTypes Name

  Ctx : Type₀
  Ctx = List (Name × Ty)

  -- The ONE place `Discrete Name` is used, and it builds an internal map.
  dec-⌈⌉ⁿ : (m : Name) → ⊤G ⊢ Dec⟨ Nm m ⟩
  dec-⌈⌉ⁿ m n _ with n ≟ m
  ... | yes p = dec-yes (Nm m) n (Eq.pathToEq p)
  ... | no ¬p = dec-no  (Nm m) n λ e → E.rec (¬p (Eq.eqToPath e))

  kty-refl : {s : TSort} (T : Ty) → ⊤G {s} ⊢ Kty T T
  kty-refl T _ _ = tyEq-refl T

  kty-glue : {s : TSort} (A B T : Ty) → (Kty {s} A T & Kty {s} B T) ⊢ Kty A B
  kty-glue A B T _ (e , f) = tyEq-trans A T B e (tyEq-sym B T f)

  -- ================================================================
  -- The two judgments about names.
  -- ================================================================

  Lookup : Ctx → Ty → NmG
  Lookup []            A = ⊥G
  Lookup ((n , T) ∷ Γ) A = (Nm n & Kty A T) ⊕ (¬G Nm n & Lookup Γ A)

  Look : Ctx → NmG
  Look Γ = ⊕ᴰ Ty (Lookup Γ)

  look-nil : Look [] ⊢ ⊥G
  look-nil = ⊕ᴰ-E λ _ → idg

  -- one step of `Look`, respelled without the ⊕ᴰ.  Both directions are
  -- composites: `⊕ᴰ-&-in` moves the index out of a conjunct.
  look-out : (n : Name) (T : Ty) (Γ : Ctx)
           → Look ((n , T) ∷ Γ) ⊢ (Nm n ⊕ (¬G Nm n & Look Γ))
  look-out n T Γ = ⊕ᴰ-E λ A →
    ⊕-E (⊕-I₁ ∘g &-E₁)
        (⊕-I₂ ∘g &-I &-E₁ (⊕ᴰ-I Ty {A = Lookup Γ} A ∘g &-E₂))

  look-in : (n : Name) (T : Ty) (Γ : Ctx)
          → (Nm n ⊕ (¬G Nm n & Look Γ)) ⊢ Look ((n , T) ∷ Γ)
  look-in n T Γ =
    ⊕-E (⊕ᴰ-I Ty {A = Lookup ((n , T) ∷ Γ)} T
         ∘g (⊕-I₁ ∘g &-I idg (kty-refl T ∘g ⊤-I)))
        (⊕ᴰ-E (λ A → ⊕ᴰ-I Ty {A = Lookup ((n , T) ∷ Γ)} A ∘g ⊕-I₂)
         ∘g ⊕ᴰ-&-in Ty)

  -- ================================================================
  -- Decidable, by induction on the context.
  -- ================================================================

  dec-Look : (Γ : Ctx) → ⊤G ⊢ Dec⟨ Look Γ ⟩
  dec-Look [] = dec-no (Look []) ∘g ⇒-I (look-nil ∘g &-E₂)
  dec-Look ((n , T) ∷ Γ) =
      dec-map (Nm n ⊕ (¬G Nm n & Look Γ)) (Look ((n , T) ∷ Γ))
              (look-in n T Γ) (look-out n T Γ)
    ∘g dec-⊕ (Nm n) (¬G Nm n & Look Γ)
    ∘g &-I (dec-⌈⌉ⁿ n)
           (dec-& (¬G Nm n) (Look Γ)
            ∘g &-I (dec-¬ (Nm n) ∘g dec-⌈⌉ⁿ n) (dec-Look Γ))

  -- ================================================================
  -- SUBSINGLETON: the index of `Look Γ` is unique.  This is the
  -- name-level rehearsal of the question the term judgment asks.
  -- ================================================================

  lookupUnique : (Γ : Ctx) (A B : Ty) → (Lookup Γ A & Lookup Γ B) ⊢ Kty A B
  lookupUnique []            A B = ⊥-E ∘g &-E₁
  lookupUnique ((n , T) ∷ Γ) A B =
    ⊕-E (⊕-E (kty-glue A B T ∘g &-I (&-E₂ ∘g &-E₁) (&-E₂ ∘g &-E₂))
             (⊥-E ∘g contra ∘g &-I (&-E₁ ∘g &-E₁) (&-E₁ ∘g &-E₂)))
        (⊕-E (⊥-E ∘g contra ∘g &-I (&-E₁ ∘g &-E₂) (&-E₁ ∘g &-E₁))
             (lookupUnique Γ A B ∘g &-I (&-E₂ ∘g &-E₁) (&-E₂ ∘g &-E₂)))
    ∘g dist&₂
