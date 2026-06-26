{- The Lambek implications as genuine adjoints to the tensor.

   For a fixed grammar `A`, we exhibit:

   * `(A ⊗ –)` has a right adjoint `(– ⟜ A)`, witnessed by the currying
     iso `⟜UMP : Iso (A ⊗ B ⊢ C) (B ⊢ C ⟜ A)`.

   * `(– ⊗ A)` has a right adjoint `(A ⊸ –)`, witnessed by the currying
     iso `⊸UMP : Iso (A ⊗ B ⊢ C) (A ⊢ B ⊸ C)`.

   NOTE on orientation.  Although `⟜UMP`/`⊸UMP` are often informally read
   as "(–⊗A) ⊣ (–⟜A)", the *variable* in `⟜UMP` is `B` (the right factor
   of `A ⊗ B`), so the functor whose right adjoint it exhibits is the
   left-tensor `(A ⊗ –)`, with right adjoint `(– ⟜ A)`.  Dually `⊸UMP`
   has variable `A` (the left factor), so it exhibits the right-tensor
   `(– ⊗ A)` with right adjoint `(A ⊸ –)`.  The counit maps are exactly
   `⟜-app : A ⊗ (B ⟜ A) ⊢ B` and `⊸-app : (A ⊸ B) ⊗ A ⊢ B`.

   We package these using c-c-l's
   `Cubical.Categories.Adjoint.UniversalElements`:
     `RightAdjointAt F d = UniversalElement C (RightAdjointProf F ⟅ d ⟆)`
     `RightAdjoint   F   = UniversalElements (RightAdjointProf F)`
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

module Grammar.LinearFunction.Adjoint (Alphabet : hSet ℓ-zero) where

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Adjoint.UniversalElements

open import Grammar.Base Alphabet
open import Grammar.HLevels Alphabet
open import Grammar.LinearProduct Alphabet as LP
open import Grammar.LinearFunction.Base Alphabet
open import Term.Base Alphabet as Term
open import Term.Category Alphabet

private
  variable
    ℓ : Level

module _ (ℓ : Level) (A : SetGrammar ℓ) where
  open Category
  open Functor
  open UniversalElement

  private
    ⟨A⟩ : Grammar ℓ
    ⟨A⟩ = ⟨ A ⟩

  --------------------------------------------------------------------------
  -- The partially-applied tensor functors on |GRAMMAR| ℓ
  --------------------------------------------------------------------------

  -- (A ⊗ –) : |GRAMMAR| → |GRAMMAR|
  A⊗- : Functor (|GRAMMAR| ℓ) (|GRAMMAR| ℓ)
  A⊗- .F-ob B = (⟨A⟩ LP.⊗ ⟨ B ⟩) , isSetGrammar⊗ (A .snd) (B .snd)
  A⊗- .F-hom f = Term.id ,⊗ f
  A⊗- .F-id = id,⊗id≡id
  A⊗- .F-seq f g = sym ⊗-intro⊗-intro

  -- (– ⊗ A) : |GRAMMAR| → |GRAMMAR|
  -⊗A : Functor (|GRAMMAR| ℓ) (|GRAMMAR| ℓ)
  -⊗A .F-ob B = (⟨ B ⟩ LP.⊗ ⟨A⟩) , isSetGrammar⊗ (B .snd) (A .snd)
  -⊗A .F-hom f = f ,⊗ Term.id
  -⊗A .F-id = id,⊗id≡id
  -⊗A .F-seq f g = sym ⊗-intro⊗-intro

  --------------------------------------------------------------------------
  -- (A ⊗ –) ⊣ (– ⟜ A)
  --------------------------------------------------------------------------

  -- The right-adjoint object: d ⟜ A, as a SetGrammar.
  _⟜A : SetGrammar ℓ → SetGrammar ℓ
  d ⟜A = (⟨ d ⟩ ⟜ ⟨A⟩) , isSetGrammar⟜ (d .snd)

  -- The counit / universal element at d is the application map
  --   ⟜-app : A ⊗ (d ⟜ A) ⊢ d
  -- which lives in (RightAdjointProf (A⊗-) ⟅ d ⟆) ⟅ d ⟜A ⟆
  --   = |GRAMMAR| [ A⊗- ⟅ d ⟜A ⟆ , d ] = (A ⊗ (d ⟜ A)) ⊢ d.
  RightAdjoint-⟜ : RightAdjoint (A⊗-)
  RightAdjoint-⟜ d .vertex = d ⟜A
  RightAdjoint-⟜ d .element = ⟜-app
  RightAdjoint-⟜ d .universal c =
    -- The action `element ∘ᴾ⟨P⟩ f` sends f : c ⊢ (d ⟜ A) to
    --   ⟜-app ∘g (id ,⊗ f) = ⟜-intro⁻ f, the inverse of ⟜UMP.
    isoToIsEquiv (invIso (⟜UMP {A = ⟨A⟩} {B = ⟨ c ⟩} {C = ⟨ d ⟩}))

  --------------------------------------------------------------------------
  -- (– ⊗ A) ⊣ (A ⊸ –)
  --------------------------------------------------------------------------

  -- The right-adjoint object: A ⊸ d, as a SetGrammar.
  A⊸_ : SetGrammar ℓ → SetGrammar ℓ
  A⊸ d = (⟨A⟩ ⊸ ⟨ d ⟩) , isSetGrammar⊸ (d .snd)

  -- The counit / universal element at d is the application map
  --   ⊸-app : (A ⊸ d) ⊗ A ⊢ d.
  RightAdjoint-⊸ : RightAdjoint (-⊗A)
  RightAdjoint-⊸ d .vertex = A⊸ d
  RightAdjoint-⊸ d .element = ⊸-app
  RightAdjoint-⊸ d .universal c =
    -- The action sends f : c ⊢ (A ⊸ d) to ⊸-app ∘g (f ,⊗ id) = ⊸-intro⁻ f.
    isoToIsEquiv (invIso (⊸UMP {A = ⟨ c ⟩} {B = ⟨A⟩} {C = ⟨ d ⟩}))
