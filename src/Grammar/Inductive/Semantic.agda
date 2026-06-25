{- The semantic endofunctor `⟦SPF⟧Pow` on the power category
   `PowerCategory X (|GRAMMAR| ℓX)`, built from a family of strictly-positive
   codes `F : X → SPFunctor X`, together with the cubical-categorical-logic
   algebra notion over it.

   This module sits BELOW `Grammar.Inductive.Indexed`: it does NOT import
   `Indexed` (no `μ`/`rec`). `Indexed` imports THIS module and retypes
   `rec`/`recHomo`/`ind` to consume the c-c-l `AlgebrasCategory ⟦SPF⟧Pow`.

   KEY definitional fact (used pervasively downstream):

     PowerCategory X (|GRAMMAR| ℓX) [ ⟦SPF⟧Pow A , A ]
       = ∀ x → ⟦ F x ⟧ ⟨ A ⟩ ⊢ ⟨ A x ⟩

   i.e. an `⟦SPF⟧Pow`-algebra *structure map* on a carrier `A : X → SetGrammar`
   IS exactly the old hand-rolled `Algebra F (λ x → ⟨ A x ⟩)`, and the
   `AlgStructureOver` displayed coherence is exactly the old `isHomo`. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Inductive.Semantic (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Power
open import Cubical.Categories.Displayed.Instances.Algebras public

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Term.Base Alphabet
open import Term.Category Alphabet

open import Grammar.Inductive.Functor Alphabet public
open import Grammar.Inductive.SetValued Alphabet public

private
  variable ℓX : Level

module _ {X : Type ℓX} (F : X → SPFunctor X) (isSetValF : ∀ x → isSetValued (F x)) where
  open Category
  open Functor

  -- The power category over X: ob = `X → SetGrammar ℓX`, and a morphism
  -- `A → B` is a family `∀ x → ⟨ A x ⟩ ⊢ ⟨ B x ⟩` (definitionally).
  PowerCat : Category (ℓ-max (ℓ-suc ℓX) ℓX) ℓX
  PowerCat = PowerCategory X (|GRAMMAR| ℓX)

  -- object action, packaged pointwise as a SetGrammar.
  ⟦SPF⟧Pow-ob : (X → SetGrammar ℓX) → (X → SetGrammar ℓX)
  ⟦SPF⟧Pow-ob A x .fst = ⟦ F x ⟧ (λ y → A y .fst)
  ⟦SPF⟧Pow-ob A x .snd = isSet⟦F⟧ (F x) (isSetValF x) A

  -- The X-indexed semantic endofunctor.
  ⟦SPF⟧Pow : Functor PowerCat PowerCat
  ⟦SPF⟧Pow .F-ob = ⟦SPF⟧Pow-ob
  ⟦SPF⟧Pow .F-hom {A}{B} ϕ x = map (F x) ϕ
  ⟦SPF⟧Pow .F-id {A} = funExt (λ x → map-id (F x))
  ⟦SPF⟧Pow .F-seq f g = funExt (λ x → map-∘ (F x) g f)

  -- Convenience alias: the c-c-l algebra *structure map* on a carrier `A`.
  -- Definitionally `∀ x → ⟦ F x ⟧ ⟨ A ⟩ ⊢ ⟨ A x ⟩`.
  SPFAlgebra : (X → SetGrammar ℓX) → Type ℓX
  SPFAlgebra A = PowerCat [ Functor.F-ob ⟦SPF⟧Pow A , A ]
