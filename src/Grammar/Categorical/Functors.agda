{- Semantic functors, in use.

   Two things this module exhibits:
   (1) every strictly-positive *code* `SPFunctor` yields an honest categorical
       `Functor` on the category of grammars `|GRAMMAR|` — its action is the
       interpretation `⟦_⟧` and the functorial `map`.  (Its initial algebra is
       the inductive grammar `μ`; see Grammar.Categorical.InductiveAlgebra.)
   (2) the grammar type-constructors `_⊗_`, `_⊕_`, `_&_` are (bi)functors on
       `|GRAMMAR|`.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Categorical.Functors (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Unit
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Instances.BinProduct using (_×C_)

open import Grammar Alphabet
open import Grammar.HLevels.Base Alphabet
open import Term.Category Alphabet
open import Term Alphabet

private
  variable
    ℓ : Level

open Functor

------------------------------------------------------------------------
-- (1) A strictly-positive code is a semantic functor.
--
-- From a single-sorted code `F : SPFunctor Unit*` (set-valued) we build the
-- endofunctor on `|GRAMMAR|` whose object action is `A ↦ ⟦ F ⟧ A`, morphism
-- action is `map F`, and whose functor laws are exactly `map-id` / `map-∘`.
------------------------------------------------------------------------

SPF→Functor : (F : SPFunctor (Unit* {ℓ})) → isSetValued F
            → Functor (|GRAMMAR| ℓ) (|GRAMMAR| ℓ)
SPF→Functor F isSetValF .F-ob A =
  ⟦ F ⟧ (λ _ → A .fst) , isSet⟦F⟧ F isSetValF (λ _ → A)
SPF→Functor F isSetValF .F-hom f       = map F (λ _ → f)
SPF→Functor F isSetValF .F-id          = map-id F
SPF→Functor F isSetValF .F-seq f g     = map-∘ F (λ _ → g) (λ _ → f)

------------------------------------------------------------------------
-- (2) The binary type-constructors are bifunctors on |GRAMMAR|.
------------------------------------------------------------------------

-- The tensor is already a bifunctor: it is the monoidal product of `GRAMMAR`.
⊗Bifunctor : Functor (|GRAMMAR| ℓ ×C |GRAMMAR| ℓ) (|GRAMMAR| ℓ)
⊗Bifunctor {ℓ} = MonoidalCategory.─⊗─ (GRAMMAR ℓ)

-- The coproduct is a bifunctor (functorial action `_,⊕p_`).
⊕Bifunctor : Functor (|GRAMMAR| ℓ ×C |GRAMMAR| ℓ) (|GRAMMAR| ℓ)
⊕Bifunctor .F-ob (A , B) = (A .fst ⊕ B .fst) , isSetGrammar⊕ (A .snd) (B .snd)
⊕Bifunctor .F-hom (f , g) = f ,⊕p g
⊕Bifunctor .F-id          = id,⊕id≡id
⊕Bifunctor .F-seq (f , g) (f' , g') = sym ⊕p-seq

-- The cartesian product `_&_` is a bifunctor in exactly the same way
-- (functorial action `_,&p_`), and the additive units `⊤`/`⊥` are the
-- terminal/initial objects (see Grammar.Categorical.UniversalProperties);
-- `_⊸_`/`_⟜_` are the right adjoints to `(_⊗ A)`/`(A ⊗_)`
-- (Grammar.Categorical.Adjoints).
