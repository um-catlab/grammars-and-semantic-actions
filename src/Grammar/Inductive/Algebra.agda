{- The public, *semantic* recursor interface for indexed inductives.

   This module ADDS, alongside the computational `rec`/`ind`/`recHomo`
   from `Grammar.Inductive.Indexed`, the cubical-categorical-logic-flavoured
   versions typed over the semantic endofunctor `⟦SPF⟧Pow` and its
   `AlgebrasCategory`.

   Carriers are `SetGrammar`s; an algebra structure map is an
   `SPFAlgebra A` (defeq to the old `Algebra F (λ x → ⟨ A x ⟩)`), and
   an algebra homomorphism is a morphism of `AlgebrasCategory ⟦SPF⟧Pow`.

   Everything here delegates to the computational `rec`/`ind` (whose
   underlying maps are definitionally equal), so `rec`/`roll` reductions
   are untouched. -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Inductive.Algebra (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Instances.Algebras
  hiding (Algebra)

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Inductive.Functor Alphabet using (SPFunctor ; map)
open import Grammar.Inductive.Indexed Alphabet using (μ ; rec ; roll)
open import Grammar.Inductive.HLevels Alphabet using (isSetGrammarμ)
open import Grammar.Inductive.Semantic Alphabet
  using (⟦SPF⟧Pow ; SPFAlgebra ; isSetValued)
open import Grammar.Equalizer.Base Alphabet
open import Grammar.Categorical.InductiveAlgebra Alphabet as IA
open import Term.Base Alphabet
open import Term.Category Alphabet

private
  variable ℓX : Level

module _ {X : Type ℓX}
  (F : X → SPFunctor X) (isSetValF : ∀ x → isSetValued (F x)) where

  open IA.Indexed F isSetValF
    using (μF-ob ; μF-str ; μF-alg ; recArrow ; recAlgHom ; recAlgHom-unique
          ; μF-isInitial)

  -- The semantic algebra category for the codes `F`.
  AlgCat : Category (ℓ-max (ℓ-suc ℓX) ℓX) ℓX
  AlgCat = AlgebrasCategory (⟦SPF⟧Pow F isSetValF)

  -- An object of `AlgCat`: a `SetGrammar` carrier + structure map.
  AlgOb : Type (ℓ-max (ℓ-suc ℓX) ℓX)
  AlgOb = Category.ob AlgCat

  -- Package a carrier `A` and `SPFAlgebra A` as an `AlgCat` object.
  mkAlg : (A : X → SetGrammar ℓX) → SPFAlgebra F isSetValF A → AlgOb
  mkAlg A α = A , α

  -- The initial algebra `(μ F , roll)`.
  initialAlgS : AlgOb
  initialAlgS = μF-alg

  -- The structural recursor, semantic packaging. Underlying map = `rec`.
  recS : (A : X → SetGrammar ℓX) → SPFAlgebra F isSetValF A
       → ∀ x → μ F x ⊢ ⟨ A x ⟩
  recS A α = rec F α

  -- The canonical algebra homomorphism out of the initial algebra,
  -- underlying map = `rec`.
  recHomoS : (Bβ : AlgOb) → AlgCat [ initialAlgS , Bβ ]
  recHomoS = recAlgHom

  -- Composition / identity of algebra homomorphisms come from `AlgCat`.
  idHomoS : (Bβ : AlgOb) → AlgCat [ Bβ , Bβ ]
  idHomoS Bβ = Category.id AlgCat {x = Bβ}

  compHomoS : (Aα Bβ Cγ : AlgOb)
    → AlgCat [ Bβ , Cγ ] → AlgCat [ Aα , Bβ ] → AlgCat [ Aα , Cγ ]
  compHomoS Aα Bβ Cγ g h = Category._⋆_ AlgCat {x = Aα} {y = Bβ} {z = Cγ} h g

  -- Uniqueness: any two algebra homs out of the initial algebra agree.
  indS : (Bβ : AlgOb) (ϕ ϕ' : AlgCat [ initialAlgS , Bβ ])
    → ϕ .fst ≡ ϕ' .fst
  indS Bβ ϕ ϕ' i =
    cong fst (sym (recAlgHom-unique Bβ ϕ) ∙ recAlgHom-unique Bβ ϕ') i

  indS' : (Bβ : AlgOb) (ϕ ϕ' : AlgCat [ initialAlgS , Bβ ])
    → ∀ x → ϕ .fst x ≡ ϕ' .fst x
  indS' Bβ ϕ ϕ' = funExt⁻ (indS Bβ ϕ ϕ')

  -- Any algebra endo-hom on the initial algebra is the identity.
  ind-idS : (ϕ : AlgCat [ initialAlgS , initialAlgS ]) → ϕ .fst ≡ idHomoS initialAlgS .fst
  ind-idS ϕ = indS initialAlgS ϕ (idHomoS initialAlgS)

  ind-id'S : (ϕ : AlgCat [ initialAlgS , initialAlgS ]) → ∀ x → ϕ .fst x ≡ id
  ind-id'S ϕ x = funExt⁻ (ind-idS ϕ) x

  -- Equalizer induction, semantic form: two maps `μ F x ⊢ ⟨ A x ⟩` that
  -- agree after `roll`-ing (modulo the equalizer's π) are equal.  This is
  -- the c-c-l-flavoured replacement for `equalizer-ind`; carriers are
  -- `SetGrammar`s and the uniqueness comes from `ind-id'S`.
  module _ (A : X → SetGrammar ℓX)
    (e e' : ∀ (x : X) → μ F x ⊢ ⟨ A x ⟩)
    (pf : ∀ (x : X) →
      e  x ∘g roll ∘g map (F x) (λ x' → eq-π (e x') (e' x')) ≡
      e' x ∘g roll ∘g map (F x) (λ x' → eq-π (e x') (e' x'))) where

    private
      EqCarrier : X → SetGrammar ℓX
      EqCarrier x .fst = equalizer (e x) (e' x)
      EqCarrier x .snd =
        isSetGrammarEqualizer (e x) (e' x)
          (isSetGrammarμ F isSetValF x) (A x .snd)

      equalizer-ind-algS : SPFAlgebra F isSetValF EqCarrier
      equalizer-ind-algS x =
        eq-intro (e x) (e' x)
          (roll ∘g map (F x) (λ x' → eq-π (e x') (e' x')))
          (pf x)

      EqAlg : AlgOb
      EqAlg = mkAlg EqCarrier equalizer-ind-algS

      opaque
        unfolding eq-π eq-intro
        eq-π-is-homo :
          ∀ x →
          eq-π (e x) (e' x) ∘g equalizer-ind-algS x ≡
            roll ∘g map (F x) (λ x' → eq-π (e x') (e' x'))
        eq-π-is-homo x = refl

      eqπHomo : AlgCat [ EqAlg , initialAlgS ]
      eqπHomo .fst x = eq-π (e x) (e' x)
      eqπHomo .snd = funExt (λ x → eq-π-is-homo x)

    equalizer-indS : ∀ (x : X) → e x ≡ e' x
    equalizer-indS x =
      equalizer-section (e x) (e' x)
        (recS EqCarrier equalizer-ind-algS x)
        (ind-id'S
          (compHomoS initialAlgS EqAlg initialAlgS eqπHomo (recHomoS EqAlg))
          x)
