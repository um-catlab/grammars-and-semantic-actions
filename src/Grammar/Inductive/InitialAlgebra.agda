{- `μ F` as a cubical-categorical-logic `InitialAlgebra`, connecting gsa's
   inductive-functor *codes* to upstream *semantic functors*.

   For an index type `X : Type ℓX` and a family of strictly-positive codes
   `F : X → SPFunctor X`, this module builds:

     1. the semantic endofunctor `⟦F⟧Pow` on the power category
        `PowerCategory X (|GRAMMAR| ℓX)` (reused from `Grammar.Inductive.Semantic`);

     2. an `InitialAlgebra ⟦F⟧Pow` whose carrier+structure is `(μ F , λ x → roll)`
        and whose unique homomorphism is `rec` (uniqueness from `ind`).

   The X-indexed notion is the primitive one; the single-sorted case is just its
   `X = Unit*` instance and is not developed separately.

   AUGMENT, not replace: `μ`/`rec`/`roll` keep their definitional reduction
   behaviour; the `InitialAlgebra` witness sits alongside, and its comparison
   maps are *built from* `rec` (see §3).

   NOTE on levels: the codes `F : X → SPFunctor X` only mention `Grammar ℓX`
   / `Type ℓX`, and `μ F x : Grammar ℓX`, so the grammar level is forced to
   coincide with the index level `ℓX`.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Inductive.InitialAlgebra (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Opposite
open import Cubical.Categories.Instances.Power
open import Cubical.Categories.Displayed.Instances.Algebras
  hiding (Algebra)
open import Cubical.Categories.Displayed.Instances.StructureOver
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.Initial

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Inductive.Indexed Alphabet
open import Grammar.Inductive.HLevels Alphabet
open import Grammar.Inductive.Semantic Alphabet
  using (⟦SPF⟧Pow)
open import Term.Base Alphabet
open import Term.Category Alphabet

module Indexed {ℓX} {X : Type ℓX}
  (F : X → SPFunctor X) (isSetValF : ∀ x → isSetValued (F x)) where

  open Category
  open Functor

------------------------------------------------------------------------
-- §1.  The semantic endofunctor of the codes `F`.
------------------------------------------------------------------------

  -- The power category over X: ob = `X → SetGrammar ℓX`, and a morphism
  -- `A → B` is a family `∀ x → ⟨ A x ⟩ ⊢ ⟨ B x ⟩`. Hom-equality is
  -- `funExt` over x (see `Cubical.Categories.Instances.Product`).
  PowerCat : Category (ℓ-max (ℓ-suc ℓX) ℓX) ℓX
  PowerCat = PowerCategory X (|GRAMMAR| ℓX)

  -- The X-indexed semantic endofunctor built from the codes `F`,
  -- reused from `Grammar.Inductive.Semantic` (single source of truth).
  ⟦F⟧Pow : Functor PowerCat PowerCat
  ⟦F⟧Pow = ⟦SPF⟧Pow F isSetValF

------------------------------------------------------------------------
-- §2.  μ F as an InitialAlgebra of ⟦F⟧Pow.
------------------------------------------------------------------------

  private
    AlgCat = ALG ⟦F⟧Pow

  -- carrier object of the initial algebra in PowerCat
  μF-ob : X → SetGrammar ℓX
  μF-ob x .fst = μ F x
  μF-ob x .snd = isSetGrammarμ F isSetValF x

  -- structure map: `λ x → roll`. Its source `λ x → ⟦ F x ⟧ (μ F)` is
  -- `F-ob ⟦F⟧Pow μF-ob` definitionally, so it is exactly an
  -- `⟦F⟧Pow`-algebra structure on `μF-ob`.
  μF-str : PowerCat [ Functor.F-ob ⟦F⟧Pow μF-ob , μF-ob ]
  μF-str x = roll

  μF-alg : Category.ob AlgCat
  μF-alg = μF-ob , μF-str

  -- Building, from any other algebra `(B , β)`, the unique algebra
  -- homomorphism `μF-alg → (B , β)`.  Its underlying family is `rec`.
  module _ (Bβ : Category.ob AlgCat) where
    private
      B : X → SetGrammar ℓX
      B = Bβ .fst
      β : PowerCat [ Functor.F-ob ⟦F⟧Pow B , B ]
      β = Bβ .snd

      -- `β` as a gsa algebra `∀ x → ⟦ F x ⟧ (λ x → ⟨ B x ⟩) ⊢ ⟨ B x ⟩`.
      αB : ∀ x → ⟦ F x ⟧ (λ x → B x .fst) ⊢ B x .fst
      αB = β

    recArrow : PowerCat [ μF-ob , B ]
    recArrow = rec F αB

    -- The displayed coherence (`α ⋆ f ≡ F-hom f ⋆ β`) is `funExt`-over-x
    -- of `recHomo F αB .snd`, which is pointwise `refl`.
    recAlgHom : AlgCat [ μF-alg , Bβ ]
    recAlgHom = recArrow , funExt (λ x → recHomo F αB .snd x)

    -- uniqueness: any algebra hom out of `μF-alg` equals `recAlgHom`.
    -- The displayed coherence is a prop (isSetHom), so it suffices to
    -- compare underlying families, which we do with `ind`.
    recAlgHom-unique : ∀ (gh : AlgCat [ μF-alg , Bβ ]) → recAlgHom ≡ gh
    recAlgHom-unique gh =
      isFaithfulFst (AlgStructureOver ⟦F⟧Pow) μF-alg Bβ recAlgHom gh recArrow≡g
      where
        g : PowerCat [ μF-ob , B ]
        g = gh .fst

        -- `gh`'s coherence read back as a gsa homomorphism property:
        -- `g x ∘g roll ≡ β x ∘g map (F x) g`, i.e. `isHomo αB` at x.
        -- `gh .snd : β ⋆ g ≡ F-hom g ⋆ β'` is `funExt`-over-x of that.
        gHomo : RecHomo F αB
        gHomo .fst = g
        gHomo .snd x = funExt⁻ (gh .snd) x

        recHomo' : RecHomo F αB
        recHomo' = recHomo F αB

        -- `ind` gives equality of the underlying families of the two
        -- homomorphisms out of the initial algebra.
        recArrow≡g : recArrow ≡ g
        recArrow≡g = ind F αB recHomo' gHomo

  -- The `Initial AlgCat` data: object + isInitial.
  μF-isInitial : isInitial AlgCat μF-alg
  μF-isInitial Bβ .fst = recAlgHom Bβ
  μF-isInitial Bβ .snd = recAlgHom-unique Bβ

  μF-Terminal-op : Terminal (AlgCat ^op)
  μF-Terminal-op = μF-alg , μF-isInitial

  -- Initial algebra: carrier `μ F`, structure `λ x → roll`, unique hom
  -- `rec`, uniqueness from `ind`.
  μF-InitialAlgebra : InitialAlgebra ⟦F⟧Pow
  μF-InitialAlgebra = terminalToUniversalElement μF-Terminal-op

------------------------------------------------------------------------
-- §3.  AUGMENT: the abstract comparison maps agree with `rec`.
------------------------------------------------------------------------

  -- The comparison morphism fed into the `InitialAlgebra` is `recAlgHom`,
  -- whose underlying PowerCat-family is *definitionally* `rec F (Bβ .snd)`
  -- (so downstream `rec`/`roll` reductions are untouched).
  ⟦F⟧Pow-recAlgHom-map≡rec : ∀ (Bβ : Category.ob AlgCat)
    → recAlgHom Bβ .fst ≡ rec F (Bβ .snd)
  ⟦F⟧Pow-recAlgHom-map≡rec Bβ = refl

  -- `recAlgHom Bβ` is THE unique algebra homomorphism out of the initial
  -- algebra (uniqueness from `ind`); hence any algebra hom `μF-alg → Bβ`
  -- has underlying family `rec`.
  ⟦F⟧Pow-any-hom-map≡rec : ∀ (Bβ : Category.ob AlgCat)
    (gh : AlgCat [ μF-alg , Bβ ])
    → gh .fst ≡ rec F (Bβ .snd)
  ⟦F⟧Pow-any-hom-map≡rec Bβ gh = cong fst (sym (recAlgHom-unique Bβ gh))
