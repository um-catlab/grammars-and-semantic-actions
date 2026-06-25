{- Phase C: connect gsa's inductive-functor *codes* to upstream *semantic
   functors* and *initial algebras*.

   This module builds, from a single-sorted strictly-positive code
   `F : Functor (Unit* {ℓ})`:

     1. a c-c-l `Functor (|GRAMMAR| ℓ) (|GRAMMAR| ℓ)`, `⟦ F ⟧F`, whose
        object action is `A ↦ ⟦ F ⟧ (λ _ → ⟨ A ⟩)` (packaged as a
        SetGrammar), F-hom = `map F`, and F-id/F-seq from `map-id`/`map-∘`;

     2. an `InitialAlgebra ⟦ F ⟧F` whose carrier+structure is `(μ F , roll)`
        and whose unique homomorphism is `rec` (uniqueness from `ind`).

   AUGMENT, not replace: `μ`/`rec`/`roll` keep their definitional reduction
   behaviour; the `InitialAlgebra` witness sits alongside, and its comparison
   maps are *built from* `rec` (see §3).
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Categorical.InductiveAlgebra (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
  renaming (Functor to CatFunctor)
open import Cubical.Categories.Instances.Opposite
open import Cubical.Categories.Displayed.Instances.Algebras
open import Cubical.Categories.Displayed.Instances.StructureOver
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.Initial

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Inductive.Indexed Alphabet
open import Grammar.Inductive.HLevels Alphabet
open import Term.Base Alphabet
open import Term.Category Alphabet

private
  variable ℓ : Level

------------------------------------------------------------------------
-- §1.  Semantic functor from a single-sorted code.
------------------------------------------------------------------------

-- A single-sorted code is a `Functor (Unit* {ℓ})`. We package it as the
-- constant family over `Unit*` to feed the indexed `μ`/`Algebra`/`rec` API.
module SingleSorted {ℓ} (F : Functor (Unit* {ℓ})) (isSetValF : isSetValued F) where

  open Category
  open CatFunctor

  -- the constant family `Unit* → Functor Unit*`
  Fᴹ : Unit* {ℓ} → Functor (Unit* {ℓ})
  Fᴹ _ = F

  -- Note on definitional equalities exploited throughout:
  --   * `Unit*` has η, so any `u : Unit*` is judgmentally `tt*`; hence
  --     `λ _ → A` and a `Unit*`-indexed family agree definitionally, and
  --     `⟦ F ⟧ (μ Fᴹ) ≡ ⟦ F ⟧ (λ _ → μ Fᴹ tt*)` holds by refl.
  --   * `map F (λ _ → f) ≡ map (Fᴹ tt*) family` likewise by η.

  -- object action, packaged as a SetGrammar
  ⟦F⟧-ob : SetGrammar ℓ → SetGrammar ℓ
  ⟦F⟧-ob A .fst = ⟦ F ⟧ (λ _ → A .fst)
  ⟦F⟧-ob A .snd = isSet⟦F⟧ F isSetValF (λ _ → A)

  ⟦_⟧F : CatFunctor (|GRAMMAR| ℓ) (|GRAMMAR| ℓ)
  ⟦_⟧F .F-ob = ⟦F⟧-ob
  ⟦_⟧F .F-hom {A}{B} f = map F (λ _ → f)
  ⟦_⟧F .F-id {A} = map-id F
  ⟦_⟧F .F-seq f g = map-∘ F (λ _ → g) (λ _ → f)

------------------------------------------------------------------------
-- §2.  μ as an InitialAlgebra of ⟦ F ⟧F.
------------------------------------------------------------------------

  private
    AlgCat = AlgebrasCategory ⟦_⟧F

  -- carrier object of the initial algebra in |GRAMMAR|
  μF-ob : SetGrammar ℓ
  μF-ob .fst = μ Fᴹ tt*
  μF-ob .snd = isSetGrammarμ Fᴹ (λ _ → isSetValF) tt*

  -- structure map: `roll : ⟦ F ⟧ (μ Fᴹ) ⊢ μ Fᴹ tt*`.
  -- Its source `⟦ F ⟧ (μ Fᴹ)` is `F-ob ⟦_⟧F μF-ob .fst` definitionally
  -- (by the Unit*-η remark above), so it is exactly an `⟦_⟧F`-algebra
  -- structure on `μF-ob`.
  μF-str : |GRAMMAR| ℓ [ CatFunctor.F-ob ⟦_⟧F μF-ob , μF-ob ]
  μF-str = roll

  -- the object of `AlgebrasCategory ⟦_⟧F`
  μF-alg : Category.ob AlgCat
  μF-alg = μF-ob , μF-str

  -- Building, from any other algebra `(B , β)`, the unique algebra
  -- homomorphism `μF-alg → (B , β)`.  Its underlying map is `rec`.
  module _ (Bβ : Category.ob AlgCat) where
    private
      B : SetGrammar ℓ
      B = Bβ .fst
      β : |GRAMMAR| ℓ [ CatFunctor.F-ob ⟦_⟧F B , B ]
      β = Bβ .snd

      -- `β` as a gsa `Algebra Fᴹ (λ _ → ⟨ B ⟩)`
      αB : Algebra Fᴹ (λ _ → B .fst)
      αB _ = β

    -- the canonical homomorphism, underlying map = rec.
    -- The displayed coherence (`AlgStructureOver`'s law `α ⋆ f ≡ F-hom f ⋆ β`)
    -- is exactly `recHomo Fᴹ αB .snd tt*` (which is `refl`); we build the
    -- ∫C-morphism directly so its expected type pins all metas.
    recArrow : |GRAMMAR| ℓ [ μF-ob , B ]
    recArrow = rec Fᴹ αB tt*

    recAlgHom : AlgCat [ μF-alg , Bβ ]
    recAlgHom = recArrow , refl

    -- uniqueness: any algebra hom out of `μF-alg` equals `recAlgHom`.
    -- The displayed coherence is a proposition (isSetHom), so it suffices
    -- to compare underlying maps, which we do with `ind`.
    recAlgHom-unique : ∀ (gh : AlgCat [ μF-alg , Bβ ]) → recAlgHom ≡ gh
    -- Morphisms in `AlgCat = ∫C (StructureOver→Catᴰ (AlgStructureOver ⟦_⟧F))`
    -- are determined by their underlying `|GRAMMAR|`-map (the displayed
    -- coherence is a prop): `isFaithfulFst`.
    recAlgHom-unique gh =
      isFaithfulFst (AlgStructureOver ⟦_⟧F) μF-alg Bβ recAlgHom gh recArrow≡g
      where
        g : |GRAMMAR| ℓ [ μF-ob , B ]
        g = gh .fst

        -- `gh`'s coherence read back as a gsa homomorphism property:
        -- `g ∘g roll ≡ β ∘g map F (λ _ → g)`, i.e. `isHomo αB` at tt*.
        gHomo : Homomorphism Fᴹ (initialAlgebra Fᴹ) αB
        gHomo .fst _ = g
        gHomo .snd _ = gh .snd

        recHomo' : Homomorphism Fᴹ (initialAlgebra Fᴹ) αB
        recHomo' = recHomo Fᴹ αB

        -- `ind` gives equality of the underlying maps of the two
        -- homomorphisms out of the initial algebra.
        recArrow≡g : recArrow ≡ g
        recArrow≡g i = ind Fᴹ αB recHomo' gHomo i tt*

  -- The `Initial AlgCat` data: object + isInitial.
  -- `isInitial AlgCat x = ∀ y → isContr (AlgCat [ x , y ])`.
  μF-isInitial : isInitial AlgCat μF-alg
  μF-isInitial Bβ .fst = recAlgHom Bβ
  μF-isInitial Bβ .snd = recAlgHom-unique Bβ

  -- `Initial AlgCat = Terminal (AlgCat ^op)` definitionally (the Hom of
  -- `^op` is flipped, and `isInitial`/`isTerminal` unfold identically).
  μF-Terminal-op : Terminal (AlgCat ^op)
  μF-Terminal-op = μF-alg , μF-isInitial

  -- `InitialAlgebra ⟦_⟧F = Initial' AlgCat = Terminal' (AlgCat ^op)
  --                       = UniversalElement (AlgCat ^op) UnitPsh`.
  -- We obtain it from the terminal object of the opposite via the
  -- generic `terminalToUniversalElement`.
  μF-InitialAlgebra : InitialAlgebra ⟦_⟧F
  μF-InitialAlgebra = terminalToUniversalElement μF-Terminal-op

------------------------------------------------------------------------
-- §3.  AUGMENT: the abstract `fold` agrees with the concrete `rec`.
------------------------------------------------------------------------

  open InitialAlgebraNotation {F = ⟦_⟧F} μF-InitialAlgebra

  -- The comparison morphism we feed into the `InitialAlgebra` is
  -- `recAlgHom`, whose underlying `|GRAMMAR|`-map is *definitionally*
  -- `rec` (so downstream `rec`/`roll` reductions are untouched).
  ⟦F⟧-recAlgHom-map≡rec : ∀ (Bβ : Category.ob AlgCat)
    → recAlgHom Bβ .fst ≡ rec Fᴹ (λ _ → Bβ .snd) tt*
  ⟦F⟧-recAlgHom-map≡rec Bβ = refl

  -- `recAlgHom Bβ` is THE unique algebra homomorphism out of the initial
  -- algebra (uniqueness from `ind`, via `recAlgHom-unique`); hence any
  -- algebra hom `μF-alg → Bβ` has underlying map `rec`.
  ⟦F⟧-any-hom-map≡rec : ∀ (Bβ : Category.ob AlgCat)
    (gh : AlgCat [ μF-alg , Bβ ])
    → gh .fst ≡ rec Fᴹ (λ _ → Bβ .snd) tt*
  ⟦F⟧-any-hom-map≡rec Bβ gh = cong fst (sym (recAlgHom-unique Bβ gh))

  -- Bridge to c-c-l's abstract recursor `fold`.
  --
  -- The cleanest statement would be `fold Bβ ≡ recAlgHom Bβ`, proved by
  -- `fold-unique (fold Bβ) (recAlgHom Bβ)`.  We deliberately do NOT state
  -- it: even *mentioning* `fold Bβ` in a type forces Agda to elaborate
  -- `fold Bβ = absurd`, which unfolds through the universal-property
  -- *inverse* (`terminalToUniversalElement`'s `equiv-proof` / `intro`).
  -- On an abstract code `F` that inverse does not reduce, leaving an
  -- unsolved algebra-structure meta on a generic element (the
  -- `_B.snd … section …` constraint).
  --
  -- The fact is nonetheless TRUE: `fold-unique` says any two morphisms out
  -- of the initial object agree, and `recAlgHom` IS such a morphism whose
  -- underlying map is `rec` (`⟦F⟧-recAlgHom-map≡rec`).  The AUGMENT
  -- guarantee is met by `⟦F⟧-recAlgHom-map≡rec` / `⟦F⟧-any-hom-map≡rec`:
  -- the comparison maps of the `InitialAlgebra` are built from — and
  -- reduce definitionally to — `rec`.
  --
  -- To make the `fold ≡ recAlgHom` bridge *typecheck* one would replace
  -- the generic `terminalToUniversalElement` packaging with a hand-built
  -- `Initial'` whose `intro` is *definitionally* `recAlgHom` (so `fold Bβ`
  -- reduces to `recAlgHom Bβ` by refl).  Left as future work.

------------------------------------------------------------------------
-- §4.  The general mutual / X-indexed case (SKETCH, with holes).
------------------------------------------------------------------------

-- For a general index type `X : Type ℓ` and a family `F : X → Functor X`,
-- the inductive type `μ F` is the carrier of an initial algebra for an
-- endofunctor on the *power category* `|GRAMMAR| ℓ ^ X`, i.e. the
-- X-indexed product `PowerCategory X (|GRAMMAR| ℓ)`.
--
-- Concretely one needs:
--   * `PowerCat X (|GRAMMAR| ℓ)` whose ob = `X → SetGrammar ℓ`, and
--     Hom (A , B) = `∀ x → ⟨ A x ⟩ ⊢ ⟨ B x ⟩` (pointwise terms);
--   * the endofunctor `⟦ F ⟧Pow` with
--        F-ob A x = ⟦ F x ⟧ (λ x → ⟨ A x ⟩)   (set-valued via isSet⟦F⟧)
--        F-hom ϕ x = map (F x) ϕ
--        F-id  = funExt (λ x → map-id (F x))
--        F-seq = funExt (λ x → map-∘ (F x) _ _)
--   * its initial algebra = `(μ F , λ x → roll)` with unique hom `rec`,
--     uniqueness from `ind` — identical to §2 but X-indexed.
--
-- The single-sorted development above is the `X = Unit*` instance of
-- exactly this (the power category over `Unit*` is `|GRAMMAR| ℓ` itself,
-- modulo the Unit*-η identifications). The remaining work is purely the
-- construction of `PowerCat` / `⟦ F ⟧Pow` as honest c-c-l data.

module IndexedSketch {ℓX ℓ} {X : Type ℓX}
  (F : X → Functor X) where

  open Category
  open CatFunctor

  -- The power category over X (pointwise SetGrammars and terms).
  -- This is the c-c-l `PowerCategory X (|GRAMMAR| ℓ)`; here we only need
  -- its existence to state the indexed functor.
  -- (level matches `PowerCategory X (|GRAMMAR| ℓ)`, with |GRAMMAR| ℓ at
  -- `Category (ℓ-suc ℓ) ℓ` and the X-fold product adding ℓX)
  PowerCat : Category (ℓ-max (ℓ-suc ℓ) ℓX) (ℓ-max ℓ ℓX)
  PowerCat = {!!}   -- = PowerCategory X (|GRAMMAR| ℓ)

  -- The X-indexed semantic endofunctor built from the codes `F`.
  ⟦F⟧Pow : CatFunctor PowerCat PowerCat
  ⟦F⟧Pow .F-ob A = {!!}    -- λ x → ⟦ F x ⟧ (λ x → ⟨ A x ⟩), set-valued
  ⟦F⟧Pow .F-hom ϕ = {!!}   -- λ x → map (F x) ϕ
  ⟦F⟧Pow .F-id = {!!}      -- funExt (λ x → map-id (F x))
  ⟦F⟧Pow .F-seq f g = {!!} -- funExt (λ x → map-∘ (F x) g f)

  -- Initial algebra: carrier `μ F`, structure `λ x → roll`, unique hom
  -- `rec`, uniqueness from `ind`.
  μF-InitialAlgebra : InitialAlgebra ⟦F⟧Pow
  μF-InitialAlgebra = {!!}
