{- ν F as a c-c-l `TerminalCoalgebra` — the dual of `μ` as an `InitialAlgebra`
   (`Grammar.Inductive.InitialAlgebra`).

   c-c-l defines `TerminalCoalgebra F = InitialAlgebra (F ^opF)`
   (`Cubical.Categories.Displayed.Instances.Coalgebras`), i.e. the terminal
   coalgebra of `F` is the initial algebra of `F` on the opposite category.  So
   we build, for the X-indexed semantic endofunctor `⟦F⟧Pow` on the power
   category, the initial algebra of `G = ⟦F⟧Pow ^opF`:

     * carrier      `ν F`            (set-valued via `isSetGrammarν`);
     * structure    `finalCoalgebra` (= `unroll`), a map νF → ⟦F⟧Pow νF, which is
                    an algebra structure for `G` on `PowerCat ^op`;
     * unique hom   `corec`, uniqueness from `coind`.

   AUGMENT, not replace: `corec`/`coind`/`unroll` keep their definitional
   behaviour; the `TerminalCoalgebra` witness sits alongside, its comparison map
   built from — and reducing to — `corec`.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Coinductive.TerminalCoalgebra (Alphabet : hSet ℓ-zero) where

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Opposite
open import Cubical.Categories.Instances.Power
open import Cubical.Categories.Displayed.Instances.Algebras
  hiding (Algebra)
open import Cubical.Categories.Displayed.Instances.StructureOver
open import Cubical.Categories.Displayed.Instances.Coalgebras
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.Initial

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Coinductive.Indexed Alphabet
open import Grammar.Coinductive.HLevels Alphabet using (isSetGrammarν)
open import Grammar.Inductive.Semantic Alphabet using (⟦SPF⟧Pow ; isSetValued)
open import Term.Base Alphabet
open import Term.Category Alphabet

private
  variable ℓX : Level

module _ {X : Type ℓX}
  (F : X → SPFunctor X) (isSetValF : ∀ x → isSetValued (F x)) where

  open Category
  open Functor

  PowerCat : Category (ℓ-max (ℓ-suc ℓX) ℓX) ℓX
  PowerCat = PowerCategory X (|GRAMMAR| ℓX)

  ⟦F⟧Pow : Functor PowerCat PowerCat
  ⟦F⟧Pow = ⟦SPF⟧Pow F isSetValF

  -- The functor whose INITIAL ALGEBRA is the terminal `⟦F⟧Pow`-coalgebra.
  G : Functor (PowerCat ^op) (PowerCat ^op)
  G = ⟦F⟧Pow ^opF

  private
    AlgCat = AlgebrasCategory G

  -- carrier: ν F, pointwise a SetGrammar
  νF-ob : X → SetGrammar ℓX
  νF-ob x .fst = ν F x
  νF-ob x .snd = isSetGrammarν F isSetValF x

  -- structure map: `finalCoalgebra` (= unroll). In `PowerCat ^op` this is a map
  -- `G νF-ob → νF-ob`, i.e. in PowerCat the coalgebra map `νF-ob → ⟦F⟧Pow νF-ob`.
  νF-str : (PowerCat ^op) [ Functor.F-ob G νF-ob , νF-ob ]
  νF-str x = finalCoalgebra F x

  νF-coalg : Category.ob AlgCat
  νF-coalg = νF-ob , νF-str

  module _ (Bβ : Category.ob AlgCat) where
    private
      B : X → SetGrammar ℓX
      B = Bβ .fst
      β : (PowerCat ^op) [ Functor.F-ob G B , B ]
      β = Bβ .snd

      -- `β` as a gsa coalgebra `∀ x → ⟨B x⟩ ⊢ ⟦F x⟧ ⟨B⟩`.
      αB : ∀ x → B x .fst ⊢ ⟦ F x ⟧ (λ x → B x .fst)
      αB = β

    corecArrow : (PowerCat ^op) [ νF-coalg .fst , B ]
    corecArrow = corec F αB

    -- The displayed coherence (`α ⋆ f ≡ G-hom f ⋆ β` in `PowerCat ^op`) is the
    -- `sym` of the corecursor's coalgebra-hom law (the two ^op flips turn
    -- `corecHomo`'s `map ϕ ∘g α ≡ finalCoalgebra ∘g ϕ` into its converse).
    corecCoalgHom : AlgCat [ νF-coalg , Bβ ]
    corecCoalgHom = corecArrow , funExt (λ x → sym (corecHomo F αB .snd x))

    -- uniqueness: any algebra hom out of `νF-coalg` equals `corecCoalgHom`.
    corecCoalgHom-unique : ∀ (gh : AlgCat [ νF-coalg , Bβ ]) → corecCoalgHom ≡ gh
    corecCoalgHom-unique gh =
      isFaithfulFst (AlgStructureOver G) νF-coalg Bβ corecCoalgHom gh corecArrow≡g
      where
        g : (PowerCat ^op) [ νF-coalg .fst , B ]
        g = gh .fst

        gCoHomo : CoRecHomo F αB
        gCoHomo .fst = g
        gCoHomo .snd x = sym (funExt⁻ (gh .snd) x)

        corecArrow≡g : corecArrow ≡ g
        corecArrow≡g = coind F αB (corecHomo F αB) gCoHomo

  νF-isInitial : isInitial AlgCat νF-coalg
  νF-isInitial Bβ .fst = corecCoalgHom Bβ
  νF-isInitial Bβ .snd = corecCoalgHom-unique Bβ

  -- `isTerminal (AlgCat ^op) = isInitial AlgCat`, and
  -- `AlgCat ^op = CoalgebrasCategory ⟦F⟧Pow`.
  νF-Terminal-op : Terminal (AlgCat ^op)
  νF-Terminal-op = νF-coalg , νF-isInitial

  -- `TerminalCoalgebra ⟦F⟧Pow = InitialAlgebra G = Initial' AlgCat
  --                            = Terminal' (AlgCat ^op)`.
  νF-TerminalCoalgebra : TerminalCoalgebra ⟦F⟧Pow
  νF-TerminalCoalgebra = terminalToUniversalElement νF-Terminal-op
