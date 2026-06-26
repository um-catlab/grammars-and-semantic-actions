{- The public, *semantic* corecursor interface for indexed coinductives.

   This module ADDS, alongside the computational `corec`/`coind` from
   `Grammar.Coinductive.Indexed`, the cubical-categorical-logic-flavoured
   versions typed over the semantic endofunctor `⟦SPF⟧Pow`.

   Carriers are `SetGrammar`s; a coalgebra structure map is an
   `SPFCoalgebra A` (defeq to the old `Coalgebra F (λ x → ⟨ A x ⟩)`).  The
   final-coalgebra carrier `ν F` is made a `SetGrammar` via `isSetGrammarν`
   (the gate cleared in `Grammar.Coinductive.HLevels`).

   Everything delegates to the computational `corec`/`coind` (whose
   underlying maps are definitionally equal). -}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Coinductive.Coalgebra (Alphabet : hSet ℓ-zero) where

open import Grammar.Base Alphabet
open import Grammar.HLevels.Base Alphabet
open import Grammar.Inductive.Functor Alphabet using (SPFunctor ; map)
open import Grammar.Coinductive.Indexed Alphabet
  using (ν ; corec ; coind ; finalCoalgebra)
open import Grammar.Coinductive.HLevels Alphabet using (isSetGrammarν)
open import Grammar.Inductive.Semantic Alphabet
  using (SPFCoalgebra ; isSetValued)
open import Term.Base Alphabet

private
  variable ℓX : Level

module _ {X : Type ℓX}
  (F : X → SPFunctor X) (isSetValF : ∀ x → isSetValued (F x)) where

  -- The final-coalgebra carrier `ν F`, packaged pointwise as a SetGrammar.
  νF-ob : X → SetGrammar ℓX
  νF-ob x .fst = ν F x
  νF-ob x .snd = isSetGrammarν F isSetValF x

  -- The structural corecursor, semantic packaging. Underlying map = `corec`.
  corecS : (A : X → SetGrammar ℓX) → SPFCoalgebra F isSetValF A
         → ∀ x → ⟨ A x ⟩ ⊢ ν F x
  corecS A α = corec F α

  -- Uniqueness of coalgebra homomorphisms into the final coalgebra:
  -- two maps that are `⟦SPF⟧Pow`-coalgebra homs (over a common structure
  -- map `α`) agree.  The coherence is supplied inline (the c-c-l
  -- `CoalgebrasCategory` packaging is unnecessary for this delegation).
  coindS : (A : X → SetGrammar ℓX) (α : SPFCoalgebra F isSetValF A)
    (ϕ ϕ' : ∀ x → ⟨ A x ⟩ ⊢ ν F x)
    (cϕ  : ∀ x → map (F x) ϕ  ∘g α x ≡ finalCoalgebra F x ∘g ϕ  x)
    (cϕ' : ∀ x → map (F x) ϕ' ∘g α x ≡ finalCoalgebra F x ∘g ϕ' x)
    → ϕ ≡ ϕ'
  coindS A α ϕ ϕ' cϕ cϕ' = coind F α (ϕ , cϕ) (ϕ' , cϕ')
