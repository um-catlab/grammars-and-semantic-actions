open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Par.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure

open import Grammar.Base Alphabet
open import Grammar.Bottom Alphabet
open import Grammar.Epsilon Alphabet using (ε)
open import Grammar.LinearProduct Alphabet
open import Grammar.Product.Binary.AsPrimitive Alphabet
open import Grammar.String Alphabet
open import Grammar.Par.Base Alphabet
open import Term.Base Alphabet

private
  variable
    ℓA ℓB ℓC ℓD : Level
    A : Grammar ℓA
    B : Grammar ℓB
    C : Grammar ℓC
    D : Grammar ℓD

-- The bridge back from the guarded core, gated by nullability: if both
-- operands cover ε (for refutation grammars: the positives are
-- non-nullable), the degenerate splits are discharged by the ε-terms —
-- external case on the &ᴰ index decides which regime each split is in —
-- and the proper splits by the core.
module _ (Aε : ε ⊢ A) (Bε : ε ⊢ B) where
  ⅋∘-complete : (A ⅋∘ B) ⊢ (A ⅋ B)
  ⅋∘-complete = {!!}

-- The Chu consistency lemma: disjointness propagates through ⊗/⅋.
-- Pointwise: an ⊗-parse of w picks a split w ≡ u ++ v with A u and B v;
-- interrogating the ⅋ at (u , v) — the ⌈⌉-witnesses come from mk⌈⌉
-- transported along the split — returns either C at the u-part or D at
-- the v-part.  Same-splitting (uniquely-supported-⌈⌉Eq on the ⌈⌉ factor,
-- cf. unique-splitting-⌈⌉L in Grammar.External.String.Tiny, plus its
-- right-handed analogue) aligns the parts, and dA/dB close the branch.
module _ (dA : (A & C) ⊢ ⊥) (dB : (B & D) ⊢ ⊥) where
  ⊗⅋-disjoint : ((A ⊗ B) & (C ⅋ D)) ⊢ ⊥
  ⊗⅋-disjoint = {!!}
