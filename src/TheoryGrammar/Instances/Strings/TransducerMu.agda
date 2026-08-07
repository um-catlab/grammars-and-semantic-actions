{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{-
  THE TRANSDUCER AS AN INDUCTIVE GRAMMAR OVER THE GLUE.

  `Transducer.Trans` is an `Eq`-predicate: it asserts the letterwise
  property rather than building it.  This file gives the same thing as a
  `μ` over the GLUED promodel -- `nil ⊕ (Letter ⊗ Var)` at the aligned
  substrate -- which is the first time `TheoryGrammar.Inductive` meets a
  carrier whose splittings carry a payload.

  What it measures: the generic container semantics goes through with no
  adjustment, and the ALGEBRA of the soundness fold is exactly the two
  multiplicative primitives of `Transducer` -- `transNil` at the `nil`
  branch, `transTensor` at the `cons` branch.  Nothing about gluing
  appears in it.
  PRIMITIVE: `letterTrans` (one `Eq` composite, no match).
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Strings.TransducerMu
  (In Out : Type₀) (f : In → Out) where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit
open import Cubical.Data.List
open import Cubical.Data.Empty using (⊥*)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Theories.Monoid
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive

import TheoryGrammar.Instances.Strings.Transducer as Tr
open Tr In Out f public

-- ==================================================================
-- The grammar of ALIGNED SINGLE LETTERS: `(c , f c)`, as a `⊕ᴰ` of a
-- pair of representables.  This is the only new grammar; everything
-- else is the description former.
-- ==================================================================

Letter : G.TheoryTy ℓ-zero tt
Letter g = Σ[ c ∈ In ] ((g .fst Eq.≡ c ∷ []) × (g .snd .fst Eq.≡ f c ∷ []))

-- PRIMITIVE.  A single aligned letter is transduced.  Written as an `Eq`
-- composite rather than by matching, because `g .fst` is a projection --
-- matching `Eq.refl` there is not a pattern Agda can solve.
letterTrans : (g : Aligned) → Letter g → Trans g
letterTrans g (c , e₁ , e₂) = Eq.ap (map f) e₁ Eq.∙ Eq.sym e₂

-- ==================================================================
-- THE DESCRIPTION.  One nonterminal, two branches.
-- ==================================================================

open Ind glue ℓ-zero Unit (λ _ → tt)

consSlot : (a : MonAr appop) → Functor tt
consSlot true  = ⌜ Letter ⌝
consSlot false = Var tt

branch : Bool → Functor tt
branch true  = ⊗e nilop (λ ())
branch false = ⊗e appop consSlot

TransF : (x : Unit) → Functor tt
TransF _ = ⊕e Bool branch

-- the inductive transducer
TransM : Ix → Type _
TransM = μ TransF

-- ==================================================================
-- SOUNDNESS, as a fold.  The algebra is `transNil` and `transTensor`;
-- the recursion, the shapes and the index bookkeeping are generic.
-- ==================================================================

μ→Trans : (g : Aligned) → TransM (tt , g) → Trans g
μ→Trans g t = fold M α (tt , g) t
  where
  M : Ix → Type ℓ-zero
  M i = Trans (i .snd)

  α : (x : Unit) (m : Aligned) (sh : Sh (TransF x) m)
    → ((p : Pos (TransF x) m sh) → M (nx (TransF x) m sh p)) → M (tt , m)
  α _ m (true  , sp , _)  _  = transNil m (sp , λ ())
  α _ m (false , sp , sh) rc =
    transTensor m (sp , pay)
    where
    pay : (a : MonAr appop) → Trans (glue .parts appop m sp a)
    pay true  = letterTrans (glue .parts appop m sp true) (sh true .lower)
    pay false = rc (false , tt*)

-- ==================================================================
-- A CLOSED ELEMENT, and the fold run on it.
-- ==================================================================

module _ (x : In) where

  private
    w1 : I.String
    w1 = x ∷ []

    g1 : Aligned
    g1 = w1 , f x ∷ [] , Eq.refl

    -- the empty aligned pair, where the recursion stops
    g0 : Aligned
    g0 = [] , [] , Eq.refl

    -- split `x` off the front: the remainder is empty on BOTH tapes,
    -- and only the input half of that was chosen
    cut1 : I.strFib .Split appop w1
    cut1 = (x ∷ []) , [] , I.cons I.nil

    glued : glue .Split appop g1
    glued = cut1 , alignedDetermined appop g1 cut1

    -- the base case: the nullary splitting of the empty pair
    nilSplit : glue .Split nilop g0
    nilSplit = tt , tt , λ ()

    one : TransM (tt , g1)
    one = sup (false , glued , shapes) recur
      where
      shapes : (a : MonAr appop) → Sh (consSlot a) (glue .parts appop g1 glued a)
      shapes true  = lift (x , Eq.refl , Eq.refl)
      shapes false = tt*

      recur : (p : Pos (TransF tt) g1 (false , glued , _)) → TransM _
      recur (true  , ())
      recur (false , tt*) = sup (true , nilSplit , λ ()) (λ { (() , _) })

  -- the fold evaluates, and to the canonical proof
  _ : μ→Trans g1 one ≡ Eq.refl
  _ = refl
