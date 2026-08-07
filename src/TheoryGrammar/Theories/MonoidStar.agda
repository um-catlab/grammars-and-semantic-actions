{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The star, generic in a monoid promodel.

   `Strings/KleeneStar` and `Bags/Automata` hold line-for-line the same
   `starSlot`/`starAlt`/`starF` and the same guardedness proof, differing
   only in the body grammar.  Neither is about its instance: every line
   mentions `nilop`, `appop` and the grading, which is exactly what a
   promodel of `monoidSig` supplies.  So it lives here once.

   NOTE WHAT IS AND IS NOT ASSUMED.  This layer needs the SIGNATURE of
   monoids and a grading -- nothing else.  It does NOT need the theory
   to be ordered, and it does not need equidivisibility, which is why
   BAGS get a Kleene star out of it as well as strings.  Those two
   hypotheses buy the things that genuinely need a left -- the
   derivative, First/FollowLast, leftmost-longest -- and none of them
   appear below.

   The one hypothesis is `ProperBody`: the star's body must be a proper
   resource.  That is the generic form of "non-nullable", and it is
   exactly the condition `Strings/KleeneStar` already documented as the
   fence around `(ε)*`.
-}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Theories.MonoidStar where

open import Cubical.Data.Bool using (Bool; true; false; if_then_else_)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded
open import TheoryGrammar.Theories.Monoid

-- Levels are pinned at ℓ-zero: that is what every monoid instance in
-- this tree uses, and leaving them open costs a `ℓ-max ℓP ℓA` in the
-- type of `ε'` for no gain.
module MonStar (GS : GradedFib monoidSig ℓ-zero ℓ-zero) where

  open Guard GS ℓ-zero Unit (λ _ → tt) public
  open FibNotation (GS .fib) public

  Gr : Type₁
  Gr = TheoryTy ℓ-zero tt

  -- the unit and the product, generic in the promodel
  ε' : Gr
  ε' = ⊗ˢ nilop (λ ())

  _⊗'_ : Gr → Gr → Gr
  A ⊗' B = ⊗ˢ appop (λ b → if b then A else B)

  infixr 20 _⊗'_

  -- ================================================================
  -- The star description.
  -- ================================================================

  starSlot : Gr → Bool → Functor tt
  starSlot A true  = ⌜ A ⌝
  starSlot A false = Var tt

  starAlt : Gr → Bool → Functor tt
  starAlt A true  = ⌜ ε' ⌝
  starAlt A false = ⊗e appop (starSlot A)

  starF : Gr → Unit → Functor tt
  starF A _ = ⊕e Bool (starAlt A)

  -- THE HYPOTHESIS.  "The body is a proper resource" -- generically what
  -- non-nullability says.  If `A` accepts the unit then the splitting
  -- `(ε , w)` puts the recursive occurrence back at `w` and the star has
  -- infinitely many parses at every index; this is the fence.
  ProperBody : Gr → Type₀
  ProperBody A = (m : GS .fib .carrier tt) (sp : GS .fib .Split appop m)
               → A (GS .fib .parts appop m sp true)
               → GS .Proper appop m sp false

  starGuarded : (A : Gr) → ProperBody A → (x : Unit) → Guarded (starF A x)
  starGuarded A pb tt = <⊕e Bool (starAlt A) alt
    where
      go : (m : GS .fib .carrier tt) (sp : GS .fib .Split appop m)
           (sh : (a : Bool) → Sh (starSlot A a) (GS .fib .parts appop m sp a))
           (a : Bool) (p : Pos (starSlot A a) _ (sh a))
         → degIx (nx (starSlot A a) _ (sh a) p) < GS .deg tt m
      go m sp sh true ()
      go m sp sh false p =
        slotProper appop m sp false (≤Var tt)
                   (pb m sp (lower (sh true))) (sh false) p

      alt : (b : Bool) → Guarded (starAlt A b)
      alt true  = <⌜⌝ ε'
      alt false = ⊗-guard appop (starSlot A) go

  -- ================================================================
  -- ... and the star itself, with its intro and elim rules.
  -- ================================================================

  KL* : Gr → Gr
  KL* A w = μ (starF A) (tt , w)

  module _ {A : Gr} where

    nil* : ε' ⊢ KL* A
    nil* w e = sup (true , lift e) λ ()

    cons* : (A ⊗' KL* A) ⊢ KL* A
    cons* w (sp , h) =
      sup (false , sp , λ { true → lift (h true) ; false → tt* })
          λ { (true , ()) ; (false , _) → h false }
