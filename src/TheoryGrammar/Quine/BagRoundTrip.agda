{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  THE PRINTER, AND WHY ITS TYPE MUST WEAKEN AT BAGS.

  `Quine.RoundTrip` builds a printer whose TYPE is its correctness
  proof:

      Printed  =  ⊕ᴰ String ⌈_⌉        -- "a string, which is my index"

  so `print : Deriv P ⊢ Printed` cannot be wrong.  The whole content of
  that file is its single primitive,

      split3++ : Split3 u v w → (u ++ v) Eq.≡ w

  -- "the parts of a splitting concatenate to the whole" -- because at a
  binary production the two slots print `s₁` at `u` and `s₂` at `v`, the
  node must print SOMETHING at `w`, and concatenation is the only way
  through.

  AT BAGS THAT PRIMITIVE IS FALSE, and `notCat` below is the
  counterexample as a term: `Ilv (k0) (q0) (q0 k0)` is a splitting whose
  parts concatenate to `k0 q0`, a different text.  So `⊕ᴰ Bag ⌈_⌉` is
  not the codomain of any COMPOSITIONAL printer over this theory.  (The
  type stays inhabited -- `⌈_⌉`'s fibre is a singleton, so `λ w t → (w ,
  Eq.refl)` inhabits it -- but that is the identity wearing a costume,
  not a printer.  `Quine.RoundTrip`'s own header makes the same point
  about where the content of such a type lies.)

  WHAT REPLACES IT is the theory's own permutation relation, and the
  replacement for `split3++` is `permMerge`, which
  `Instances.Bags.Permutation` already has:

      permMerge : Perm a u → Perm b v → Ilv u v w → Perm (a ++ b) w

  So the printer's codomain is

      Printed  =  ⊕ᴰ Bag (λ s → Perm s _)     -- "a text, up to order"

  and the theorem it proves, uniformly in every derivation, is

      printOK : (t : Deriv P w) → Perm (printed t) w

  -- "the printer prints a PERMUTATION of its input", not "the printer
  prints its input".  That weakening is not a shortcoming of this file;
  it is the same fact as `Quine.Bag`'s "a bag quine is an equivalence
  class of texts".  The theory has no term distinguishing the members of
  the class, so no term of the theory can promise one of them.

  AND THE COROLLARY THAT MAKES THE QUINE TESTS MEAN WHAT THEY SAY.
  `count` cannot see order either (`countPerm`), so the printer is EXACT
  at the level the quine equation is stated at:

      printCount : (t : Deriv P w) → count (printed t) ≡ count w
-}
module TheoryGrammar.Quine.BagRoundTrip where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.SemanticAction using (passes; _↦_; _at_)
open import TheoryGrammar.Quine.Bag
open import TheoryGrammar.Instances.Bags.Permutation Chr
  using (Perm; permRefl; permMerge; ilvNilL)
  renaming (nil to permNil; cons to permCons)

-- §1  THE STRING PRINTER'S PRIMITIVE, REFUTED.

headIsK : Bag → Bool
headIsK (k0 ∷ _) = true
headIsK _        = false

notCat : Σ[ u ∈ Bag ] Σ[ v ∈ Bag ] Σ[ w ∈ Bag ]
           (Ilv u v w × ((u ++ v) ≡ w → ⊥))
notCat = (k0 ∷ []) , (q0 ∷ []) , (q0 ∷ k0 ∷ [])
       , right (left nil)
       , λ p → true≢false (cong headIsK p)

-- §2  THE TARGET, and the two things that build it.

-- "a text, and my world is a rearrangement of it"
PermG : Bag → Gr
PermG s w = Perm s w

Printed : Gr
Printed = ⊕ᴰ Bag PermG

-- PRIMITIVE (phase 1). A one-letter world prints itself; the only place
-- `⌈_⌉`'s `Eq.refl` is taken apart.
litPerm : (s : Bag) → ⌈ s ⌉ ⊢ PermG s
litPerm s = ⌈⌉-E {a = s} {B = PermG s} (permRefl s)

-- ... and the binary rule, which at strings was concatenation and here
-- is `permMerge`.  Note NO `Eq.refl` is matched: the two slots'
-- permutations and the interleaving are exactly its three inputs.
catAt : {u v w : Bag} → Ilv u v w → Printed u → Printed v → Printed w
catAt s (s₁ , p₁) (s₂ , p₂) = (s₁ ++ s₂) , permMerge p₁ p₂ s

catRep : ⊗ˢ appop (λ _ → Printed) ⊢ Printed
catRep w ((u , v , sp) , h) = catAt sp (h true) (h false)

-- §3  THE PRINTER, one clause per production.  Line for line
--     `Quine.RoundTrip`'s -- only the two primitives above differ.

PMot : G.Ix → Type₀
PMot i = Printed (i .snd)

printAlg : G.AlgC CYKF PMot
printAlg P = ⊕ᴰ-E branch
  where
    branch : (r : Rule P) → G.⟦ ruleF P r ⟧c PMot ⊢ Printed
    branch (inl (c , pf)) =
      ⊕ᴰ-I Bag {A = PermG} (c ∷ []) ∘g litPerm (c ∷ []) ∘g lowerg
    branch (inr (Q , T , pf)) =
      catRep
      ∘g ⊗ˢ-map appop {A = λ a → G.⟦ binSlot Q T a ⟧c PMot} {B = λ _ → Printed}
           (λ { true  → &ᴰ-E Bool {B = λ b → G.⟦ NEslot Q b ⟧c PMot} true
              ; false → &ᴰ-E Bool {B = λ b → G.⟦ NEslot T b ⟧c PMot} true })

print : (P : NT) → Deriv P ⊢ Printed
print P w t = G.foldC PMot printAlg (P , w) t

-- §4  THE ROUND TRIP, as a theorem about EVERY derivation -- and it is
--     a PERMUTATION, which is all this theory can say.  Nothing is
--     checked at a particular text here.

printed : (P : NT) (w : Bag) → Deriv P w → Bag
printed P w t = print P w t .fst

printOK : (P : NT) (w : Bag) (t : Deriv P w) → Perm (printed P w t) w
printOK P w t = print P w t .snd

-- §5 ... AND IT IS EXACT ON MULTISETS.

-- an insertion moves the inserted letter's count out front
countIns : {x : Chr} {v w : Bag} → Ilv (x ∷ []) v w
         → count w ≡ bitM x ⊎M count v
countIns {x} (left s) =
  cong (bitM x ⊎M_) (sym (cong count (Eq.eqToPath (ilvNilL s))))
countIns {x} (right {x = y} s) =
  cong (bitM y ⊎M_) (countIns s) ∙ ⊎M-swap (bitM y) (bitM x) _

countPerm : {a w : Bag} → Perm a w → count a ≡ count w
countPerm permNil                = refl
countPerm (permCons {x = x} p i) =
  cong (bitM x ⊎M_) (countPerm p) ∙ sym (countIns i)

printCount : (P : NT) (w : Bag) (t : Deriv P w)
           → count (printed P w t) ≡ count w
printCount P w t = countPerm (printOK P w t)

-- §6 ... and it COMPUTES. These add nothing to §4 logically; they are the
-- evidence that the whole pipeline evaluates.

printS : (P : NT) → Deriv P ⊢ Δ Bag
printS P = tagA Bag {A = PermG} ∘g print P

printD : (P : NT) → ⊤G ⊢ Result (¬G Deriv P) (Δ Bag)
printD P = mapR (¬G Deriv P) (Δ Bag) (printS P) ∘g derives? P

runPrint : (P : NT) → Bag → Maybe Bag
runPrint P = runΔ Bag (¬G Deriv P) (printD P)

_ : passes (runPrint ntS at
             ( (k0 ∷ q0 ∷ [])             ↦ just (k0 ∷ q0 ∷ [])
             ∷ (k0 ∷ k1 ∷ q0 ∷ q1 ∷ [])   ↦ just (k0 ∷ k1 ∷ q0 ∷ q1 ∷ [])
             ∷ (q0 ∷ k0 ∷ [])             ↦ just (k0 ∷ q0 ∷ [])
             ∷ (k0 ∷ [])                  ↦ nothing   -- not a program
             ∷ [] ))
_ = refl
