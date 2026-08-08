{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- THE PRETTY-PRINTER, AND ITS ROUND TRIP. A printer takes a parse tree to
   a string. -}
module TheoryGrammar.Quine.RoundTrip where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe using (Maybe; just; nothing)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.SemanticAction using (passes; _↦_; _at_)
open import TheoryGrammar.Quine.Base

-- §1  THE TARGET, and the one primitive.

-- "a string, and it is the world I am at"
Printed : Gr
Printed = ⊕ᴰ String (λ s → ⌈ s ⌉)

-- PRIMITIVE (phase 1).  The parts of a splitting concatenate to the
-- whole.  The only place a splitting is taken apart, and the only fact
-- about `Split3` the printer needs.
split3++ : {u v w : String} → Split3 u v w → (u ++ v) Eq.≡ w
split3++ nil            = Eq.refl
split3++ (cons {c} sp)  = Eq.ap (c ∷_) (split3++ sp)

-- ... and its reading as a rule: concatenating the slots' printings is
-- a printing of the whole.  `Eq.refl` on both slots is what carries the
-- two facts `u = s₁`, `v = s₂` into the goal.
catAt : {u v w : String} → Split3 u v w → Printed u → Printed v → Printed w
catAt sp (s₁ , Eq.refl) (s₂ , Eq.refl) = (s₁ ++ s₂) , Eq.sym (split3++ sp)

catRep : ⊗ˢ appop (λ _ → Printed) ⊢ Printed
catRep w ((u , v , sp) , h) = catAt sp (h true) (h false)

-- §2 THE PRINTER, one clause per production.

PMot : G.Ix → Type₀
PMot i = Printed (i .snd)

printAlg : G.AlgC CYKF PMot
printAlg P = ⊕ᴰ-E branch
  where
    branch : (r : Rule P) → G.⟦ ruleF P r ⟧c PMot ⊢ Printed
    branch (inl (c , pf)) =
      ⊕ᴰ-I String {A = λ s → ⌈ s ⌉} (c ∷ []) ∘g lowerg
    branch (inr (Q , T , pf)) =
      catRep
      ∘g ⊗ˢ-map appop {A = λ a → G.⟦ binSlot Q T a ⟧c PMot} {B = λ _ → Printed}
           (λ { true  → &ᴰ-E Bool {B = λ b → G.⟦ NEslot Q b ⟧c PMot} true
              ; false → &ᴰ-E Bool {B = λ b → G.⟦ NEslot T b ⟧c PMot} true })

print : (P : NT) → Deriv P ⊢ Printed
print P w t = G.foldC PMot printAlg (P , w) t

-- §3 THE ROUND TRIP, as a theorem about EVERY derivation.

printed : (P : NT) (w : String) → Deriv P w → String
printed P w t = print P w t .fst

printOK : (P : NT) (w : String) (t : Deriv P w) → printed P w t ≡ w
printOK P w t = sym (Eq.eqToPath (print P w t .snd))

-- §4 ... and the pipeline. `parse`, then `print`.

roundTrip : (P : NT) → ⊤G ⊢ Result (¬G Deriv P) Printed
roundTrip P = mapR (¬G Deriv P) Printed (print P) ∘g derives? P

printS : (P : NT) → Deriv P ⊢ Δ String
printS P = tagA String {A = λ s → ⌈ s ⌉} ∘g print P

printD : (P : NT) → ⊤G ⊢ Result (¬G Deriv P) (Δ String)
printD P = mapR (¬G Deriv P) (Δ String) (printS P) ∘g derives? P

runPrint : (P : NT) → String → Maybe String
runPrint P = runΔ String (¬G Deriv P) (printD P)

-- ... and it COMPUTES.  These add nothing to `printOK` logically; they
-- are the evidence that the whole pipeline evaluates at typecheck time.
_ : passes (runPrint ntS at
             ( (c0 ∷ c# ∷ c0 ∷ c0 ∷ [])                ↦ just (c0 ∷ c# ∷ c0 ∷ c0 ∷ [])
             ∷ (c1 ∷ c# ∷ c1 ∷ c1 ∷ [])                ↦ just (c1 ∷ c# ∷ c1 ∷ c1 ∷ [])
             ∷ (c0 ∷ c1 ∷ c# ∷ c0 ∷ c0 ∷ c1 ∷ c1 ∷ []) ↦ just (c0 ∷ c1 ∷ c# ∷ c0 ∷ c0 ∷ c1 ∷ c1 ∷ [])
             ∷ (c0 ∷ c# ∷ c0 ∷ [])                     ↦ nothing   -- not a program
             ∷ [] ))
_ = refl

-- the sub-nonterminals print their own spans too -- the printer is
-- defined at every nonterminal, not just at the root
_ : passes (runPrint ntE at
             ( (c0 ∷ c1 ∷ [])                ↦ just (c0 ∷ c1 ∷ [])
             ∷ (c0 ∷ c1 ∷ c1 ∷ c0 ∷ [])      ↦ just (c0 ∷ c1 ∷ c1 ∷ c0 ∷ [])
             ∷ (c0 ∷ [])                     ↦ nothing
             ∷ [] ))
_ = refl

-- §5  A COROLLARY WITH TEETH.  `printOK` plus `witness` says the round
--     trip holds at any text the decision ACCEPTS -- and acceptance is
--     itself checked by evaluation, so this is a closed argument.

roundTripAt : (w : String) (pf : run (derives! ntS) w ≡ true)
            → printed ntS w (witness (Deriv ntS) (¬G Deriv ntS) (derives? ntS) w pf) ≡ w
roundTripAt w pf = printOK ntS w _
