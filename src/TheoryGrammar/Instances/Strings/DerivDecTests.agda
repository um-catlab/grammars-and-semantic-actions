{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- DOES THE DERIVATIVE ROUTE COMPUTE? `DerivDec` decides the tensor by
   recursion on the WORLD instead of by searching a list of cuts. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Strings.DerivDecTests where

open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.List
open import Cubical.Data.Empty using (⊥*)

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Decidable.Splittings
open import TheoryGrammar.Decidable.Enumerated
open import TheoryGrammar.Enumerable using (decΠBool)

data Chr : Type₀ where
  ca cb : Chr

open import TheoryGrammar.Instances.Strings.DerivDec Chr
import TheoryGrammar.Instances.Strings.Enumeration Chr as SE

-- Two singleton grammars, decidable by construction.

Lit : Chr → Gr
Lit c []       = ⊥*
Lit ca (ca ∷ []) = Unit*
Lit ca (cb ∷ _)  = ⊥*
Lit ca (ca ∷ _ ∷ _) = ⊥*
Lit cb (cb ∷ []) = Unit*
Lit cb (ca ∷ _)  = ⊥*
Lit cb (cb ∷ _ ∷ _) = ⊥*

decLit : (c : Chr) (w : String) → Dec⟨ Lit c ⟩ w
decLit c       []           = dec-no (Lit c) [] λ ()
decLit ca (ca ∷ [])         = dec-yes (Lit ca) (ca ∷ []) tt*
decLit ca (cb ∷ w)          = dec-no  (Lit ca) (cb ∷ w) λ ()
decLit ca (ca ∷ x ∷ w)      = dec-no  (Lit ca) (ca ∷ x ∷ w) λ ()
decLit cb (cb ∷ [])         = dec-yes (Lit cb) (cb ∷ []) tt*
decLit cb (ca ∷ w)          = dec-no  (Lit cb) (ca ∷ w) λ ()
decLit cb (cb ∷ x ∷ w)      = dec-no  (Lit cb) (cb ∷ x ∷ w) λ ()

-- the tensor under test: "an `a` followed by a `b`"
Slots : Bool → Gr
Slots = boolΠ (Lit ca) (Lit cb)

-- the deciders both routes are handed, at any word
deciders : (w : String) (sp : MonSplit appop w) (a : Bool)
         → Dec⟨ Slots a ⟩ (MonParts appop w sp a)
deciders w (u , v , s) true  = decLit ca u
deciders w (u , v , s) false = decLit cb v

-- The two routes, at the same tensor.

open DecEnum strFib using (dec-⊗-cuts)

viaDeriv : (w : String) → Dec⟨ ⊗ˢ appop Slots ⟩ w
viaDeriv w = strDecDeriv .dec-⊗ˢ appop Slots w (deciders w)

viaCuts : (w : String) → Dec⟨ ⊗ˢ appop Slots ⟩ w
viaCuts w =
  dec-⊗-cuts appop Slots w (SE.enumSplit appop w) (SE.enumComplete appop w)
             (λ sp → decΠBool (deciders w sp true) (deciders w sp false))

-- read a decision as a Bool, so the answers can be pinned
yes? : {A : Gr} (w : String) → Dec⟨ A ⟩ w → Bool
yes? {A} w = dec-elim A w (λ _ → true) (λ _ → false)

-- THE MEASUREMENT.  Every line below is `refl`.

ab ba aab : String
ab  = ca ∷ cb ∷ []
ba  = cb ∷ ca ∷ []
aab = ca ∷ ca ∷ cb ∷ []

-- the derivative route reduces ...
_ : yes? ab  (viaDeriv ab)  ≡ true
_ = refl

_ : yes? ba  (viaDeriv ba)  ≡ false
_ = refl

_ : yes? aab (viaDeriv aab) ≡ false
_ = refl

_ : yes? [] (viaDeriv []) ≡ false
_ = refl

-- ... and agrees with the enumeration route, which also reduces
_ : yes? ab  (viaCuts ab)  ≡ true
_ = refl

_ : yes? ba  (viaCuts ba)  ≡ false
_ = refl

_ : yes? aab (viaCuts aab) ≡ false
_ = refl

_ : yes? [] (viaCuts []) ≡ false
_ = refl
