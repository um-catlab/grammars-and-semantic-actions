{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- The splittings of w are its length+1 cuts, enumerated and proved complete. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Strings.Enumeration (Char : Type₀) where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.List
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Substrate
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded
open import Cubical.Foundations.Isomorphism

open import TheoryGrammar.Instances.Strings.KleeneStar Char public

Splits : Gr
Splits = ⊤G ⊗' ⊤G

splitsIso : (w : String) → Iso (Splits w) (MonSplit appop w)
splitsIso w .Iso.fun (sp , _) = sp
splitsIso w .Iso.inv sp       = sp , λ { true → tt ; false → tt }
splitsIso w .Iso.sec sp       = refl
splitsIso w .Iso.ret (sp , h) =
  ΣPathP (refl , funExt λ { true → refl ; false → refl })

-- ENUMERATION OF SPLITTINGS.  Derivable, not assumed: the splittings
-- of `w` are its `length w + 1` cuts.

data _∈L_ {X : Type₀} (x : X) : List X → Type₀ where
  here  : ∀ {xs} → x ∈L (x ∷ xs)
  there : ∀ {y xs} → x ∈L xs → x ∈L (y ∷ xs)

∈map : {X Y : Type₀} (f : X → Y) {x : X} {xs : List X}
     → x ∈L xs → f x ∈L map f xs
∈map f here      = here
∈map f (there p) = there (∈map f p)

cuts : (w : String) → List (MonSplit appop w)
cuts []      = ([] , [] , nil) ∷ []
cuts (c ∷ w) =
  ([] , c ∷ w , nil) ∷ map (λ { (u , v , s) → (c ∷ u , v , cons s) }) (cuts w)

cutsComplete : {u v w : String} (s : Split3 u v w) → (u , v , s) ∈L cuts w
cutsComplete {v = []}    nil = here
cutsComplete {v = _ ∷ _} nil = here
cutsComplete (cons s)        = there (∈map _ (cutsComplete s))

enumSplit : (o : MonOp) (m : String) → List (MonSplit o m)
enumSplit nilop []      = tt ∷ []
enumSplit nilop (_ ∷ _) = []
enumSplit appop w       = cuts w

enumComplete : (o : MonOp) (m : String) (sp : MonSplit o m) → sp ∈L enumSplit o m
enumComplete nilop []      tt = here
enumComplete appop w (u , v , s) = cutsComplete s
