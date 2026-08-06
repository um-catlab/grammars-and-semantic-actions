{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Listable index sets: membership, and deciding a Σ by searching a
   complete list.  Used both by the instances (to enumerate splittings)
   and by the decidability layer (`dec-⊗-enum`, `dec-⊕ᴰ`). -}
module TheoryGrammar.Enumerable where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Bool
open import Cubical.Data.Unit
open import Cubical.Data.List
open import Cubical.Data.Empty using (⊥*)

private variable ℓM ℓA : Level

data _∈L_ {X : Type ℓM} (x : X) : List X → Type ℓM where
  here  : {xs : List X} → x ∈L (x ∷ xs)
  there : {y : X} {xs : List X} → x ∈L xs → x ∈L (y ∷ xs)

∈map : {X Y : Type ℓM} (f : X → Y) {x : X} {xs : List X}
     → x ∈L xs → f x ∈L map f xs
∈map f here      = here
∈map f (there p) = there (∈map f p)


No : {ℓ : Level} → Type ℓ → Type ℓ
No X = X → ⊥* {ℓ-zero}

AllNo' : {I : Type ℓM} (B : I → Type ℓA) → List I → Type (ℓ-max ℓM ℓA)
AllNo' B []       = Unit*
AllNo' B (i ∷ is) = No (B i) × AllNo' B is

lookupNo' : {I : Type ℓM} {B : I → Type ℓA} (is : List I) (i : I)
          → i ∈L is → AllNo' B is → No (B i)
lookupNo' (i ∷ is) .i here      (k , _) = k
lookupNo' (_ ∷ is) i  (there p) (_ , r) = lookupNo' is i p r

walk : {I : Type ℓM} {B : I → Type ℓA}
     → ((i : I) → B i ⊎ No (B i)) → (is : List I)
     → (Σ[ i ∈ I ] B i) ⊎ AllNo' B is
walk d []       = inr tt*
walk d (i ∷ is) = here? (d i)
  where
    here? : _ → _
    here? (inl b) = inl (i , b)
    here? (inr k) = later? (walk d is)
      where later? : _ → _
            later? (inl y) = inl y
            later? (inr r) = inr (k , r)

decΣ : {I : Type ℓM} {B : I → Type ℓA}
     → (allI : List I) → ((i : I) → i ∈L allI)
     → ((i : I) → B i ⊎ No (B i))
     → (Σ[ i ∈ I ] B i) ⊎ No (Σ[ i ∈ I ] B i)
decΣ allI complete d = out (walk d allI)
  where out : _ → _
        out (inl y)   = inl y
        out (inr all) = inr λ x → lookupNo' allI (x .fst) (complete (x .fst))
                                            all (x .snd)

-- a Π over Bool, decided slotwise
decΠBool : {B : Bool → Type ℓA}
         → B true ⊎ No (B true) → B false ⊎ No (B false)
         → ((b : Bool) → B b) ⊎ No ((b : Bool) → B b)
decΠBool (inr k) _        = inr λ f → k (f true)
decΠBool (inl _) (inr k)  = inr λ f → k (f false)
decΠBool (inl x) (inl y)  = inl λ { true → x ; false → y }
