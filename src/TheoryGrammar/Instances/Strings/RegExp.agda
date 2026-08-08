{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Regular expressions and Brzozowski matching, over the generic
   connectives. -}
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sum using (_⊎_; inl; inr)
import Cubical.Data.Equality as Eq
open import TheoryGrammar.Enumerable using (No)

module TheoryGrammar.Instances.Strings.RegExp
  (Char : Type₀)
  (decChar : (a b : Char) → (a Eq.≡ b) ⊎ No (a Eq.≡ b))
  where

open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.List
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Enumerable using (No)

open import TheoryGrammar.Instances.Strings.Derivative Char public

private variable b b₁ b₂ : Bool

-- Syntax, indexed by nullability.

data RegExp : Bool → Type₀ where
  ∅ᵣ  : RegExp false
  εᵣ  : RegExp true
  ⟨_⟩ : Char → RegExp false
  _∪_ : RegExp b₁ → RegExp b₂ → RegExp (b₁ or b₂)
  _·_ : RegExp b₁ → RegExp b₂ → RegExp (b₁ and b₂)
  _⋆  : RegExp false → RegExp true

infixr 25 _·_
infixr 24 _∪_
infix  26 _⋆

⟪_⟫ : RegExp b → Gr
⟪ ∅ᵣ    ⟫ = ⊥G
⟪ εᵣ    ⟫ = ε'
⟪ ⟨ c ⟩ ⟫ = literal c
⟪ r ∪ s ⟫ = ⟪ r ⟫ ⊕ ⟪ s ⟫
⟪ r · s ⟫ = ⟪ r ⟫ ⊗' ⟪ s ⟫
⟪ r ⋆   ⟫ = KL* ⟪ r ⟫

-- The index really is nullability: both directions.

private
  orFalseL : b₁ or b₂ Eq.≡ false → b₁ Eq.≡ false
  orFalseL {false} e = Eq.refl
  orFalseL {true}  ()

  orFalseR : b₁ or b₂ Eq.≡ false → b₂ Eq.≡ false
  orFalseR {false} e = e
  orFalseR {true}  ()

  orTrue : b₁ or b₂ Eq.≡ true → (b₁ Eq.≡ true) ⊎ (b₂ Eq.≡ true)
  orTrue {true}  e = inl Eq.refl
  orTrue {false} e = inr e

  andFalse : b₁ and b₂ Eq.≡ false → (b₁ Eq.≡ false) ⊎ (b₂ Eq.≡ false)
  andFalse {false} e = inl Eq.refl
  andFalse {true}  e = inr e

  andTrueL : b₁ and b₂ Eq.≡ true → b₁ Eq.≡ true
  andTrueL {false} ()
  andTrueL {true}  e = Eq.refl

  andTrueR : b₁ and b₂ Eq.≡ true → b₂ Eq.≡ true
  andTrueR {false} ()
  andTrueR {true}  e = e

-- `false` really does refute ε -- this is what the star's derivative
-- consumes, and the only place the index earns its keep.
noNil : (r : RegExp b) → b Eq.≡ false → No (⟪ r ⟫ [])
noNil ∅ᵣ      e ()
noNil εᵣ      ()
noNil ⟨ c ⟩   e ()
noNil (r ⋆)   ()
noNil (r ∪ s) e (inl p) = noNil r (orFalseL e) p
noNil (r ∪ s) e (inr q) = noNil s (orFalseR e) q
noNil (r · s) e ((_ , _ , nil) , h) = go (andFalse e)
  where go : _ → _
        go (inl e₁) = noNil r e₁ (h true)
        go (inr e₂) = noNil s e₂ (h false)

-- ... and `true` really does supply one
yesNil : (r : RegExp b) → b Eq.≡ true → ⟪ r ⟫ []
yesNil ∅ᵣ      ()
yesNil ⟨ c ⟩   ()
yesNil εᵣ      e = tt , λ ()
yesNil (r ⋆)   e = nil* [] (tt , λ ())
yesNil (r ∪ s) e = go (orTrue e)
  where go : _ → (⟪ r ⟫ ⊕ ⟪ s ⟫) []
        go (inl e₁) = inl (yesNil r e₁)
        go (inr e₂) = inr (yesNil s e₂)
yesNil (r · s) e =
  ([] , [] , nil) ,
  λ { true → yesNil r (andTrueL e) ; false → yesNil s (andTrueR e) }

-- and hence a decision at ε, by the index alone
decNil : (r : RegExp b) → ⟪ r ⟫ [] ⊎ No (⟪ r ⟫ [])
decNil {b} r = go b Eq.refl
  where
    go : (d : Bool) → b Eq.≡ d → ⟪ r ⟫ [] ⊎ No (⟪ r ⟫ [])
    go true  e = inl (yesNil r e)
    go false e = inr (noNil r e)

-- The syntactic derivative. Its nullability is not determined statically
-- -- `δ_c r` can be nullable for a non-nullable `r` -- so it comes back
-- paired with its index.

RE : Type₀
RE = Σ[ d ∈ Bool ] RegExp d

private
  -- factored out so the correctness proofs can generalise over the
  -- decision rather than re-running it
  δlit : (c a : Char) → (c Eq.≡ a) ⊎ No (c Eq.≡ a) → RE
  δlit c a (inl _) = true  , εᵣ
  δlit c a (inr _) = false , ∅ᵣ

  -- the nullable-left summand exists only when the left factor is
  -- nullable, which the index tells us without a search
  δcat : {b₂ : Bool} → Bool → RE → RegExp b₂ → RE → RE
  δcat true  (_ , r') s (_ , s') = _ , ((r' · s) ∪ s')
  δcat false (_ , r') s _        = _ , (r' · s)

δᵣ : Char → RegExp b → RE
δᵣ c ∅ᵣ                  = false , ∅ᵣ
δᵣ c εᵣ                  = false , ∅ᵣ
δᵣ c ⟨ a ⟩               = δlit c a (decChar c a)
δᵣ c (r ∪ s)             = _ , (δᵣ c r .snd ∪ δᵣ c s .snd)
δᵣ c (_·_ {b₁ = b₁} r s) = δcat b₁ (δᵣ c r) s (δᵣ c s)
δᵣ c (r ⋆)               = _ , (δᵣ c r .snd · (r ⋆))

-- CORRECTNESS: `δᵣ` computes the semantic derivative.

private
  Aof : (r : RegExp b₁) (s : RegExp b₂) → (a : MonAr appop) → Gr
  Aof r s a = if a then ⟪ r ⟫ else ⟪ s ⟫

δ-sound    : (c : Char) (r : RegExp b) (w : String)
           → ⟪ δᵣ c r .snd ⟫ w → ⟪ r ⟫ (c ∷ w)
δ-complete : (c : Char) (r : RegExp b) (w : String)
           → ⟪ r ⟫ (c ∷ w) → ⟪ δᵣ c r .snd ⟫ w

-- ---- soundness ---------------------------------------------------

private
  δlit-sound : (c a : Char) (d : (c Eq.≡ a) ⊎ No (c Eq.≡ a)) (w : String)
             → ⟪ δlit c a d .snd ⟫ w → literal a (c ∷ w)
  δlit-sound c a (inl Eq.refl) []      _        = Eq.refl
  δlit-sound c a (inl Eq.refl) (_ ∷ _) (() , _)
  δlit-sound c a (inr n)       w       ()

  -- push the induction hypothesis through the LEFT slot of a tensor;
  -- the two families agree at `false` and differ at `true` by exactly
  -- the derivative
  slotL : (c : Char) (r : RegExp b₁) (s : RegExp b₂) (w : String)
        → (⟪ δᵣ c r .snd ⟫ ⊗' ⟪ s ⟫) w
        → ⊗ˢ appop (Derivᶜ.δA c (Aof r s)) w
  slotL c r s w ((u , v , sp) , h) =
    (u , v , sp) , λ { true  → δ-sound c r u (h true)
                     ; false → h false }

δ-sound c ∅ᵣ      w ()
δ-sound c εᵣ      w ()
δ-sound c ⟨ a ⟩   w x = δlit-sound c a (decChar c a) w x
δ-sound c (r ∪ s) w (inl p) = inl (δ-sound c r w p)
δ-sound c (r ∪ s) w (inr q) = inr (δ-sound c s w q)
δ-sound c (_·_ {b₁ = false} r s) w x =
  Derivᶜ.δ⊗-inv c (Aof r s) w (inr (slotL c r s w x))
δ-sound c (_·_ {b₁ = true} r s) w (inl x) =
  Derivᶜ.δ⊗-inv c (Aof r s) w (inr (slotL c r s w x))
δ-sound c (_·_ {b₁ = true} r s) w (inr y) =
  Derivᶜ.δ⊗-inv c (Aof r s) w
    (inl (yesNil r Eq.refl , δ-sound c s w y))
δ-sound c (r ⋆) w ((u , v , sp) , h) =
  cons* (c ∷ w) ((c ∷ u , v , cons sp)
                , λ { true  → δ-sound c r u (h true)
                    ; false → h false })

-- ---- completeness ------------------------------------------------

private
  δlit-complete : (c a : Char) (d : (c Eq.≡ a) ⊎ No (c Eq.≡ a)) (w : String)
                → literal a (c ∷ w) → ⟪ δlit c a d .snd ⟫ w
  δlit-complete c a (inl _)  .[] Eq.refl = tt , λ ()
  δlit-complete c a (inr n) w    e       = n (headEq e)
    where headEq : (c ∷ w) Eq.≡ (a ∷ []) → c Eq.≡ a
          headEq Eq.refl = Eq.refl

  slotL' : (c : Char) (r : RegExp b₁) (s : RegExp b₂) (w : String)
         → ⊗ˢ appop (Derivᶜ.δA c (Aof r s)) w
         → (⟪ δᵣ c r .snd ⟫ ⊗' ⟪ s ⟫) w
  slotL' c r s w ((u , v , sp) , h) =
    (u , v , sp) , λ { true  → δ-complete c r u (h true)
                     ; false → h false }

δ-complete c ∅ᵣ w ()
δ-complete c εᵣ w (() , _)
δ-complete c ⟨ a ⟩ w x = δlit-complete c a (decChar c a) w x
δ-complete c (r ∪ s) w (inl p) = inl (δ-complete c r w p)
δ-complete c (r ∪ s) w (inr q) = inr (δ-complete c s w q)
δ-complete c (_·_ {b₁ = false} r s) w x =
  go (Derivᶜ.δ⊗-fun c (Aof r s) w x)
  where go : _ → (⟪ δᵣ c r .snd ⟫ ⊗' ⟪ s ⟫) w
        go (inl (p , _)) = E.rec (lower (noNil r Eq.refl p))
        go (inr t)       = slotL' c r s w t
δ-complete c (_·_ {b₁ = true} r s) w x =
  go (Derivᶜ.δ⊗-fun c (Aof r s) w x)
  where go : _ → _
        go (inl (_ , q)) = inr (δ-complete c s w q)
        go (inr t)       = inl (slotL' c r s w t)
δ-complete c (r ⋆) w x = go (unroll* (c ∷ w) x)
  where
    go : (ε' ⊕ (⟪ r ⟫ ⊗' KL* ⟪ r ⟫)) (c ∷ w)
       → (⟪ δᵣ c r .snd ⟫ ⊗' KL* ⟪ r ⟫) w
    go (inl (() , _))
    -- `nil` is the case where the body matched ε and the star had to
    -- absorb the character itself.  NON-NULLABILITY kills it, and this
    -- is the ONLY place the index is used.
    go (inr ((_ , _ , nil)     , h)) = E.rec (lower (noNil r Eq.refl (h true)))
    go (inr ((_ , v , cons sp) , h)) =
      (_ , v , sp) , λ { true  → δ-complete c r _ (h true)
                       ; false → h false }

-- THE MATCHER.  Decides the denotation, so there is nothing left to
-- verify about it: `δ-sound`/`δ-complete` carry the whole argument.

decRE : (r : RegExp b) (w : String) → ⟪ r ⟫ w ⊎ No (⟪ r ⟫ w)
decRE r []      = decNil r
decRE r (c ∷ w) = go (decRE (δᵣ c r .snd) w)
  where go : _ → ⟪ r ⟫ (c ∷ w) ⊎ No (⟪ r ⟫ (c ∷ w))
        go (inl p) = inl (δ-sound c r w p)
        go (inr n) = inr λ z → n (δ-complete c r w z)
