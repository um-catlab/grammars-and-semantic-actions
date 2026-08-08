{- LINEAR CONTEXTS: the `Fibered` of contexts, and everything the typing
   rules need to say about them. -}
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
module TheoryGrammar.Instances.LinTyped.Context where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Empty as E using (⊥*)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Nat using (ℕ; zero; suc; discreteℕ)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit using (Unit; tt)

open import TheoryGrammar.Base
open import TheoryGrammar.Decidable
open import TheoryGrammar.Fibered
open import TheoryGrammar.Instances.LinTyped.Signature
open import TheoryGrammar.Instances.LinTyped.Fibered
open import TheoryGrammar.Instances.LinTyped.Base
open import TheoryGrammar.Instances.LinTyped.Types

-- `Ctx` denotes a linear context: a de Bruijn scope with each slot
-- either owned (`just A`) or spent (`nothing`).
Ctx : Type₀
Ctx = List (Maybe Ty)

-- The ONE place `Discrete` on a carrier is used, and it builds an
-- internal map.  The construction is generic
-- (`Decidable.Representable`); this is only its instantiation at `nm`.
private module R = DecRep (linFib .carrier)

dec-⌈⌉ⁿ : (m : ℕ) → ⊤G ⊢ Dec⟨ Nm m ⟩
dec-⌈⌉ⁿ = R.dec-⌈⌉ {s = nm} discreteℕ

-- THE SPLITTING.  Note the missing constructors -- see the header.

infix 4 _⊎ᶜ_↝_

data _⊎ᶜ_↝_ : Ctx → Ctx → Ctx → Type₀ where
  cnil  : [] ⊎ᶜ [] ↝ []
  cskip : ∀ {Γ₁ Γ₂ Γ} → Γ₁ ⊎ᶜ Γ₂ ↝ Γ
        → (nothing ∷ Γ₁) ⊎ᶜ (nothing ∷ Γ₂) ↝ (nothing ∷ Γ)
  cleft : ∀ {A Γ₁ Γ₂ Γ} → Γ₁ ⊎ᶜ Γ₂ ↝ Γ
        → (just A ∷ Γ₁) ⊎ᶜ (nothing ∷ Γ₂) ↝ (just A ∷ Γ)
  crght : ∀ {A Γ₁ Γ₂ Γ} → Γ₁ ⊎ᶜ Γ₂ ↝ Γ
        → (nothing ∷ Γ₁) ⊎ᶜ (just A ∷ Γ₂) ↝ (just A ∷ Γ)

-- PRIMITIVE (phase 1): LINEARITY IS REAL.  No context that owns a slot
-- splits as itself twice.  The proof is the missing constructor, and
-- nothing else -- compare `LinLam.Context.noDupUse`.
noDupOwn : (A : Ty) (Γ : Ctx)
         → (just A ∷ Γ) ⊎ᶜ (just A ∷ Γ) ↝ (just A ∷ Γ) → E.⊥
noDupOwn A Γ ()

-- ... and NOTHING IS DROPPED: an owned slot on the right of `↝` is
-- owned by exactly one premise.  Again the missing constructor.
noDropOwn : (A : Ty) (Γ₁ Γ₂ Γ : Ctx)
          → (nothing ∷ Γ₁) ⊎ᶜ (nothing ∷ Γ₂) ↝ (just A ∷ Γ) → E.⊥
noDropOwn A Γ₁ Γ₂ Γ ()

-- "nothing is owned", as a RECURSIVE predicate -- valued in
-- `Unit`/`⊥*`, so every consumer computes.

Nil : Ctx → Type₀
Nil []              = Unit
Nil (nothing ∷ Γ)   = Nil Γ
Nil (just _  ∷ Γ)   = ⊥*

-- carried as a CONSTANT grammar at any sort
KNil : {s : TSort} → Ctx → TheoryTy ℓ-zero s
KNil Γ _ = Nil Γ

dec-nil : {s : TSort} (Γ : Ctx) → ⊤G {s} ⊢ Dec⟨ KNil {s} Γ ⟩
dec-nil []            m _ = dec-yes (KNil []) m tt
dec-nil (nothing ∷ Γ) m u = dec-nil Γ m u
dec-nil (just T ∷ Γ)  m _ = dec-no (KNil (just T ∷ Γ)) m λ ()

-- THE VARIABLE RULE'S PREMISE.  `Solo Γ A` denotes "the index I am
-- looking at names the ONE live slot of `Γ`, and that slot holds `A`".

Solo : Ctx → Ty → NmG
Solo []             A n       = ⊥*
Solo (just T ∷ Γ)   A zero    = TyEq A T × Nil Γ
Solo (just T ∷ Γ)   A (suc n) = ⊥*
Solo (nothing ∷ Γ)  A zero    = ⊥*
Solo (nothing ∷ Γ)  A (suc n) = Solo Γ A n

-- `Look Γ` denotes "the index I am looking at owns `Γ` outright, at
-- SOME type" -- and the type is the sum's index, so a derivation
-- carries it.
Look : Ctx → NmG
Look Γ = ⊕ᴰ Ty (Solo Γ)

-- Decidable, by the same recursion `Solo` is defined by.

-- PRIMITIVE (phase 1).  `Solo` recurses on the context AND the index,
-- so its decision does too; every leaf is a framework combinator.
dec-Look : (Γ : Ctx) → ⊤G ⊢ Dec⟨ Look Γ ⟩
dec-Look []             n       _ = dec-no (Look []) n λ { (A , ()) }
dec-Look (just T ∷ Γ)   zero    _ =
  dec-elim (KNil {nm} Γ) zero
    (λ nl → dec-yes (Look (just T ∷ Γ)) zero (T , tyEq-refl T , nl))
    (λ k  → dec-no  (Look (just T ∷ Γ)) zero λ z → k (z .snd .snd))
    (dec-nil {nm} Γ zero tt)
dec-Look (just T ∷ Γ)   (suc n) _ =
  dec-no (Look (just T ∷ Γ)) (suc n) λ { (A , ()) }
dec-Look (nothing ∷ Γ)  zero    _ =
  dec-no (Look (nothing ∷ Γ)) zero λ { (A , ()) }
-- `Look (nothing ∷ Γ) (suc n)` IS `Look Γ n`, definitionally
dec-Look (nothing ∷ Γ)  (suc n) _ = dec-Look Γ n tt

-- THE AMBIENT RELATION. `Blank Γ₁ Γ` denotes "Γ₁ is Γ with some slots
-- blanked": same length, and every slot `Γ₁` owns is owned by `Γ` at the
-- same type.

Blank : Ctx → Ctx → Type₀
Blank []              []              = Unit
Blank []              (_ ∷ _)         = ⊥*
Blank (_ ∷ _)         []              = ⊥*
Blank (nothing ∷ Γ)   (_ ∷ Γ₀)        = Blank Γ Γ₀
Blank (just A ∷ Γ)    (nothing ∷ Γ₀)  = ⊥*
Blank (just A ∷ Γ)    (just B ∷ Γ₀)   = TyEq A B × Blank Γ Γ₀

Blank-refl : (Γ : Ctx) → Blank Γ Γ
Blank-refl []             = tt
Blank-refl (nothing ∷ Γ)  = Blank-refl Γ
Blank-refl (just A ∷ Γ)   = tyEq-refl A , Blank-refl Γ

Blank-trans : (Γ₁ Γ Γ₀ : Ctx) → Blank Γ₁ Γ → Blank Γ Γ₀ → Blank Γ₁ Γ₀
Blank-trans []             []             []            p q = tt
Blank-trans []             []             (_ ∷ _)       p ()
Blank-trans []             (_ ∷ _)        Γ₀            () q
Blank-trans (_ ∷ _)        []             Γ₀            () q
Blank-trans (nothing ∷ Γ₁) (nothing ∷ Γ)  []            p ()
Blank-trans (nothing ∷ Γ₁) (nothing ∷ Γ)  (_ ∷ Γ₀)      p q = Blank-trans Γ₁ Γ Γ₀ p q
Blank-trans (nothing ∷ Γ₁) (just B ∷ Γ)   []            p ()
Blank-trans (nothing ∷ Γ₁) (just B ∷ Γ)   (nothing ∷ _) p ()
Blank-trans (nothing ∷ Γ₁) (just B ∷ Γ)   (just C ∷ Γ₀) p q = Blank-trans Γ₁ Γ Γ₀ p (q .snd)
Blank-trans (just A ∷ Γ₁)  (nothing ∷ Γ)  Γ₀            () q
Blank-trans (just A ∷ Γ₁)  (just B ∷ Γ)   []            p ()
Blank-trans (just A ∷ Γ₁)  (just B ∷ Γ)   (nothing ∷ _) p ()
Blank-trans (just A ∷ Γ₁)  (just B ∷ Γ)   (just C ∷ Γ₀) p q =
  tyEq-trans A B C (p .fst) (q .fst) , Blank-trans Γ₁ Γ Γ₀ (p .snd) (q .snd)

-- both components of a splitting are sub-contexts of the whole
splitBlankL : {Γ₁ Γ₂ Γ : Ctx} → Γ₁ ⊎ᶜ Γ₂ ↝ Γ → Blank Γ₁ Γ
splitBlankL cnil       = tt
splitBlankL (cskip s)  = splitBlankL s
splitBlankL (cleft s)  = tyEq-refl _ , splitBlankL s
splitBlankL (crght s)  = splitBlankL s

splitBlankR : {Γ₁ Γ₂ Γ : Ctx} → Γ₁ ⊎ᶜ Γ₂ ↝ Γ → Blank Γ₂ Γ
splitBlankR cnil       = tt
splitBlankR (cskip s)  = splitBlankR s
splitBlankR (cleft s)  = splitBlankR s
splitBlankR (crght s)  = tyEq-refl _ , splitBlankR s

-- THE LEAF LEMMA, and the reason `Blank` exists.

soloTy : (Γ Γ' Γ₀ : Ctx) (A B : Ty) (n : ℕ)
       → Blank Γ Γ₀ → Blank Γ' Γ₀ → Solo Γ A n → Solo Γ' B n → TyEq A B
soloTy []             Γ'              Γ₀             A B n       p  p' () s'
soloTy (just T ∷ Γ)   []              Γ₀             A B n       p  p' s ()
soloTy (nothing ∷ Γ)  []              Γ₀             A B n       p  p' s ()
soloTy (just T ∷ Γ)   (just T' ∷ Γ')  []             A B n       () p' s s'
soloTy (just T ∷ Γ)   (just T' ∷ Γ')  (nothing ∷ _)  A B n       () p' s s'
soloTy (just T ∷ Γ)   (just T' ∷ Γ')  (just T₀ ∷ Γ₀) A B zero    p  p' s s' =
  tyEq-trans A T B (s .fst)
    (tyEq-trans T T₀ B (p .fst)
      (tyEq-sym B T₀ (tyEq-trans B T' T₀ (s' .fst) (p' .fst))))
soloTy (just T ∷ Γ)   (just T' ∷ Γ')  (just T₀ ∷ Γ₀) A B (suc n) p  p' () s'
soloTy (just T ∷ Γ)   (nothing ∷ Γ')  Γ₀             A B zero    p  p' s ()
soloTy (just T ∷ Γ)   (nothing ∷ Γ')  Γ₀             A B (suc n) p  p' () s'
soloTy (nothing ∷ Γ)  (just T' ∷ Γ')  Γ₀             A B zero    p  p' () s'
soloTy (nothing ∷ Γ)  (just T' ∷ Γ')  Γ₀             A B (suc n) p  p' s ()
soloTy (nothing ∷ Γ)  (nothing ∷ Γ')  Γ₀             A B zero    p  p' () s'
soloTy (nothing ∷ Γ)  (nothing ∷ Γ')  []             A B (suc n) () p' s s'
soloTy (nothing ∷ Γ)  (nothing ∷ Γ')  (_ ∷ Γ₀)       A B (suc n) p  p' s s' =
  soloTy Γ Γ' Γ₀ A B n p p' s s'

-- QUANTIFYING OVER THE SPLITTINGS OF A CONTEXT. `SplitG Γ P` denotes "the
-- context splits SOMEHOW, and the two halves satisfy `P`".

SplitΣ : Ctx → Type₀
SplitΣ Γ = Σ[ Γ₁ ∈ Ctx ] Σ[ Γ₂ ∈ Ctx ] (Γ₁ ⊎ᶜ Γ₂ ↝ Γ)

SplitG : (Γ : Ctx) → (Ctx → Ctx → TmG) → TmG
SplitG Γ P = ⊕ᴰ (SplitΣ Γ) λ z → P (z .fst) (z .snd .fst)

-- PRIMITIVE (phase 1), three pairs: the splittings of a context are
-- read off its head, which is INVERSION on the splitting datatype and
-- so cannot be a combinator.  Everything downstream uses only these.
splitG-nil-out : (P : Ctx → Ctx → TmG) → SplitG [] P ⊢ P [] []
splitG-nil-out P t ((_ , _ , cnil) , p) = p

splitG-nil-in : (P : Ctx → Ctx → TmG) → P [] [] ⊢ SplitG [] P
splitG-nil-in P t p = ([] , [] , cnil) , p

splitG-skip-out : (Γ : Ctx) (P : Ctx → Ctx → TmG)
  → SplitG (nothing ∷ Γ) P
  ⊢ SplitG Γ (λ Γ₁ Γ₂ → P (nothing ∷ Γ₁) (nothing ∷ Γ₂))
splitG-skip-out Γ P t ((_ , _ , cskip s) , p) = (_ , _ , s) , p

splitG-skip-in : (Γ : Ctx) (P : Ctx → Ctx → TmG)
  → SplitG Γ (λ Γ₁ Γ₂ → P (nothing ∷ Γ₁) (nothing ∷ Γ₂))
  ⊢ SplitG (nothing ∷ Γ) P
splitG-skip-in Γ P t ((Γ₁ , Γ₂ , s) , p) = (nothing ∷ Γ₁ , nothing ∷ Γ₂ , cskip s) , p

splitG-just-out : (T : Ty) (Γ : Ctx) (P : Ctx → Ctx → TmG)
  → SplitG (just T ∷ Γ) P
  ⊢ ( SplitG Γ (λ Γ₁ Γ₂ → P (just T ∷ Γ₁) (nothing ∷ Γ₂))
    ⊕ SplitG Γ (λ Γ₁ Γ₂ → P (nothing ∷ Γ₁) (just T ∷ Γ₂)) )
splitG-just-out T Γ P t ((_ , _ , cleft s) , p) = inl ((_ , _ , s) , p)
splitG-just-out T Γ P t ((_ , _ , crght s) , p) = inr ((_ , _ , s) , p)

splitG-just-in : (T : Ty) (Γ : Ctx) (P : Ctx → Ctx → TmG)
  → ( SplitG Γ (λ Γ₁ Γ₂ → P (just T ∷ Γ₁) (nothing ∷ Γ₂))
    ⊕ SplitG Γ (λ Γ₁ Γ₂ → P (nothing ∷ Γ₁) (just T ∷ Γ₂)) )
  ⊢ SplitG (just T ∷ Γ) P
splitG-just-in T Γ P t (inl ((Γ₁ , Γ₂ , s) , p)) =
  (just T ∷ Γ₁ , nothing ∷ Γ₂ , cleft s) , p
splitG-just-in T Γ P t (inr ((Γ₁ , Γ₂ , s) , p)) =
  (nothing ∷ Γ₁ , just T ∷ Γ₂ , crght s) , p

-- ... and hence the decision, by structural recursion on the context.
-- Nothing below matches a splitting; the three views above did it once.
dec-SplitG : (Γ : Ctx) (P : Ctx → Ctx → TmG) (t : Raw)
           → ((Γ₁ Γ₂ : Ctx) → Dec⟨ P Γ₁ Γ₂ ⟩ t)
           → Dec⟨ SplitG Γ P ⟩ t
dec-SplitG [] P t d =
  dec-map (P [] []) (SplitG [] P) (splitG-nil-in P) (splitG-nil-out P) t (d [] [])
dec-SplitG (nothing ∷ Γ) P t d =
  dec-map (SplitG Γ Q) (SplitG (nothing ∷ Γ) P)
          (splitG-skip-in Γ P) (splitG-skip-out Γ P) t
          (dec-SplitG Γ Q t λ Γ₁ Γ₂ → d (nothing ∷ Γ₁) (nothing ∷ Γ₂))
  where
  Q : Ctx → Ctx → TmG
  Q Γ₁ Γ₂ = P (nothing ∷ Γ₁) (nothing ∷ Γ₂)
dec-SplitG (just T ∷ Γ) P t d =
  dec-map (SplitG Γ QL ⊕ SplitG Γ QR) (SplitG (just T ∷ Γ) P)
          (splitG-just-in T Γ P) (splitG-just-out T Γ P) t
          (dec-⊕ (SplitG Γ QL) (SplitG Γ QR) t
            ( dec-SplitG Γ QL t (λ Γ₁ Γ₂ → d (just T ∷ Γ₁) (nothing ∷ Γ₂))
            , dec-SplitG Γ QR t (λ Γ₁ Γ₂ → d (nothing ∷ Γ₁) (just T ∷ Γ₂)) ))
  where
  QL QR : Ctx → Ctx → TmG
  QL Γ₁ Γ₂ = P (just T ∷ Γ₁) (nothing ∷ Γ₂)
  QR Γ₁ Γ₂ = P (nothing ∷ Γ₁) (just T ∷ Γ₂)
