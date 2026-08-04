{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
-- Feasibility test: does the internal ⅋ CALCULATE?
--
-- Alphabet = Bool, a = true, b = false.  We test ⅋ as the negative side
-- of the Chu lift for (1) a tensor of literals and (2) one unrolling of
-- Kleene star.  Everything is internal: complements are ¬G, test strings
-- are representables ⌈w⌉, refutations are ⊢-sequents, and the ⅋-choice
-- functions are driven by internal decidability witnesses ⊤ ⊢ A ⊕ ¬G A
-- composed via ⊕-elim and distributivity — never by with-casing a
-- witness.  Pointwise reasoning appears only in the proofs of the
-- decidability atoms and mismatch lemmas (opaque bodies), and at the
-- final run boundary (evaluating a closed term at a string).
module Examples.ParTest where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool)
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_)
open import Cubical.Data.Empty as Empty using ()
import Cubical.Data.Equality as Eq

Alphabet : hSet ℓ-zero
Alphabet = (Bool , isSetBool)

open import Grammar.Base Alphabet
open import Grammar.Bottom Alphabet
open import Grammar.Top Alphabet
open import Grammar.String Alphabet
open import Grammar.Literal Alphabet
open import Grammar.LinearProduct Alphabet
open import Grammar.Function Alphabet using (_⇒_ ; ⇒-intro ; ⇒-app)
open import Grammar.Negation Alphabet
open import Grammar.Epsilon Alphabet using (ε)
open import Grammar.Product.Binary.AsPrimitive Alphabet
  using (_&_ ; &-intro ; π₁ ; π₂ ; &-swap)
open import Grammar.Sum.Binary.AsPrimitive Alphabet
  using (_⊕_ ; inl ; inr ; ⊕-elim ; ⊗⊕-distL ; ⊗⊕-distR)
open import Grammar.Distributivity Alphabet using (&⊕-distL ; &⊕-distR)
open import Grammar.Par.Base Alphabet
open import Term.Base Alphabet

private
  a b : Bool
  a = true
  b = false

  [a] [b] ab ba : String
  [a] = a ∷ []
  [b] = b ∷ []
  ab = a ∷ b ∷ []
  ba = b ∷ a ∷ []

-- The Chu-atom complements and the ⅋-unit, all DSL grammars.
NotLitA NotLitB NES : Grammar ℓ-zero
NotLitA = ¬G (literal a)
NotLitB = ¬G (literal b)
NES = ¬G ε

-- Discriminate a ⊕-value at the run boundary.
isInl : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} → X ⊎ Y → Bool
isInl (Sum.inl _) = true
isInl (Sum.inr _) = false

opaque
  unfolding _⊗_ _⇒_ _⊕_ _&_ ε ⊤ ⊤-intro ⇒-intro ⇒-app &-intro π₁ π₂
            inl inr ⊕-elim ⊗⊕-distL ⊗⊕-distR ⊗-intro literal ⊥-elim
            mk⌈⌉ uniquely-supported-⌈⌉Eq

  -- ══════════════════════════════════════════════════════════════
  -- Internal decidability atoms: ⊤ ⊢ A ⊕ ¬G A, proven pointwise once;
  -- everything downstream composes them via ⊕-elim + distributivity.
  -- ══════════════════════════════════════════════════════════════

  dec-litA : ⊤ ⊢ (literal a ⊕ ¬G (literal a))
  dec-litA [] _ = Sum.inr (λ ())
  dec-litA (true ∷ []) _ = Sum.inl Eq.refl
  dec-litA (false ∷ []) _ = Sum.inr (λ ())
  dec-litA (x ∷ y ∷ rest) _ = Sum.inr (λ ())

  dec-ε : ⊤ ⊢ (ε ⊕ ¬G ε)
  dec-ε [] _ = Sum.inl Eq.refl
  dec-ε (x ∷ rest) _ = Sum.inr (λ ())

  -- A representable refutes any grammar empty at its string.
  ⌈⌉⊢¬ : ∀ {ℓA} {A : Grammar ℓA} (u : String) → (A u → Empty.⊥) → ⌈ u ⌉ ⊢ ¬G A
  ⌈⌉⊢¬ {A = A} u nAu w pu pA =
    nAu (Eq.transport A (Eq.sym (uniquely-supported-⌈⌉Eq u w pu)) pA)

  -- Mismatch lemmas: internal statements, pointwise proofs.
  head-mismatch-ba : (⌈ ba ⌉ & (literal a ⊗ ⊤)) ⊢ ⊥
  head-mismatch-ba w' (pba , (s , plit , _)) =
    clash (rightEq s)
      (Eq.transport (λ z → z Eq.≡ [a] ++ rightEq s)
        (Eq.sym (uniquely-supported-⌈⌉Eq ba w' pba))
        (Eq.transport (λ z → w' Eq.≡ z ++ rightEq s) plit (s .snd)))
    where
    clash : ∀ w₂ → ba Eq.≡ [a] ++ w₂ → Empty.⊥
    clash _ ()

  len-mismatch-ab : (⌈ ab ⌉ & (literal a ⊗ ε)) ⊢ ⊥
  len-mismatch-ab w' (pab , (s , plit , peps)) =
    clash
      (Eq.transport (λ z → z Eq.≡ [a] ++ [])
        (Eq.sym (uniquely-supported-⌈⌉Eq ab w' pab))
        (Eq.transport (λ z → w' Eq.≡ [a] ++ z) peps
          (Eq.transport (λ z → w' Eq.≡ z ++ rightEq s) plit (s .snd))))
    where
    clash : ab Eq.≡ [a] ++ [] → Empty.⊥
    clash ()

  -- ══════════════════════════════════════════════════════════════
  -- Test 1: tensor of literals.  ba ∉ lit a ⊗ lit b — the refutation is
  -- a uniform combinator pipeline: attach dec-litA to the left factor,
  -- distribute, and eliminate.  No index inspection at all.
  -- ══════════════════════════════════════════════════════════════

  refuteBA : ⌈ ba ⌉ ⊢ (NotLitA ⅋ NotLitB)
  refuteBA = ⅋-intro λ u v →
    ⊕-elim
      (⊥-elim ∘g head-mismatch-ba
        ∘g &-intro π₁ ((π₂ ,⊗ ⊤-intro) ∘g π₂))
      (inl ∘g (π₂ ,⊗ id) ∘g π₂)
    ∘g &⊕-distL
    ∘g &-intro π₁
        (⊗⊕-distR
         ∘g ((&⊕-distL ∘g &-intro id (dec-litA ∘g ⊤-intro)) ,⊗ id)
         ∘g π₂)

  -- ab ∈ lit a ⊗ lit b: no refutation exists (internal disjointness).
  noRefuteAB : (⌈ ab ⌉ & (NotLitA ⅋ NotLitB)) ⊢ ⊥
  noRefuteAB =
    ⊕-elim
      (λ w' → λ { ((s , nla , pv) , pab) →
        nla (Eq.transport (literal a) (forceL w' s pv pab) Eq.refl) })
      (λ w' → λ { ((s , pu , nlb) , pab) →
        nlb (Eq.transport (literal b) (forceR w' s pu pab) Eq.refl) })
    ∘g &⊕-distR
    ∘g &-swap
    ∘g &-intro π₁ (⅋-app [a] [b] ∘g &-intro π₂ (input ∘g π₁))
    where
    input : ⌈ ab ⌉ ⊢ (⌈ [a] ⌉ ⊗ ⌈ [b] ⌉)
    input w' pab =
      Eq.transport (λ z → (⌈ [a] ⌉ ⊗ ⌈ [b] ⌉) z)
        (uniquely-supported-⌈⌉Eq ab w' pab)
        ((([a] , [b]) , Eq.refl) , mk⌈⌉ [a] , mk⌈⌉ [b])

    forceL : ∀ w' (s : SplittingEq w') → ⌈ [b] ⌉ (rightEq s) → ⌈ ab ⌉ w'
      → [a] Eq.≡ leftEq s
    forceL w' s pv pab =
      cancelL (leftEq s) (rightEq s)
        (Eq.transport (λ z → z Eq.≡ leftEq s ++ rightEq s)
          (Eq.sym (uniquely-supported-⌈⌉Eq ab w' pab)) (s .snd))
        (uniquely-supported-⌈⌉Eq [b] _ pv)
      where
      cancelL : ∀ w₁ w₂ → ab Eq.≡ w₁ ++ w₂ → [b] Eq.≡ w₂ → [a] Eq.≡ w₁
      cancelL [] _ () Eq.refl
      cancelL (x ∷ []) _ Eq.refl Eq.refl = Eq.refl
      cancelL (x ∷ y ∷ []) _ () Eq.refl
      cancelL (x ∷ y ∷ z ∷ r) _ () Eq.refl

    forceR : ∀ w' (s : SplittingEq w') → ⌈ [a] ⌉ (leftEq s) → ⌈ ab ⌉ w'
      → [b] Eq.≡ rightEq s
    forceR w' s pu pab =
      cancelR (leftEq s) (rightEq s)
        (Eq.transport (λ z → z Eq.≡ leftEq s ++ rightEq s)
          (Eq.sym (uniquely-supported-⌈⌉Eq ab w' pab)) (s .snd))
        (uniquely-supported-⌈⌉Eq [a] _ pu)
      where
      cancelR : ∀ w₁ w₂ → ab Eq.≡ w₁ ++ w₂ → [a] Eq.≡ w₁ → [b] Eq.≡ w₂
      cancelR _ _ Eq.refl Eq.refl = Eq.refl

  -- ══════════════════════════════════════════════════════════════
  -- Test 2: one unrolling of Kleene star's negative functor
  -- F⁻ X = NES & (NotLitA ⅋ X), continuation stand-in X := NES.
  -- Two nested internal decisions: dec-litA on the left factor, then
  -- dec-ε on the right factor.
  -- ══════════════════════════════════════════════════════════════

  parStar-ab : ⌈ ab ⌉ ⊢ (NotLitA ⅋ NES)
  parStar-ab = ⅋-intro λ u v →
    ⊕-elim
      (⊕-elim
         (⊥-elim ∘g len-mismatch-ab
           ∘g &-intro π₁ ((π₂ ,⊗ π₂) ∘g π₂))
         (inr ∘g (π₁ ,⊗ π₂) ∘g π₂)
       ∘g &⊕-distL
       ∘g &-intro π₁
           (⊗⊕-distL
            ∘g (id ,⊗ (&⊕-distL ∘g &-intro id (dec-ε ∘g ⊤-intro)))
            ∘g π₂))
      (inl ∘g (π₂ ,⊗ id) ∘g π₂)
    ∘g &⊕-distL
    ∘g &-intro π₁
        (⊗⊕-distR
         ∘g ((&⊕-distL ∘g &-intro id (dec-litA ∘g ⊤-intro)) ,⊗ id)
         ∘g π₂)

  refuteStar-ab : ⌈ ab ⌉ ⊢ (NES & (NotLitA ⅋ NES))
  refuteStar-ab = &-intro (⌈⌉⊢¬ ab (λ ())) parStar-ab

  -- a ∈ a*: no one-level refutation of [a] exists.
  noRefuteStar-a : (⌈ [a] ⌉ & (NES & (NotLitA ⅋ NES))) ⊢ ⊥
  noRefuteStar-a =
    ⊕-elim
      (λ w' → λ { ((s , nla , pv) , pa) →
        nla (Eq.transport (literal a) (forceL w' s pv pa) Eq.refl) })
      (λ w' → λ { ((s , pu , nes) , pa) →
        nes (Eq.sym (forceR w' s pu pa)) })
    ∘g &⊕-distR
    ∘g &-swap
    ∘g &-intro π₁ (⅋-app [a] [] ∘g &-intro (π₂ ∘g π₂) (input ∘g π₁))
    where
    input : ⌈ [a] ⌉ ⊢ (⌈ [a] ⌉ ⊗ ⌈ [] ⌉)
    input w' pa =
      Eq.transport (λ z → (⌈ [a] ⌉ ⊗ ⌈ [] ⌉) z)
        (uniquely-supported-⌈⌉Eq [a] w' pa)
        ((([a] , []) , Eq.refl) , mk⌈⌉ [a] , mk⌈⌉ [])

    forceL : ∀ w' (s : SplittingEq w') → ⌈ [] ⌉ (rightEq s) → ⌈ [a] ⌉ w'
      → [a] Eq.≡ leftEq s
    forceL w' s pv pa =
      cancelL (leftEq s) (rightEq s)
        (Eq.transport (λ z → z Eq.≡ leftEq s ++ rightEq s)
          (Eq.sym (uniquely-supported-⌈⌉Eq [a] w' pa)) (s .snd))
        (uniquely-supported-⌈⌉Eq [] _ pv)
      where
      cancelL : ∀ w₁ w₂ → [a] Eq.≡ w₁ ++ w₂ → [] Eq.≡ w₂ → [a] Eq.≡ w₁
      cancelL [] _ () Eq.refl
      cancelL (x ∷ []) _ Eq.refl Eq.refl = Eq.refl
      cancelL (x ∷ y ∷ r) _ () Eq.refl

    forceR : ∀ w' (s : SplittingEq w') → ⌈ [a] ⌉ (leftEq s) → ⌈ [a] ⌉ w'
      → [] Eq.≡ rightEq s
    forceR w' s pu pa =
      cancelR (leftEq s) (rightEq s)
        (Eq.transport (λ z → z Eq.≡ leftEq s ++ rightEq s)
          (Eq.sym (uniquely-supported-⌈⌉Eq [a] w' pa)) (s .snd))
        (uniquely-supported-⌈⌉Eq [a] _ pu)
      where
      cancelR : ∀ w₁ w₂ → [a] Eq.≡ w₁ ++ w₂ → [a] Eq.≡ w₁ → [] Eq.≡ w₂
      cancelR _ _ Eq.refl Eq.refl = Eq.refl

  -- ══════════════════════════════════════════════════════════════
  -- Run boundary: evaluate the closed internal terms at their strings
  -- and check the ⅋-choice normalises by refl.
  -- ══════════════════════════════════════════════════════════════

  result-ba : Bool
  result-ba =
    isInl ((⅋-app [b] [a] ∘g
             &-intro (refuteBA) (λ w' pw →
               Eq.transport (λ z → (⌈ [b] ⌉ ⊗ ⌈ [a] ⌉) z)
                 (uniquely-supported-⌈⌉Eq ba w' pw)
                 ((([b] , [a]) , Eq.refl) , mk⌈⌉ [b] , mk⌈⌉ [a])))
           ba (mk⌈⌉ ba))

  computes-ba : result-ba Eq.≡ true
  computes-ba = Eq.refl

  result-star : Bool
  result-star =
    isInl ((⅋-app [a] [b] ∘g
             &-intro (parStar-ab) (λ w' pw →
               Eq.transport (λ z → (⌈ [a] ⌉ ⊗ ⌈ [b] ⌉) z)
                 (uniquely-supported-⌈⌉Eq ab w' pw)
                 ((([a] , [b]) , Eq.refl) , mk⌈⌉ [a] , mk⌈⌉ [b])))
           ab (mk⌈⌉ ab))

  computes-star : result-star Eq.≡ false
  computes-star = Eq.refl
