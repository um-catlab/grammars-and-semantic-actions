{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- GENERATION, AT DYCK, COMPUTING. `DyckDec` decides `D`; nothing here is
   added to that file. -}
module TheoryGrammar.GenerateTests where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Unit
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.List
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Enumerable using (No)
open import TheoryGrammar.Enumerable.Listed using (Listed; elts)

-- THE ALPHABET.  Two letters, so a Dyck word is a `List Bool` with
-- `true` for "(" and `false` for ")".

decEqB : (a b : Bool) → (a Eq.≡ b) ⊎ No (a Eq.≡ b)
decEqB true  true  = inl Eq.refl
decEqB false false = inl Eq.refl
decEqB true  false = inr λ ()
decEqB false true  = inr λ ()

open import TheoryGrammar.Instances.Strings.DyckDec Bool decEqB true false

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Generate
open import TheoryGrammar.Generate.FromDec
open import TheoryGrammar.Instances.Strings.Graded Bool using (strGraded)
open import TheoryGrammar.Instances.Strings.Base Bool using (strFib; splitAll; String; accepts?; ¬G_; ⊤G; Δ; okA; run; _∘g_; _⊢_)
open import TheoryGrammar.Theories.Monoid using (MonOp; nilop; appop)

open GenFromDec strGraded ℓ-zero Unit (λ _ → tt) enumSplitL enumArL
  using (fromDec; GenDesc; UpDesc; genμ; upμ; upStream; Draw)

-- 1.  THE EXHAUSTIVE GENERATOR, FOR FREE.

dyckGen : (x : Unit) → GenDesc (dyckF x)
dyckGen x = fromDec (dyckF x) (dyckDec x)

-- Dyck is unambiguous, so a word in the language has exactly one parse
-- tree and a word outside it has none.  `genμ`'s fuel bounds the DEPTH
-- of the tree, not the length of the word.
_ : length (genμ dyckF dyckGen 3 (tt , []))                       ≡ 1
_ = refl

_ : length (genμ dyckF dyckGen 4 (tt , true ∷ false ∷ []))        ≡ 1
_ = refl

_ : length (genμ dyckF dyckGen 5 (tt , true ∷ true ∷ false ∷ false ∷ [])) ≡ 1
_ = refl

_ : length (genμ dyckF dyckGen 5 (tt , true ∷ false ∷ true ∷ false ∷ [])) ≡ 1
_ = refl

-- NOT Dyck words: the search space is empty.  This is generation
-- refuting nothing -- an empty `⋁` makes no claim, which is exactly the
-- `findΣ`/`decΣ` asymmetry.  `dyckProbe` is what carries the refutation.
_ : length (genμ dyckF dyckGen 5 (tt , true ∷ []))                ≡ 0
_ = refl

_ : length (genμ dyckF dyckGen 5 (tt , false ∷ true ∷ []))        ≡ 0
_ = refl

-- ... and running out of fuel is also an empty search space, NOT a
-- refutation.  The word is Dyck; depth 1 cannot reach it.
_ : length (genμ dyckF dyckGen 1 (tt , true ∷ false ∷ []))        ≡ 0
_ = refl

-- 2. THE THEORY'S BOTTOM-UP POINT.

strictStrPoint : StrictPoint strFib
strictStrPoint .opU nilop _ = []
strictStrPoint .opU appop f = f true ++ f false
strictStrPoint .splitU nilop f = tt
strictStrPoint .splitU appop f = f true , f false , splitAll (f true) (f false)
strictStrPoint .partsU nilop f ()
strictStrPoint .partsU appop f true  = Eq.refl
strictStrPoint .partsU appop f false = Eq.refl

-- 3. THE FUZZER'S DESCRIPTION.

dyckUp : (x : Unit) → UpDesc (dyckF x)
dyckUp tt = weights , alt
  where
    -- WEIGHTING IS MULTIPLICITY -- here 1:1, which is the CRITICAL
    -- branching process (`dyckAlt false` has two `Var` slots taken with
    -- probability ½, so mean offspring is 1).
    weights : List Bool
    weights = true ∷ false ∷ []

    alt : (b : Bool) → UpDesc (dyckAlt b)
    alt true  = lift (([] , tt , λ ()) ∷ [])              -- ε at []
    alt false = a₂
      where
        a₄ : (a : Bool) → UpDesc (dyck₄ a)
        a₄ true  = lift (((false ∷ []) , Eq.refl) ∷ [])   -- ")" at ")"
        a₄ false = tt*

        a₃ : (a : Bool) → UpDesc (dyck₃ a)
        a₃ true  = tt*
        a₃ false = a₄

        a₂ : (a : Bool) → UpDesc (dyck₂ a)
        a₂ true  = lift (((true ∷ []) , Eq.refl) ∷ [])    -- "(" at "("
        a₂ false = a₃

-- 4. A PSEUDORANDOM STREAM OF INPUTS.

fuzz : ℕ → ℕ → Seed → List (Maybe (Draw dyckF tt))
fuzz size count sd = upStream dyckF strictStrPoint dyckUp size count tt sd

-- the words, with the failures dropped
fuzzWords : ℕ → ℕ → Seed → List String
fuzzWords size count sd = map fst (catMaybes (fuzz size count sd))

sample₁ : List String
sample₁ = fuzzWords 8 16 2024

-- SIXTEEN DRAWS AT SEED 2024, SIZE 8. Reading `true` as "(" and `false` as
-- ")": ε ε ε (()) () () ε ε ε ε () ε ε (((()))())(()) ε ((()))() The heavy
-- tail of the critical branching process is visible: eleven ε, and one
-- word of length 14 reaching depth 4.
_ : sample₁
  ≡ [] ∷ [] ∷ [] ∷
    (true ∷ true ∷ false ∷ false ∷ []) ∷
    (true ∷ false ∷ []) ∷
    (true ∷ false ∷ []) ∷
    [] ∷ [] ∷ [] ∷ [] ∷
    (true ∷ false ∷ []) ∷
    [] ∷ [] ∷
    (true ∷ true ∷ true ∷ true ∷ false ∷ false ∷ false ∷ true ∷ false ∷
     false ∷ true ∷ true ∷ false ∷ false ∷ []) ∷
    [] ∷
    (true ∷ true ∷ true ∷ false ∷ false ∷ false ∷ true ∷ false ∷ []) ∷
    []
_ = refl

-- ... and no draw exhausted the size: sixteen draws, sixteen successes.
_ : length (fuzz 8 16 2024) ≡ 16
_ = refl

_ : length sample₁ ≡ 16
_ = refl

-- 5. THE TWO DIRECTIONS AGAINST EACH OTHER.

parseCounts : List String → List ℕ
parseCounts = map (λ w → length (genμ dyckF dyckGen 8 (tt , w)))

_ : parseCounts sample₁ ≡ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ 1 ∷ []
_ = refl

-- 6. THE FUZZED TEST SUITE.

open import TheoryGrammar.Generate.Suite
open import TheoryGrammar.SemanticAction using (passes)

open FuzzSuite strFib ℓ-zero Unit (λ _ → tt)
               (λ o m _ → enumSplitL o m .elts) enumArL
  using (fuzzed; world; onWorld; viaA; sizeOf; draws)

-- THE PROGRAM UNDER TEST: `DyckDec`'s decider, run at whatever the fuzzer
-- drew.
-- The TERM, named: `okA` reads the decision on the success branch and
-- leaves the refutation alone, so nothing has left the calculus yet.
dyckOk : ⊤G ⊢ Δ Bool
dyckOk = okA D (¬G D) ∘g dyckProbe

-- ... and `run` is the single exit, here because the fuzzer's `onWorld`
-- takes a function of the world.
dyckAccepts : String → Bool
dyckAccepts = run dyckOk

suite₁ : List (String × Bool)
suite₁ = fuzzed dyckF strictStrPoint dyckUp 8 8 2024 tt
                (world dyckF tt) (onWorld dyckF tt dyckAccepts)

-- EIGHT DRAWS, EIGHT ACCEPTANCES. Not a coincidence to be checked
-- afterwards: the draws are built AT their index, so `true` in the right
-- column is the decider agreeing with a fact the generator already
-- guaranteed.
_ : suite₁ gives
      ([] , true) ∷ ([] , true) ∷ ([] , true) ∷
      (true ∷ true ∷ false ∷ false ∷ [] , true) ∷
      (true ∷ false ∷ [] , true) ∷
      (true ∷ false ∷ [] , true) ∷
      ([] , true) ∷ ([] , true) ∷ []
_ = refl

-- ... and the same draws under a SEMANTIC ACTION on the term: `sizeOf`,
-- the generic node count, against the length of the word it derives.
suite₂ : List (ℕ × ℕ)
suite₂ = fuzzed dyckF strictStrPoint dyckUp 8 8 2024 tt
                (sizeOf dyckF dyckGen tt) (onWorld dyckF tt length)

_ : suite₂ gives
      (1 , 0) ∷ (1 , 0) ∷ (1 , 0) ∷ (5 , 4) ∷ (3 , 2) ∷ (3 , 2) ∷
      (1 , 0) ∷ (1 , 0) ∷ []
_ = refl

-- 7. THE SAME RUN AS A PROPERTY RATHER THAN A SNAPSHOT.

suite₃ : List (ℕ × ℕ)
suite₃ = fuzzed dyckF strictStrPoint dyckUp 8 24 2024 tt
                (sizeOf dyckF dyckGen tt)
                (onWorld dyckF tt (λ w → suc (length w)))

_ : passes suite₃
_ = refl

