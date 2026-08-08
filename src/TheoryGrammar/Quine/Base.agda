{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- A QUINE ENGINE. A quine is a source text whose OUTPUT is its own source. -}
module TheoryGrammar.Quine.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Enumerable
open import TheoryGrammar.SemanticAction

-- §0  THE ALPHABET

data Chr : Type₀ where
  c0 c1 c# : Chr

-- the two letter classes, as TYPES: a unit rule of the CYK description
-- is a type, so "P → any bit" is one rule schema and not two.
Bit? : Chr → Type₀
Bit? c0 = Unit
Bit? c1 = Unit
Bit? c# = ⊥

Hash? : Chr → Type₀
Hash? c0 = ⊥
Hash? c1 = ⊥
Hash? c# = Unit

open import TheoryGrammar.Instances.Strings.CYK Chr public

-- §1  THE GRAMMAR

data NT : Type₀ where ntS ntR ntH ntB ntE ntO : NT

unitR : NT → Chr → Type₀
unitR ntS c = ⊥
unitR ntR c = ⊥
unitR ntH c = Hash? c
unitR ntB c = Bit? c
unitR ntE c = ⊥
unitR ntO c = Bit? c

binR : NT → NT → NT → Type₀
binR ntS ntB ntR = Unit      -- S → B R
binR ntR ntB ntR = Unit      -- R → B R
binR ntR ntH ntE = Unit      -- R → H E
binR ntE ntB ntO = Unit      -- E → B O
binR ntO ntB ntE = Unit      -- O → B E
binR _   _   _   = ⊥

open Parser NT unitR binR public

allRules : (P : NT) → List (Rule P)
allRules ntS = inr (ntB , ntR , tt) ∷ []
allRules ntR = inr (ntB , ntR , tt) ∷ inr (ntH , ntE , tt) ∷ []
allRules ntH = inl (c# , tt) ∷ []
allRules ntB = inl (c0 , tt) ∷ inl (c1 , tt) ∷ []
allRules ntE = inr (ntB , ntO , tt) ∷ []
allRules ntO = inl (c0 , tt) ∷ inl (c1 , tt) ∷ inr (ntB , ntE , tt) ∷ []

-- Completeness.  Mechanical: for each nonterminal, every pair of
-- nonterminals that is NOT a right-hand side reduces to `⊥`.
allComplete : (P : NT) (r : Rule P) → r ∈L allRules P
allComplete ntS (inl (_ , ()))
allComplete ntS (inr (ntS , _ , ()))
allComplete ntS (inr (ntR , _ , ()))
allComplete ntS (inr (ntH , _ , ()))
allComplete ntS (inr (ntE , _ , ()))
allComplete ntS (inr (ntO , _ , ()))
allComplete ntS (inr (ntB , ntS , ()))
allComplete ntS (inr (ntB , ntR , tt)) = here
allComplete ntS (inr (ntB , ntH , ()))
allComplete ntS (inr (ntB , ntB , ()))
allComplete ntS (inr (ntB , ntE , ()))
allComplete ntS (inr (ntB , ntO , ()))
allComplete ntR (inl (_ , ()))
allComplete ntR (inr (ntS , _ , ()))
allComplete ntR (inr (ntR , _ , ()))
allComplete ntR (inr (ntE , _ , ()))
allComplete ntR (inr (ntO , _ , ()))
allComplete ntR (inr (ntB , ntS , ()))
allComplete ntR (inr (ntB , ntR , tt)) = here
allComplete ntR (inr (ntB , ntH , ()))
allComplete ntR (inr (ntB , ntB , ()))
allComplete ntR (inr (ntB , ntE , ()))
allComplete ntR (inr (ntB , ntO , ()))
allComplete ntR (inr (ntH , ntS , ()))
allComplete ntR (inr (ntH , ntR , ()))
allComplete ntR (inr (ntH , ntH , ()))
allComplete ntR (inr (ntH , ntB , ()))
allComplete ntR (inr (ntH , ntE , tt)) = there here
allComplete ntR (inr (ntH , ntO , ()))
allComplete ntH (inl (c0 , ()))
allComplete ntH (inl (c1 , ()))
allComplete ntH (inl (c# , tt)) = here
allComplete ntH (inr (_ , _ , ()))
allComplete ntB (inl (c0 , tt)) = here
allComplete ntB (inl (c1 , tt)) = there here
allComplete ntB (inl (c# , ()))
allComplete ntB (inr (_ , _ , ()))
allComplete ntE (inl (_ , ()))
allComplete ntE (inr (ntS , _ , ()))
allComplete ntE (inr (ntR , _ , ()))
allComplete ntE (inr (ntH , _ , ()))
allComplete ntE (inr (ntE , _ , ()))
allComplete ntE (inr (ntO , _ , ()))
allComplete ntE (inr (ntB , ntS , ()))
allComplete ntE (inr (ntB , ntR , ()))
allComplete ntE (inr (ntB , ntH , ()))
allComplete ntE (inr (ntB , ntB , ()))
allComplete ntE (inr (ntB , ntE , ()))
allComplete ntE (inr (ntB , ntO , tt)) = here
allComplete ntO (inl (c0 , tt)) = here
allComplete ntO (inl (c1 , tt)) = there here
allComplete ntO (inl (c# , ()))
allComplete ntO (inr (ntS , _ , ()))
allComplete ntO (inr (ntR , _ , ()))
allComplete ntO (inr (ntH , _ , ()))
allComplete ntO (inr (ntE , _ , ()))
allComplete ntO (inr (ntO , _ , ()))
allComplete ntO (inr (ntB , ntS , ()))
allComplete ntO (inr (ntB , ntR , ()))
allComplete ntO (inr (ntB , ntH , ()))
allComplete ntO (inr (ntB , ntB , ()))
allComplete ntO (inr (ntB , ntE , tt)) = there (there here)
allComplete ntO (inr (ntB , ntO , ()))

-- §2 THE ONE EXTERNAL INPUT: decidability of the alphabet.

decEqC : (a b : Chr) → (a Eq.≡ b) ⊎ No (a Eq.≡ b)
decEqC c0 c0 = inl Eq.refl
decEqC c1 c1 = inl Eq.refl
decEqC c# c# = inl Eq.refl
decEqC c0 c1 = inr λ ()
decEqC c0 c# = inr λ ()
decEqC c1 c0 = inr λ ()
decEqC c1 c# = inr λ ()
decEqC c# c0 = inr λ ()
decEqC c# c1 = inr λ ()

decEqS : (u v : String) → (u Eq.≡ v) ⊎ No (u Eq.≡ v)
decEqS []      []      = inl Eq.refl
decEqS []      (_ ∷ _) = inr λ ()
decEqS (_ ∷ _) []      = inr λ ()
decEqS (a ∷ u) (b ∷ v) = both (decEqC a b) (decEqS u v)
  where both : (a Eq.≡ b) ⊎ No (a Eq.≡ b) → (u Eq.≡ v) ⊎ No (u Eq.≡ v)
             → ((a ∷ u) Eq.≡ (b ∷ v)) ⊎ No ((a ∷ u) Eq.≡ (b ∷ v))
        both (inl Eq.refl) (inl Eq.refl) = inl Eq.refl
        both (inr k)       _             = inr λ { Eq.refl → k Eq.refl }
        both _             (inr k)       = inr λ { Eq.refl → k Eq.refl }

litProbe : (c : Chr) → Probe ⌈ c ∷ [] ⌉
litProbe c w _ = decEqS w (c ∷ [])

open Decide allRules allComplete litProbe public

-- §3 THE INTERPRETER, as a semantic action.

-- QUOTING: the only string function in the interpreter, and it is the
-- classical quine's `quote`.
enc : String → String
enc []      = []
enc (c ∷ s) = c ∷ c ∷ enc s

-- THE OPCODE'S MEANING.  `emit b d` is what a program with opcode `b`
-- and decoded data `d` prints.
emit : Chr → String → String
emit c0 d = d ++ (c# ∷ enc d)
emit c1 d = enc d ++ (c# ∷ d)
emit c# d = []                      -- unreachable: `B` derives no `#`

module AI = ActInd strFib ℓ-zero NT (λ _ → tt)

-- THE INTERPRETER, parameterised by what the ROOT does.
module Interp (X : Type₀) (x₀ : X) (root : Chr → String → X) where

  Val : NT → Type₀
  Val ntS = X                       -- THE OUTPUT
  Val ntR = String                  -- dec of the data
  Val ntH = Unit
  Val ntB = Chr                     -- the letter
  Val ntE = String                  -- dec of the data below
  Val ntO = String                  -- dec of the data below

  unitVal : (P : NT) (c : Chr) → unitR P c → Val P
  unitVal ntS c ()
  unitVal ntR c ()
  unitVal ntE c ()
  unitVal ntH c pf = tt
  unitVal ntB c pf = c                -- the letter itself
  unitVal ntO c pf = []               -- a pair's second bit: dropped

  binVal : (P Q T : NT) → binR P Q T → Val Q → Val T → Val P
  binVal ntS ntB ntR tt b d = root b d      -- S → B R : run the opcode
  binVal ntR ntB ntR tt _ d = d             -- R → B R : skip a code bit
  binVal ntR ntH ntE tt _ d = d             -- R → H E : the data
  binVal ntE ntB ntO tt b d = b ∷ d         -- E → B O : KEEP the first bit
  binVal ntO ntB ntE tt _ d = d             -- O → B E : DROP the second
  binVal ntS _ _ _ _ _ = x₀                 -- (unreachable)
  binVal ntR _ _ _ _ _ = []
  binVal ntH _ _ _ _ _ = tt
  binVal ntB _ _ _ _ _ = c0
  binVal ntE _ _ _ _ _ = []
  binVal ntO _ _ _ _ _ = []

  Mot : G.Ix → Type₀
  Mot i = Δ (Val (i .fst)) (i .snd)

  alg : AI.ActAlg CYKF Val
  alg P = ⊕ᴰ-E branch
    where
      -- the two slots of a binary rule carry the two nonterminals'
      -- meanings; matching on the ARITY, never on a term
      slotX : NT → NT → Bool → Type₀
      slotX Q T true  = Val Q
      slotX Q T false = Val T

      branch : (r : Rule P) → G.⟦ ruleF P r ⟧c Mot ⊢ Δ (Val P)
      branch (inl (c , pf))     = pureA (Val P) (unitVal P c pf)
      branch (inr (Q , T , pf)) =
        mapA (λ f → binVal P Q T pf (f true) (f false))
             (⊗A appop {A = λ a → G.⟦ binSlot Q T a ⟧c Mot} (slotX Q T)
                 (λ { true  → &ᴰA Bool true idA
                    ; false → &ᴰA Bool true idA }))

  -- THE INTERPRETER: a parse tree, run.
  interp : (P : NT) → Deriv P ⊢ Δ (Val P)
  interp = AI.recA alg

  -- THE PIPELINE, still a term. `mapR` applies the interpreter on the
  -- success branch and leaves the refutation alone, so `outD` is `⊤G ⊢
  -- Result (¬G Deriv P) (Δ (Val P))` and nothing has been externalised.

  outD : (P : NT) → ⊤G ⊢ Result (¬G Deriv P) (Δ (Val P))
  outD P = mapR (¬G Deriv P) (Δ (Val P)) (interp P) ∘g derives? P

  -- the only externalisation, and it belongs in a `refl` line
  runOut : (P : NT) → String → Maybe (Val P)
  runOut P = runΔ (Val P) (¬G Deriv P) (outD P)

derives! : (P : NT) → ⊤G ⊢ Δ Bool
derives! P = okA (Deriv P) (¬G Deriv P) ∘g derives? P

-- THE QUINE INTERPRETER: the root prints.
open Interp String [] emit public
