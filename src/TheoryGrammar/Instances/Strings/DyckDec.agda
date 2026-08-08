{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- A TOTAL DYCK PARSER, FROM THE GENERIC THEOREM.
   `Decidable.Inductive.decμ` says: a guarded description over a theory
   with listed splittings is DECIDED. -}
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sum using (_⊎_; inl; inr)
import Cubical.Data.Equality as Eq
open import TheoryGrammar.Enumerable using (No)

-- PARAMETERISED BY THE ALPHABET. The grammar cares only that the two
-- brackets are distinguishable, so the alphabet is a parameter and the one
-- external input -- decidable equality on it -- is a hypothesis.
module TheoryGrammar.Instances.Strings.DyckDec
  (Chr    : Type₀)
  (decEqC : (a b : Chr) → (a Eq.≡ b) ⊎ No (a Eq.≡ b))
  (lp rp  : Chr)
  where

open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.List
open import Cubical.Data.Empty as E using (⊥)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Base
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded
open import TheoryGrammar.Enumerable
open import TheoryGrammar.Enumerable.Listed
open import TheoryGrammar.Decidable.Inductive
open import TheoryGrammar.SemanticAction
open import Cubical.Data.Maybe using (Maybe; just; nothing)

open import TheoryGrammar.Instances.Strings.Enumeration Chr

-- THE THEORY'S OBLIGATION, discharged once: the cuts and the arity are
-- listed.  `enumSplit` / `enumComplete` are `Strings.Enumeration`'s.

enumSplitL : (o : MonOp) (m : String) → Listed (MonSplit o m)
enumSplitL o m .elts     = enumSplit o m
enumSplitL o m .complete = enumComplete o m

enumArL : (o : MonOp) → Listed (MonAr o)
enumArL nilop .elts     = []
enumArL nilop .complete = λ ()
enumArL appop .elts     = true ∷ false ∷ []
enumArL appop .complete true  = here
enumArL appop .complete false = there here

-- opened SELECTIVELY: the `Ind` names (`Functor`, `Sh`, `μ`, ...) already
-- come from `Strings.Graded`'s `Guard`, and re-exporting the same instance
-- under a second path would make every one of them ambiguous.
open DecInd strGraded ℓ-zero Unit (λ _ → tt) enumSplitL enumArL
  using (DecDesc; GuardedD; Reaches; decμ)

-- THE DESCRIPTION.  `⊗e` is binary, so the four-factor body
-- `'(' ⊗ D ⊗ ')' ⊗ D` is three nested `⊗e`s, right-associated.

lparen rparen : Gr
lparen = ⌈ lp ∷ [] ⌉
rparen = ⌈ rp ∷ [] ⌉

dyck₄ : Bool → Functor tt          -- ')' ⊗ D
dyck₄ true  = ⌜ rparen ⌝
dyck₄ false = Var tt

dyck₃ : Bool → Functor tt          -- D ⊗ (')' ⊗ D)
dyck₃ true  = Var tt
dyck₃ false = ⊗e appop dyck₄

dyck₂ : Bool → Functor tt          -- '(' ⊗ (D ⊗ (')' ⊗ D))
dyck₂ true  = ⌜ lparen ⌝
dyck₂ false = ⊗e appop dyck₃

dyckAlt : Bool → Functor tt
dyckAlt true  = ⌜ ε' ⌝
dyckAlt false = ⊗e appop dyck₂

dyckF : Unit → Functor tt
dyckF _ = ⊕e Bool dyckAlt

-- THE GRAMMAR: the parse trees of `w` as a Dyck word.
D : Gr
D w = μ dyckF (tt , w)

-- GUARDEDNESS -- the file's one real proof.

private
  Ok : String → Ix → Type₀
  Ok m j = degIx j < length m

  -- a literal pins its factor: the left slot has length 1
  lenL : {u : String} → Sh (⌜ lparen ⌝) u → 0 < length u
  lenL sh = go (lower sh)
    where go : {u : String} → u Eq.≡ (lp ∷ []) → 0 < length u
          go Eq.refl = ≤-refl

dyckGuarded : (x : Unit) (m : String) → GuardedD (dyckF x) m
dyckGuarded tt m true  = tt*
dyckGuarded tt m false = outer
  where
    outer : (sp : MonSplit appop m)
          → ((a : Bool) → Sh (dyck₂ a) (MonParts appop m sp a))
          → (a : Bool) → Reaches (dyck₂ a) (MonParts appop m sp a) (Ok m)
    outer (u , v , s) shs true  = tt*
    outer (u , v , s) shs false = mid
      where
        -- the right factor is strictly shorter, because the left is "("
        vLt : length v < length m
        vLt = split3LenR< s (lenL (shs true))

        mid : (sp₂ : MonSplit appop v)
            → ((a : Bool) → Sh (dyck₃ a) (MonParts appop v sp₂ a))
            → (a : Bool) → Reaches (dyck₃ a) (MonParts appop v sp₂ a) (Ok m)
        mid (u₂ , v₂ , s₂) shs₂ true  = lift (≤<-trans (split3LenL s₂) vLt)
        mid (u₂ , v₂ , s₂) shs₂ false = inner
          where
            inner : (sp₃ : MonSplit appop v₂)
                  → ((a : Bool) → Sh (dyck₄ a) (MonParts appop v₂ sp₃ a))
                  → (a : Bool) → Reaches (dyck₄ a) (MonParts appop v₂ sp₃ a) (Ok m)
            inner (u₃ , v₃ , s₃) shs₃ true  = tt*
            inner (u₃ , v₃ , s₃) shs₃ false =
              lift (≤<-trans (≤-trans (split3LenR s₃) (split3LenR s₂)) vLt)

-- WHAT THE GRAMMAR OWES: the alternatives are listed, and the three
-- constants are decided.  Pure inspection.

listedBool : Listed Bool
listedBool .elts     = true ∷ false ∷ []
listedBool .complete true  = here
listedBool .complete false = there here

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

-- ... AND THAT PRIMITIVE, RE-READ AS AN INTERNAL PROBE.
litProbe : (v : String) → Probe ⌈ v ⌉
litProbe v u _ = decEqS u v

decEps : (m : String) → ε' m ⊎ No (ε' m)
decEps []      = inl (tt , λ ())
decEps (_ ∷ _) = inr λ { (() , _) }

dyckDec : (x : Unit) → DecDesc (dyckF x)
dyckDec tt = listedBool , alt
  where
    alt : (b : Bool) → DecDesc (dyckAlt b)
    alt true  = lift λ m _ → decEps m
    alt false = a₂
      where
        a₄ : (a : Bool) → DecDesc (dyck₄ a)
        a₄ true  = lift (litProbe (rp ∷ []))
        a₄ false = tt*

        a₃ : (a : Bool) → DecDesc (dyck₃ a)
        a₃ true  = tt*
        a₃ false = a₄

        a₂ : (a : Bool) → DecDesc (dyck₂ a)
        a₂ true  = lift (litProbe (lp ∷ []))
        a₂ false = a₃

-- ... AND THE PARSER, as a PROBE.  This one line is the only place the
-- metalanguage `⊎` appears: `Dec⟨ D ⟩ w` IS `D w ⊎ No (D w)`, so `decμ`
-- lands in the calculus definitionally.  Everything below is a term.

dyckProbe : Probe D
dyckProbe w _ = decμ dyckDec dyckGuarded (tt , w)

-- THE PARSE TREE, read out by a SEMANTIC ACTION.

data Tree : Type₀ where
  εT    : Tree
  nodeT : Tree → Tree → Tree

module AI = ActInd strFib ℓ-zero Unit (λ _ → tt)

TreeMot : Ix → Type₀
TreeMot i = Δ Tree (i .snd)

dyckAlg : AI.ActAlg dyckF (λ _ → Tree)
dyckAlg tt = ⊕ᴰ-E branch
  where
    -- ')' ⊗ D  --  drop the literal, keep the subtree
    lvl4 : ⟦ ⊗e appop dyck₄ ⟧c TreeMot ⊢ Δ Tree
    lvl4 = mapA (λ f → f false)
           (⊗A appop {A = λ a → ⟦ dyck₄ a ⟧c TreeMot} (λ _ → Tree)
               (λ { true  → pureA Tree εT ; false → idA }))

    -- D ⊗ (')' ⊗ D)  --  the two subtrees, in order
    lvl3 : ⟦ ⊗e appop dyck₃ ⟧c TreeMot ⊢ Δ Tree
    lvl3 = mapA (λ f → nodeT (f true) (f false))
           (⊗A appop {A = λ a → ⟦ dyck₃ a ⟧c TreeMot} (λ _ → Tree)
               (λ { true  → idA ; false → lvl4 }))

    -- '(' ⊗ (D ⊗ (')' ⊗ D))  --  drop the literal
    lvl2 : ⟦ ⊗e appop dyck₂ ⟧c TreeMot ⊢ Δ Tree
    lvl2 = mapA (λ f → f false)
           (⊗A appop {A = λ a → ⟦ dyck₂ a ⟧c TreeMot} (λ _ → Tree)
               (λ { true  → pureA Tree εT ; false → lvl3 }))

    branch : (b : Bool) → ⟦ dyckAlt b ⟧c TreeMot ⊢ Δ Tree
    branch true  = pureA Tree εT        -- the ε alternative
    branch false = lvl2

readTree : D ⊢ Δ Tree
readTree = AI.recA dyckAlg tt

-- THE PIPELINE, still a term: the action runs on the success branch and
-- the refutation is left alone.  `run` appears only in the `refl` lines.
dyckTree! : ⊤G ⊢ Δ (Maybe Tree)
dyckTree! = maybeA D (¬G D) readTree ∘g dyckProbe

-- the Boolean shadow, for the negative cases
dyck! : ⊤G ⊢ Δ Bool
dyck! = okA D (¬G D) ∘g dyckProbe

-- The tests live in `Instances.Strings.DyckLex`, where the alphabet is
-- instantiated and words can be written as string literals.
