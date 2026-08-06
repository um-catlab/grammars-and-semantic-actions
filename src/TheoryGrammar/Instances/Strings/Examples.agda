{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Worked examples at a two-letter alphabet: a parse, a star, and CYK. -}
module TheoryGrammar.Instances.Strings.Examples where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Sigma
open import Cubical.Data.List
import Cubical.Data.Equality as Eq

open import Cubical.Data.Maybe using (Maybe; just; nothing)

open import TheoryGrammar.Enumerable
open import TheoryGrammar.SemanticAction
open import TheoryGrammar.SemanticAction using (passes; _↦_; _at_)
open import TheoryGrammar.Instances.Strings.CYK Bool

-- the grammar `a b` over the two-letter alphabet
ab : Gr
ab = literal true ⊗' literal false

parse-ab : ab (true ∷ false ∷ [])
parse-ab = ⊗-mk (cons nil) Eq.refl Eq.refl

-- a two-element star, built from the star's combinators rather than
-- from constructors of a bespoke datatype
aa : KL* (literal true) (true ∷ true ∷ [])
aa = cons* _ (⊗-mk (cons nil) Eq.refl
       (cons* _ (⊗-mk (cons nil) Eq.refl
         (nil* _ ε-mk))))

-- CYK at a two-letter alphabet:  S → A B,  A → 'a',  B → 'b'
-- (true = 'a', false = 'b').  Rules are TYPES, so a rule may carry
-- evidence rather than just a Bool.

data NT : Type₀ where ntS ntA ntB : NT

unitR : NT → Bool → Type₀
unitR ntS c = ⊥
unitR ntA c = c Eq.≡ true
unitR ntB c = c Eq.≡ false

binR : NT → NT → NT → Type₀
binR ntS ntA ntB = Unit
binR _   _   _   = ⊥

open Parser NT unitR binR

-- The two leaves and the node, built from the DESCRIPTION'S intro
-- rules (`leaf`, `node`).  Nothing here mentions `sup`, shapes,
-- positions, or absurd position patterns -- that is phase-1 vocabulary
-- and an example has no business with it.
leafA : Deriv ntA (true ∷ [])
leafA = leaf true Eq.refl Eq.refl

leafB : Deriv ntB (false ∷ [])
leafB = leaf false Eq.refl Eq.refl

-- a parse tree for "ab" from S.  The type is a GRAMMAR, so the word it
-- parses is in the index and cannot drift from the tree.
parseAB : Deriv ntS (true ∷ false ∷ [])
parseAB = node tt (cons nil)
               (literalNN true  _ Eq.refl)
               (literalNN false _ Eq.refl)
               leafA leafB

-- ==================================================================
-- ... and the parser, as a term.
-- ==================================================================

allRules : (P : NT) → List (Rule P)
allRules ntS = inr (ntA , ntB , tt) ∷ []
allRules ntA = inl (true  , Eq.refl) ∷ []
allRules ntB = inl (false , Eq.refl) ∷ []

-- PRIMITIVE.  External decidability of the carrier -- the one entry
-- point `Decidable.Representable` sanctions, and the only place below
-- where a string is matched or an `inl`/`inr` is written by hand.
decEqB : (a b : Bool) → (a Eq.≡ b) ⊎ No (a Eq.≡ b)
decEqB true  true  = inl Eq.refl
decEqB false false = inl Eq.refl
decEqB true  false = inr λ ()
decEqB false true  = inr λ ()

decEqS : (u v : String) → (u Eq.≡ v) ⊎ No (u Eq.≡ v)
decEqS []      []      = inl Eq.refl
decEqS []      (_ ∷ _) = inr λ ()
decEqS (_ ∷ _) []      = inr λ ()
decEqS (a ∷ u) (b ∷ v) = both (decEqB a b) (decEqS u v)
  where both : (a Eq.≡ b) ⊎ No (a Eq.≡ b) → (u Eq.≡ v) ⊎ No (u Eq.≡ v)
             → ((a ∷ u) Eq.≡ (b ∷ v)) ⊎ No ((a ∷ u) Eq.≡ (b ∷ v))
        both (inl Eq.refl) (inl Eq.refl) = inl Eq.refl
        both (inr k)       _             = inr λ { Eq.refl → k Eq.refl }
        both _             (inr k)       = inr λ { Eq.refl → k Eq.refl }

-- ... and that primitive, re-read as a PROBE: a partial view of the
-- world at a literal.  Everything after this is a combinator.
litProbe : (c : Bool) → Probe ⌈ c ∷ [] ⌉
litProbe c w _ = decEqS w (c ∷ [])

matchLit : (c : Bool) → Cover (MaybeG ⌈ c ∷ [] ⌉)
matchLit c = probe→maybe ⌈ c ∷ [] ⌉ (litProbe c)

open Search allRules matchLit

-- Observing the parser.  `okA` (TheoryGrammar.SemanticAction) is the
-- generic observer: it reads a `Result E A` at ANY error grammar, so
-- the very same combinator observes `parse` here (error `⊤G`) and
-- `derives?` below (error `¬G _`).  The result is a TERM `⊤G ⊢ Δ Bool`;
-- `run` appears only in the `refl` line, and cases are batched with
-- `passes … at …` so the term under test is written once.

parses? : (P : NT) → ⊤G ⊢ Δ Bool
parses? P = okA (Deriv P) ⊤G ∘g parse P

_ : passes (run (parses? ntS) at
             ( (true ∷ false ∷ []) ↦ true
             ∷ (false ∷ true ∷ []) ↦ false
             ∷ [] ))
_ = refl

_ : passes (run (parses? ntA) at ((true ∷ []) ↦ true ∷ []))
_ = refl

-- ==================================================================
-- ... and the DECISION.  `decide` returns a parse or a proof that none
-- exists -- not merely a failure to find one.
-- ==================================================================

allComplete : (P : NT) (r : Rule P) → r ∈L allRules P
allComplete ntS (inl (c , ()))
allComplete ntS (inr (ntS , _   , ()))
allComplete ntS (inr (ntA , ntS , ()))
allComplete ntS (inr (ntA , ntA , ()))
allComplete ntS (inr (ntA , ntB , tt)) = here
allComplete ntS (inr (ntB , _   , ()))
allComplete ntA (inl (true  , Eq.refl)) = here
allComplete ntA (inl (false , ()))
allComplete ntA (inr (_ , _ , ()))
allComplete ntB (inl (false , Eq.refl)) = here
allComplete ntB (inl (true  , ()))
allComplete ntB (inr (_ , _ , ()))

open Decide allRules allComplete decEqS

-- ... and observing the DECISION with the SAME combinator, only at a
-- different error grammar: `Dec⟨ A ⟩` is `Result (¬G A) A`, so
-- `derives? P` and `parse P` have one shape between them.

derives! : (P : NT) → ⊤G ⊢ Δ Bool
derives! P = okA (Deriv P) (¬G Deriv P) ∘g derives? P

-- "ab" is derivable from S; "ba" is REFUTED, not merely unfound
_ : passes (run (derives! ntS) at
             ( (true ∷ false ∷ []) ↦ true
             ∷ (false ∷ true ∷ []) ↦ false
             ∷ [] ))
_ = refl

_ : passes (run (derives! ntA) at ((true ∷ []) ↦ true ∷ []))
_ = refl

-- ==================================================================
-- THE WITNESS, not just the decision.
--
-- A `Bool` throws away everything the parser proved.  What we actually
-- want out is the parse TREE, and reading one out is a SEMANTIC ACTION
-- `Deriv P ⊢ Δ Tree` -- the generic notion, from
-- `TheoryGrammar.SemanticAction`.
--
-- The algebra below is written entirely in the connectives: the
-- description's `⊕e` IS `⊕ᴰ`, its `⊗e` IS `⊗ˢ` and its `&e` IS `&ᴰ`, so
-- the three branches are `⊕ᴰ-E`, `⊗A` and `&ᴰA` and there is not one
-- match on a shape.  `Tree` cannot be fabricated: the action's source is
-- the derivation, so a tree comes out only where a parse went in.
-- ==================================================================

data Tree : Type₀ where
  leafT : Bool → Tree
  nodeT : Tree → Tree → Tree

module AI = ActInd strFib ℓ-zero NT (λ _ → tt)

TreeMot : G.Ix → Type₀
TreeMot i = Δ Tree (i .snd)

cykAlg : AI.ActAlg CYKF (λ _ → Tree)
cykAlg P = ⊕ᴰ-E branch
  where
    -- one branch per production; `ruleF` says what each one's payload is
    branch : (r : Rule P) → G.⟦ ruleF P r ⟧c TreeMot ⊢ Δ Tree
    branch (inl (c , pf))     = pureA Tree (leafT c)
    branch (inr (Q , T , pf)) =
      -- `⊗A` reads both slots of the splitting; `&ᴰA … true` picks the
      -- recursive occurrence out of the (occurrence, non-triviality)
      -- pair that guardedness put there, and `idA` is the subtree.
      -- The `λ { true → … ; false → … }` matches on the ARITY, never on
      -- a term: `binSlot Q T a` is stuck at a variable `a`, and this is
      -- the same use of finiteness that `Readable.λ-decSlots` makes.
      mapA (λ f → nodeT (f true) (f false))
           (⊗A appop {A = λ a → G.⟦ binSlot Q T a ⟧c TreeMot} (λ _ → Tree)
               (λ { true  → &ᴰA Bool true idA
                  ; false → &ᴰA Bool true idA }))

abstractify : (P : NT) → Deriv P ⊢ Δ Tree
abstractify = AI.recA cykAlg

-- The pipeline stays a TERM: `mapR` applies the action on the success
-- branch and leaves the other alone.  ONE action reads the tree out of
-- the incomplete parser ...
parseT : (P : NT) → ⊤G ⊢ Result ⊤G (Δ Tree)
parseT P = mapR ⊤G (Δ Tree) (abstractify P) ∘g parse P

-- ... and out of the DECISION, with no change to the action at all
derivT : (P : NT) → ⊤G ⊢ Result (¬G Deriv P) (Δ Tree)
derivT P = mapR (¬G Deriv P) (Δ Tree) (abstractify P) ∘g derives? P

_ : passes (runΔ Tree ⊤G (parseT ntS) at
             ( (true ∷ false ∷ []) ↦ just (nodeT (leafT true) (leafT false))
             ∷ (false ∷ true ∷ []) ↦ nothing
             ∷ [] ))
_ = refl

_ : passes (runΔ Tree ⊤G (parseT ntA) at
             ((true ∷ []) ↦ just (leafT true) ∷ []))
_ = refl

_ : passes (runΔ Tree _ (derivT ntS) at
             ( (true ∷ false ∷ []) ↦ just (nodeT (leafT true) (leafT false))
             ∷ (false ∷ true ∷ []) ↦ nothing
             ∷ [] ))
_ = refl

-- ==================================================================
-- The remaining maps out of `⊤` in this instance.  A VIEW is a
-- `Cover (P ⊕ Q)`, which is a `Result Q P` -- so `accepts?` reads which
-- branch it took, with no new combinator.
-- ==================================================================

-- ---- `charCase` / `decNT` : "is this word empty?", the decomposition
-- ---- axiom and its swap.  They are each other's complement, and the
-- ---- tests say so.
empty? : ⊤G ⊢ Δ Bool
empty? = okA ⌈ [] ⌉ NonTrivial ∘g charCase

nonTrivial? : ⊤G ⊢ Δ Bool
nonTrivial? = okA NonTrivial ⌈ [] ⌉ ∘g decNT

_ : passes (run empty? at ([] ↦ true ∷ (true ∷ []) ↦ false ∷ []))
_ = refl

_ : passes (run nonTrivial? at
             ( []                  ↦ false
             ∷ (true ∷ [])         ↦ true
             ∷ (true ∷ false ∷ []) ↦ true
             ∷ [] ))
_ = refl

-- ---- `litProbe` / `matchLit` : the literal matcher, at BOTH shapes.
-- ---- `matchLit` is `litProbe` weakened along `toMaybe`, so the two
-- ---- must agree on acceptance -- which is what these check.
lit? : (c : Bool) → ⊤G ⊢ Δ Bool
lit? c = okA ⌈ c ∷ [] ⌉ (¬G ⌈ c ∷ [] ⌉) ∘g litProbe c

litM? : (c : Bool) → ⊤G ⊢ Δ Bool
litM? c = okA ⌈ c ∷ [] ⌉ ⊤G ∘g matchLit c

_ : passes (run (lit? true) at
             ( (true ∷ [])         ↦ true
             ∷ (false ∷ [])        ↦ false
             ∷ []                  ↦ false
             ∷ (true ∷ true ∷ [])  ↦ false
             ∷ [] ))
_ = refl

_ : passes (run (litM? true)  at ((true ∷ []) ↦ true ∷ (false ∷ []) ↦ false ∷ []))
_ = refl

_ : passes (run (litM? false) at ((false ∷ []) ↦ true ∷ []))
_ = refl

-- ==================================================================
-- THE REJECTIONS, AS THEOREMS -- and the CONTRAST, which this instance
-- is the only one that can show, because it has BOTH shapes of the same
-- algorithm.
--
-- `refute` is uniform in the error grammar, so it applies to `parse`
-- and to `derives?` alike.  What comes back is not alike:
--
--     derives?  E = ¬G (Deriv P)   ⟹  Deriv P w → ⊥   -- a theorem
--     parse     E = ⊤G             ⟹  tt              -- nothing
--
-- Both tests above read `↦ false`.  Only one of them says anything
-- about the LANGUAGE; the other says something about the algorithm.
-- ==================================================================

noDeriv : (P : NT) (w : String) → run (derives! P) w ≡ false
        → (¬G Deriv P) w
noDeriv P = refute (Deriv P) (¬G Deriv P) (derives? P)

-- "ba" is REFUTED: no parse tree from S exists for it, at all
no-parse-ba : (¬G Deriv ntS) (false ∷ true ∷ [])
no-parse-ba = noDeriv ntS (false ∷ true ∷ []) refl

-- neither does "aa", and this is a fact about the grammar S → A B
no-parse-aa : (¬G Deriv ntS) (true ∷ true ∷ [])
no-parse-aa = noDeriv ntS (true ∷ true ∷ []) refl

-- ... and the accepting side hands back the derivation itself
yes-parse-ab : Deriv ntS (true ∷ false ∷ [])
yes-parse-ab = witness (Deriv ntS) (¬G Deriv ntS) (derives? ntS)
                       (true ∷ false ∷ []) refl

-- THE CONTRAST.  The same combinator at `parse`, whose error grammar is
-- `⊤G`, yields `Unit` -- there is nothing to hand back.  This is the
-- honest content of an incomplete parser, and it is why `Search` is
-- weaker than `Decide` even though both compute the same booleans.
nothing-from-parse : ⊤G (false ∷ true ∷ [])
nothing-from-parse = refute (Deriv ntS) ⊤G (parse ntS) (false ∷ true ∷ []) refl

-- the literal matcher, both ways: `litProbe` refutes, `matchLit` cannot
no-lit : (¬G ⌈ true ∷ [] ⌉) (false ∷ [])
no-lit = refute ⌈ true ∷ [] ⌉ (¬G ⌈ true ∷ [] ⌉) (litProbe true) (false ∷ []) refl

-- and the views, whose "failure" branch was always positive information:
-- refuting `⌈ [] ⌉` at a non-empty word RETURNS the non-triviality
nonTrivial-ab : NonTrivial (true ∷ false ∷ [])
nonTrivial-ab = refute ⌈ [] ⌉ NonTrivial charCase (true ∷ false ∷ []) refl

