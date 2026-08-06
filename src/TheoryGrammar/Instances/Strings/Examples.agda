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

open import TheoryGrammar.Enumerable
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

-- the two leaves ...
leafA : Deriv ntA (true ∷ [])
leafA = G.sup (inl (true , Eq.refl) , lift Eq.refl) λ ()

leafB : Deriv ntB (false ∷ [])
leafB = G.sup (inl (false , Eq.refl) , lift Eq.refl) λ ()

-- ... and a parse tree for "ab" from S.  The type is a GRAMMAR, so the
-- word it parses is in the index and cannot drift from the tree.
parseAB : Deriv ntS (true ∷ false ∷ [])
parseAB = G.sup
  ( inr (ntA , ntB , tt)
  , (((true ∷ []) , (false ∷ []) , cons nil)
    , λ { true  → λ { true → tt* ; false → lift (literalNN true  _ Eq.refl) }
        ; false → λ { true → tt* ; false → lift (literalNN false _ Eq.refl) } }) )
  λ { (true  , (true  , _)) → leafA
    ; (false , (true  , _)) → leafB
    ; (true  , (false , ()))
    ; (false , (false , ())) }

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

-- Observing the parser: `MaybeG-E` into a constant grammar, via
-- `TheoryGrammar.View.maybe→Bool`.  Matching `inl`/`inr` here was a
-- phase violation -- the eliminator exists.
succeeded : (A : Gr) → Cover (MaybeG A) → Cover (λ _ → Bool)
succeeded = maybe→Bool

-- "ab" parses from S, "ba" does not, and "a" parses from A
_ : succeeded (Deriv ntS) (parse ntS) (true ∷ false ∷ []) tt ≡ true
_ = refl

_ : succeeded (Deriv ntS) (parse ntS) (false ∷ true ∷ []) tt ≡ false
_ = refl

_ : succeeded (Deriv ntA) (parse ntA) (true ∷ []) tt ≡ true
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

-- ... and observing the DECISION: `⊕-E` into a constant grammar, via
-- `TheoryGrammar.View.probe→Bool`.  `DecG A` is `Dec⟨ A ⟩`, so
-- `decide P` is a `Probe`.
isYes : (A : Gr) → Probe A → Cover (λ _ → Bool)
isYes = probe→Bool

-- "ab" is derivable from S; "ba" is REFUTED, not merely unfound
_ : isYes (Deriv ntS) (decide ntS) (true ∷ false ∷ []) tt ≡ true
_ = refl

_ : isYes (Deriv ntS) (decide ntS) (false ∷ true ∷ []) tt ≡ false
_ = refl

_ : isYes (Deriv ntA) (decide ntA) (true ∷ []) tt ≡ true
_ = refl
