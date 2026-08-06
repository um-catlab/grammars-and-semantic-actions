{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- A context-free grammar in Chomsky normal form IS a description, with
   the non-terminals as the description's non-terminals.  So `Deriv P` --
   the parse trees of `w` from `P` -- is the generic `μ`, a grammar, and
   not a `List` of non-terminal names. -}
open import Cubical.Foundations.Prelude

module TheoryGrammar.Instances.Strings.CYK (Char : Type₀) where

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

open import TheoryGrammar.Enumerable
open import TheoryGrammar.Instances.Strings.Enumeration Char public

-- internal negation and decision, out of the connectives
¬G_ : Gr → Gr
¬G A = A ⇒ ⊥G

DecG : Gr → Gr
DecG A = A ⊕ (¬G A)

module CYK (V : Type₀)
           (unitR : V → Char → Type₀)          -- P → c
           (binR  : V → V → V → Type₀) where   -- P → Q T

  -- the descriptions are indexed by the CFG's own non-terminals
  module G = Guard strGraded ℓ-zero V (λ _ → tt)

  Rule : V → Type₀
  Rule P = (Σ[ c ∈ Char ] unitR P c) ⊎ (Σ[ Q ∈ V ] Σ[ T ∈ V ] binR P Q T)

  -- A recursive occurrence together with a proof its part is non-empty.
  -- That proof is what makes the splitting proper, and CNF's ban on
  -- ε-productions is exactly what supplies it.
  NEslot : V → Bool → G.Functor tt
  NEslot Q true  = G.Var Q
  NEslot Q false = G.⌜ NonTrivial ⌝

  NEvar : V → G.Functor tt
  NEvar Q = G.&e Bool (NEslot Q)

  binSlot : V → V → Bool → G.Functor tt
  binSlot Q T true  = NEvar Q
  binSlot Q T false = NEvar T

  ruleF : (P : V) → Rule P → G.Functor tt
  ruleF P (inl (c , _))     = G.⌜ ⌈ c ∷ [] ⌉ ⌝
  ruleF P (inr (Q , T , _)) = G.⊗e appop (binSlot Q T)

  CYKF : (P : V) → G.Functor tt
  CYKF P = G.⊕e (Rule P) (ruleF P)

  -- THE PARSE TREES of `w` from `P`, as a grammar
  Deriv : V → Gr
  Deriv P w = G.μ CYKF (P , w)

  -- ================================================================
  -- Guardedness.  Both slots of a binary rule are proper parts, so this
  -- is the uniform rule -- CNF is precisely the shape that makes it so.
  -- ================================================================

  ≤NEslot : (Q : V) (b : Bool) → G.Guarded≤ (NEslot Q b)
  ≤NEslot Q true  = G.≤Var Q
  ≤NEslot Q false = G.≤⌜⌝ NonTrivial

  ≤binSlot : (Q T : V) (b : Bool) → G.Guarded≤ (binSlot Q T b)
  ≤binSlot Q T true  = G.≤&e Bool (NEslot Q) (≤NEslot Q)
  ≤binSlot Q T false = G.≤&e Bool (NEslot T) (≤NEslot T)

  cykGuarded : (P : V) → G.Guarded (CYKF P)
  cykGuarded P = G.<⊕e (Rule P) (ruleF P) alt
    where
      pr : (Q T : V) (m : String) (sp : MonSplit appop m)
           (sh : (a : Bool) → G.Sh (binSlot Q T a) (MonParts appop m sp a))
           (a : Bool) → G.Pos (binSlot Q T a) _ (sh a) → StrProper appop m sp a
      pr Q T m (u , v , s) sh true  p = lower (sh false false)
      pr Q T m (u , v , s) sh false p = lower (sh true false)

      alt : (r : Rule P) → G.Guarded (ruleF P r)
      alt (inl (c , _))     = G.<⌜⌝ ⌈ c ∷ [] ⌉
      alt (inr (Q , T , _)) =
        G.<⊗e appop (binSlot Q T) (≤binSlot Q T) (pr Q T)

-- Every word is trivial or not.  This IS the decomposition axiom with
-- its branches swapped -- no argument left to make, because the
-- resource predicate is defined as the non-trivial branch.
decNT : ⊤G ⊢ (NonTrivial ⊕ ⌈ [] ⌉)
decNT = ⊕-E isEmpty isNT ∘g charCase
  where
    Out : Gr
    Out = NonTrivial ⊕ ⌈ [] ⌉

    isEmpty : ⌈ [] ⌉ ⊢ Out
    isEmpty = ⊕-I₂

    isNT : NonTrivial ⊢ Out
    isNT = ⊕-I₁

module Parser (V : Type₀)
              (unitR : V → Char → Type₀)
              (binR  : V → V → V → Type₀) where

  open CYK V unitR binR public

  -- the two constructors of a parse tree, as terms
  leaf : {P : V} {w : String} (c : Char) → unitR P c
       → w Eq.≡ c ∷ [] → Deriv P w
  leaf c pf q = G.sup (inl (c , pf) , lift q) λ ()

  node : {P Q T : V} {w u v : String} → binR P Q T → Split3 u v w
       → NonTrivial u → NonTrivial v → Deriv Q u → Deriv T v → Deriv P w
  node {Q = Q} {T} {u = u} {v} pf s neu nev tq tT =
    G.sup ( inr (Q , T , pf)
          , ((u , v , s) , λ { true  → λ { true → tt* ; false → lift neu }
                             ; false → λ { true → tt* ; false → lift nev } }) )
          λ { (true  , (true  , _)) → tq
            ; (false , (true  , _)) → tT
            ; (true  , (false , ()))
            ; (false , (false , ())) }

  -- THE PARSER.  `allRules` says the grammar is finite; `matchLit` is
  -- the literal matcher, itself a term of the calculus.
  module Search (allRules : (P : V) → List (Rule P))
                (matchLit : (c : Char) → ⊤G ⊢ MaybeG ⌈ c ∷ [] ⌉) where

    Mot : G.Ix → Type₀
    Mot i = MaybeG (Deriv (i .fst)) (i .snd)

    -- Alternation, point-free.  `⊕-E` into an internal hom, so the
    -- first alternative is eliminated by the rule rather than matched.
    orElse : (A : Gr) → MaybeG A ⊢ (MaybeG A ⇒ MaybeG A)
    orElse A = ⊕-E (⇒-I (just-I ∘g &-E₁)) (⇒-I &-E₂)

    alt2 : {X A : Gr} → X ⊢ MaybeG A → X ⊢ MaybeG A → X ⊢ MaybeG A
    alt2 {A = A} f g = ⇒-E (orElse A ∘g f) g

    module _ (P : V) (w : String) (rec : G.▷ Mot (P , w)) where

      tryCut : (Q T : V) → binR P Q T → MonSplit appop w → Mot (P , w)
      tryCut Q T pf (u , v , s) = go (decNT u tt) (decNT v tt)
        where
          go : (NonTrivial ⊕ ⌈ [] ⌉) u → (NonTrivial ⊕ ⌈ [] ⌉) v → Mot (P , w)
          go (inl neu) (inl nev) =
            join (rec (Q , u) (split3LenL< s (ntLen nev)))
                 (rec (T , v) (split3LenR< s (ntLen neu)))
            where join : Mot (Q , u) → Mot (T , v) → Mot (P , w)
                  join (inl tq) (inl tT) = inl (node pf s neu nev tq tT)
                  join _        _        = inr tt*
          go _ _ = inr tt*

      tryCuts : (Q T : V) → binR P Q T → List (MonSplit appop w) → Mot (P , w)
      tryCuts Q T pf []       = inr tt*
      tryCuts Q T pf (c ∷ cs) =
        alt2 {X = ⊤G} (λ _ _ → tryCut Q T pf c)
                      (λ _ _ → tryCuts Q T pf cs) w tt

      tryRule : Rule P → Mot (P , w)
      tryRule (inl (c , pf))     = fromLit (matchLit c w tt)
        where fromLit : MaybeG ⌈ c ∷ [] ⌉ w → Mot (P , w)
              fromLit (inl q) = inl (leaf c pf q)
              fromLit (inr _) = inr tt*
      tryRule (inr (Q , T , pf)) = tryCuts Q T pf (cuts w)

      tryRules : List (Rule P) → Mot (P , w)
      tryRules []       = inr tt*
      tryRules (r ∷ rs) =
        alt2 {X = ⊤G} (λ _ _ → tryRule r) (λ _ _ → tryRules rs) w tt

    -- FIXME (phase violation).  This is a SEMANTIC löb: the step is an
    -- Agda function, not a `▷ Mot ⊢ᴵ Mot` term, so `tryRules` /
    -- `tryCut` / `orElse` below eliminate sums by matching instead of
    -- by `⊕-E`.  The reference idiom is `fixP` in
    -- Grammar/Parser/RecursiveDescent.agda, whose step IS a term.
    --
    -- What is missing is the generic analogue of
    --   ▷-app-NE : ⟨¬Nullable B⟩ → (B ⊗ ⊤) & ▷ A ⊢ B ⊗ A
    -- (Grammar/Later/Properties.agda), which is what lets a `▷` be
    -- consumed INSIDE a tensor.  `TheoryGrammar.Graded` exposes `löb`
    -- but not that rule, so no point-free step can be written yet.
    -- Adding it is the fix; `hyloC` is the alternative, and needs `⅋e`
    -- because parsing must consider ALL splittings, not choose one.
    parseIx : (i : G.Ix) → Mot i
    parseIx = G.löb λ { (P , w) rec → tryRules P w rec (allRules P) }

    -- the procedure, as a term of the calculus
    parse : (P : V) → ⊤G ⊢ MaybeG (Deriv P)
    parse P w _ = parseIx (P , w)

  -- ================================================================
  -- THE DECISION.  `DecG (Deriv P) = Deriv P ⊕ ¬G Deriv P`, decided by
  -- `löb` whose step is a named `▷ … ⊢ᴵ …` term.  Both searches -- over
  -- rules and over splittings -- are the SAME combinator, `decΣ`.
  -- ================================================================

  module Decide (allRules : (P : V) → List (Rule P))
                (allComplete : (P : V) (r : Rule P) → r ∈L allRules P)
                (decEq : (u v : String) → (u Eq.≡ v) ⊎ No (u Eq.≡ v)) where

    Der : G.Ix → Type₀
    Der = G.μ CYKF

    DecMot : G.Ix → Type₀
    DecMot i = DecG (Deriv (i .fst)) (i .snd)

    -- PRIMITIVE (phase 1): the empty word is trivial
    ¬NT[] : No (NonTrivial [])
    ¬NT[] (c , (u , v , s) , h) = go (h true) s
      where go : u Eq.≡ c ∷ [] → Split3 u v [] → E.⊥* {ℓ-zero}
            go Eq.refl ()

    decNTat : (u : String) → NonTrivial u ⊎ No (NonTrivial u)
    decNTat u = out (decNT u tt)
      where out : (NonTrivial ⊕ ⌈ [] ⌉) u → NonTrivial u ⊎ No (NonTrivial u)
            out (inl nt)      = inl nt
            out (inr Eq.refl) = inr ¬NT[]

    module _ (P : V) (w : String)
             (rec : (j : G.Ix) → G.degIx j < length w → DecMot j) where

      Slots : (Q T : V) → MonSplit appop w → Type₀
      Slots Q T sp = (a : Bool) → G.⟦ binSlot Q T a ⟧c Der (MonParts appop w sp a)

      decCut : (Q T : V) (sp : MonSplit appop w)
             → Slots Q T sp ⊎ No (Slots Q T sp)
      decCut Q T (u , v , s) = go (decNTat u) (decNTat v)
        where
          go : NonTrivial u ⊎ No (NonTrivial u)
             → NonTrivial v ⊎ No (NonTrivial v)
             → Slots Q T (u , v , s) ⊎ No (Slots Q T (u , v , s))
          go (inr ku) _        = inr λ f → ku (lower (f true false))
          go _        (inr kv) = inr λ f → kv (lower (f false false))
          go (inl nu) (inl nv) =
            decΠBool (decΠBool (rec (Q , u) (split3LenL< s (ntLen nv)))
                               (inl (lift nu)))
                     (decΠBool (rec (T , v) (split3LenR< s (ntLen nu)))
                               (inl (lift nv)))

      decRule : (r : Rule P) → G.⟦ ruleF P r ⟧c Der w ⊎ No (G.⟦ ruleF P r ⟧c Der w)
      decRule (inl (c , pf)) = lit (decEq w (c ∷ []))
        where lit : (w Eq.≡ c ∷ []) ⊎ No (w Eq.≡ c ∷ [])
                  → G.⟦ ruleF P (inl (c , pf)) ⟧c Der w
                    ⊎ No (G.⟦ ruleF P (inl (c , pf)) ⟧c Der w)
              lit (inl q) = inl (lift q)
              lit (inr k) = inr λ x → k (lower x)
      decRule (inr (Q , T , pf)) =
        decΣ (cuts w) (enumComplete appop w) (decCut Q T)

      decStep : DecMot (P , w)
      decStep = shift (decΣ (allRules P) (allComplete P) decRule)
        where
          shift : G.⟦ CYKF P ⟧c Der w ⊎ No (G.⟦ CYKF P ⟧c Der w) → DecMot (P , w)
          shift (inl t) = inl (G.roll (G.fromC (CYKF P) w t))
          shift (inr k) = inr λ d → k (G.toC (CYKF P) w (G.unroll d))

    -- the löb step, as a named term of the right type -- projections
    -- only, no match on the index
    step : G.▷ DecMot G.⊢ᴵ DecMot
    step i r = decStep (i .fst) (i .snd) r

    decIx : (i : G.Ix) → DecMot i
    decIx = G.löb step

    -- THE DECISION PROCEDURE, as a term of the calculus
    decide : (P : V) → ⊤G ⊢ DecG (Deriv P)
    decide P w _ = decIx (P , w)
