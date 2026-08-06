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
open import TheoryGrammar.Fibered
open import TheoryGrammar.Inductive
open import TheoryGrammar.Graded

open import TheoryGrammar.Enumerable
import TheoryGrammar.Decidable.Enumerated as DE
open DE using (module DecEnum)
open import TheoryGrammar.Instances.Strings.Enumeration Char public

-- the cut search, and the two abbreviations its hypothesis is stated in
open DecEnum strFib using (⊗at; Refutes; dec-⊗-cuts)

-- `¬G_` and `Dec⟨_⟩` are the generic ones (`Decidable.Additive`, via
-- `DecFib` in `Strings.Base`); this instance defines neither.

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

  Der : G.Ix → Type₀
  Der = G.μ CYKF

  -- ================================================================
  -- THE DESCRIPTION, READ AS CONNECTIVES.
  --
  -- `⟦_⟧c` (Inductive) is the description spelled in the connectives:
  -- `⊕e` IS `⊕ᴰ`, `&e` IS `&ᴰ`, `⊗e` IS `⊗ˢ`, `⌜_⌝` IS `Liftg`, all
  -- DEFINITIONALLY.  So the abbreviations below are grammars, and
  --
  --     Layer P         ≡ ⊕ᴰ (Rule P) (RuleG P)
  --     RuleG P (inl _) ≡ Liftg ⌈ c ∷ [] ⌉
  --     RuleG P (inr _) ≡ SlotG Q ⊗' SlotG T
  --     SlotG Q         ≡ &ᴰ Bool (λ b → …)   -- Deriv Q, and its resource
  --
  -- hold on the nose.  That is what lets the generic `dec-⊕ᴰ` /
  -- `dec-⊗-cuts` / `dec-&ᴰ` be applied to a DESCRIPTION with no
  -- coercion anywhere.
  -- ================================================================

  Layer : V → Gr
  Layer P = G.⟦ CYKF P ⟧c Der

  RuleG : (P : V) → Rule P → Gr
  RuleG P r = G.⟦ ruleF P r ⟧c Der

  SlotG : V → Gr
  SlotG Q = G.⟦ NEvar Q ⟧c Der

  binSlots : V → V → Bool → Gr
  binSlots Q T a = G.⟦ binSlot Q T a ⟧c Der

  -- ================================================================
  -- THE FIXED POINT, as maps of the calculus.  `Inductive` explains why
  -- `rollg`/`unrollg` cannot be stated generically (a level
  -- stratification, not a mathematical obstruction) and says to define
  -- them per instance, where the levels are concrete.  These are the
  -- only place `sup` / `toC` / `fromC` appear outside `leaf` / `node`.
  -- ================================================================

  unrollD : (P : V) → Deriv P ⊢ Layer P
  unrollD P w t = G.toC (CYKF P) w (G.unroll t)

  rollD : (P : V) → Layer P ⊢ Deriv P
  rollD P w t = G.roll (G.fromC (CYKF P) w t)

  -- ================================================================
  -- THE RESOURCE CERTIFICATE A SLOT CARRIES -- a term.
  --
  -- `NEslot Q false = ⌜ NonTrivial ⌝`, so projecting the `false`
  -- component of a slot and discharging the constant former's `Lift`
  -- says: a slot of a binary rule certifies ITS OWN part to be
  -- non-trivial.  This one term is the whole content of "CNF has no
  -- ε-productions", and it is `&ᴰ-E` followed by `lowerg`.
  -- ================================================================

  neOf : (Q : V) → SlotG Q ⊢ NonTrivial
  neOf Q = lowerg ∘g &ᴰ-E Bool {B = λ b → G.⟦ NEslot Q b ⟧c Der} false

  derOf : (Q : V) → SlotG Q ⊢ Deriv Q
  derOf Q = &ᴰ-E Bool {B = λ b → G.⟦ NEslot Q b ⟧c Der} true

  -- ================================================================
  -- Guardedness.  Both slots of a binary rule are proper parts, so this
  -- is the uniform rule -- CNF is precisely the shape that makes it so.
  --
  -- PRIMITIVE (phase 1): `neOfSh` is `neOf` at the level of SHAPES,
  -- which is where guardedness lives (`Guarded` is stated with
  -- `Sh`/`Pos`/`nx`).  It is the only place a shape is looked at, and it
  -- is the shape analogue of a term that already exists.
  -- ================================================================

  neOfSh : (Q : V) (w : String) → G.Sh (NEvar Q) w → NonTrivial w
  neOfSh Q w sh = lower (sh false)

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
      pr Q T m sp sh true  p = neOfSh T (MonParts appop m sp false) (sh false)
      pr Q T m sp sh false p = neOfSh Q (MonParts appop m sp true)  (sh true)

      alt : (r : Rule P) → G.Guarded (ruleF P r)
      alt (inl (c , _))     = G.<⌜⌝ ⌈ c ∷ [] ⌉
      alt (inr (Q , T , _)) =
        G.<⊗e appop (binSlot Q T) (≤binSlot Q T) (pr Q T)

-- Every word is trivial or not.  This IS the decomposition axiom with
-- its branches swapped -- no argument left to make, because the
-- resource predicate is defined as the non-trivial branch.
--
-- `caseOf` is `withView` at `B = ⊤G`, where the payload is vacuous and
-- the `with` degenerates to `_∘g_`.  Every view used at `⊤` has this
-- shape; see `TheoryGrammar.View`.
decNT : Cover (NonTrivial ⊕ ⌈ [] ⌉)
decNT = caseOf charCase ⊕-I₂ ⊕-I₁

-- PRIMITIVE (phase 1): the empty word is trivial.  The only fact about
-- the resource predicate that is not already a term.
¬NT[] : No (NonTrivial [])
¬NT[] (c , (u , v , s) , h) = go (h true) s
  where go : u Eq.≡ c ∷ [] → Split3 u v [] → E.⊥* {ℓ-zero}
        go Eq.refl ()

-- ... so non-triviality is DECIDED, as an internal probe: the cover
-- `decNT` says every word is trivial or not, and `¬NT[]` turns the
-- trivial branch into a refutation.  `⌈⌉-E` is what carries a fact
-- known at ONE world to a map out of that world's representable, so
-- this is a composite of combinators and one primitive.
probe-NT : Probe NonTrivial
probe-NT = caseOf decNT
             (dec-yes NonTrivial)
             (⌈⌉-E {a = []} {B = Dec⟨ NonTrivial ⟩} (dec-no NonTrivial [] ¬NT[]))

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

    -- Alternation and the search over a finite list of alternatives are
    -- `TheoryGrammar.Result`'s `altM` / `altListM`, at the error grammar
    -- `⊤G`.  They used to be spelled out here as `orElse` / `alt2` /
    -- two `List` folds; nothing about them was specific to CYK.

    module _ (P : V) (w : String) (rec : G.▷ Mot (P , w)) where

      -- the constant grammar at this world, which is what a step of the
      -- SEMANTIC löb below is forced to work at -- see the FIXME
      Here : Gr
      Here _ = Deriv P w

      search : {Y : Type₀} → List Y → (Y → Mot (P , w)) → Mot (P , w)
      search {Y = Y} ys f = altListM Here Y ys (λ y _ _ → f y) w tt

      tryCut : (Q T : V) → binR P Q T → MonSplit appop w → Mot (P , w)
      tryCut Q T pf (u , v , s) = go (decNT u tt) (decNT v tt)
        where
          go : (NonTrivial ⊕ ⌈ [] ⌉) u → (NonTrivial ⊕ ⌈ [] ⌉) v → Mot (P , w)
          go (inl neu) (inl nev) =
            join (rec (Q , u) (split3LenL< s (ntLen nev)))
                 (rec (T , v) (split3LenR< s (ntLen neu)))
            where join : Mot (Q , u) → Mot (T , v) → Mot (P , w)
                  join (inl tq) (inl tT) = inl (node pf s neu nev tq tT)
                  join _        _        = inr tt
          go _ _ = inr tt

      tryCuts : (Q T : V) → binR P Q T → List (MonSplit appop w) → Mot (P , w)
      tryCuts Q T pf cs = search cs (tryCut Q T pf)

      tryRule : Rule P → Mot (P , w)
      tryRule (inl (c , pf))     = fromLit (matchLit c w tt)
        where fromLit : MaybeG ⌈ c ∷ [] ⌉ w → Mot (P , w)
              fromLit (inl q) = inl (leaf c pf q)
              fromLit (inr _) = inr tt
      tryRule (inr (Q , T , pf)) = tryCuts Q T pf (cuts w)

      tryRules : List (Rule P) → Mot (P , w)
      tryRules rs = search rs tryRule

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
  -- THE DECISION.  `Dec⟨ Deriv P ⟩ = Deriv P ⊕ ¬G Deriv P`, decided by
  -- `löb` whose step is a named `▷ … ⊢ᴵ …` term, and every layer of
  -- that term is a combinator:
  --
  --     dec-map (Layer P) (Deriv P) (rollD P) (unrollD P)
  --       ∘ dec-⊕ᴰ  (Rule P)          -- search the rules
  --           ∘ per rule:
  --               dec-map … ∘ litProbe c        -- the terminal
  --               dec-⊗-cuts appop …            -- search the cuts
  --                 ∘ per cut: dec-elim probe-NT …
  --                     ∘ dec-&ᴰ                -- nonterminal + resource
  --
  -- The two searches -- over rules and over cuts -- are the SAME
  -- combinator (`Enumerable.decΣ`, wrapped as `dec-⊕ᴰ` and
  -- `dec-⊗-cuts`), because `⊕ᴰ` over the tags and `⊗ˢ` over the
  -- splittings are both `Σ`s.
  --
  -- `dec-⊗-cuts` asks for a decision of each cut AS A WHOLE, not of
  -- each slot separately, and that is what makes the guarded call
  -- legal: a cut with a trivial side is refuted outright (by `neOf`,
  -- since a slot certifies its own part non-trivial), and a cut with
  -- neither side trivial has both sides PROPER, hence strictly shorter
  -- by `deg<`.  See `Instances.Spans.CYK`, which is the same term over
  -- the span theory.
  -- ================================================================

  module Decide (allRules    : (P : V) → List (Rule P))
                (allComplete : (P : V) (r : Rule P) → r ∈L allRules P)
                (litProbe    : (c : Char) → Probe ⌈ c ∷ [] ⌉) where

    DecMot : G.Ix → Type₀
    DecMot i = Dec⟨ Deriv (i .fst) ⟩ (i .snd)

    -- the terminal alternative, decided.  `Liftg` is the constant
    -- former's coercion and `dec-map` transports the decision across it.
    decLit : (c : Char) → Probe (Liftg ⌈ c ∷ [] ⌉)
    decLit c = dec-map ⌈ c ∷ [] ⌉ (Liftg ⌈ c ∷ [] ⌉) liftg lowerg ∘g litProbe c

    module _ (P : V) (w : String)
             (rec : (j : G.Ix) → G.degIx j < length w → DecMot j) where

      module _ (Q T : V) (sp : MonSplit appop w) where

        private
          u v : String
          u = MonParts appop w sp true
          v = MonParts appop w sp false

          CutDec : Type₀
          CutDec = ⊗at appop (binSlots Q T) w sp
                 ⊎ Refutes appop (binSlots Q T) w sp

          -- a trivial side refutes the cut, because `neOf` says the slot
          -- sitting there certifies its own part to be non-trivial
          missL : (¬G NonTrivial) u → Refutes appop (binSlots Q T) w sp
          missL k h = k (neOf Q u (h true))

          missR : (¬G NonTrivial) v → Refutes appop (binSlots Q T) w sp
          missR k h = k (neOf T v (h false))

          -- neither side trivial: each side is then a PROPER part, and
          -- `deg<` -- the grading's own field -- says a proper part is
          -- strictly smaller, which is exactly what `▷` demands.  So
          -- `split3LenL<` / `split3LenR<` / `ntLen` are used only to
          -- BUILD `strGraded`, never to use it.
          slotDec : (R : V) (t : String) → G.degIx (R , t) < length w
                  → NonTrivial t → Dec⟨ SlotG R ⟩ t
          slotDec R t shorter nt =
            dec-&ᴰ (λ b → G.⟦ NEslot R b ⟧c Der) t
              λ { true  → rec (R , t) shorter
                ; false → dec-yes (Liftg NonTrivial) t
                                  (liftg {A = NonTrivial} t nt) }

          -- `decΠBool` is the arity-finiteness concession, the same one
          -- `DecEnumerable.decAt` makes: the two slots sit at DIFFERENT
          -- words, so combining them is not a `&ᴰ` of the calculus.
          both : NonTrivial u → NonTrivial v → CutDec
          both nu nv =
            decΠBool {B = λ a → binSlots Q T a (MonParts appop w sp a)}
              (slotDec Q u (strGraded .deg< appop w sp true  nv) nu)
              (slotDec T v (strGraded .deg< appop w sp false nu) nv)

        -- THE CUT, decided.  Two nested `dec-elim`s on the resource
        -- probe -- an instance never matches a sum, it eliminates one.
        decCut : CutDec
        decCut =
          dec-elim NonTrivial u
            (λ nu → dec-elim NonTrivial v
                      (λ nv → both nu nv)
                      (λ k → inr (missR k))
                      (probe-NT v tt))
            (λ k → inr (missL k))
            (probe-NT u tt)

      -- one rule, decided: the terminal alternative, or a search over
      -- the cuts.  `cuts` / `enumComplete` are the file's only external
      -- residue.
      decRule : (r : Rule P) → Dec⟨ RuleG P r ⟩ w
      decRule (inl (c , _))     = decLit c w tt
      decRule (inr (Q , T , _)) =
        dec-⊗-cuts appop (binSlots Q T) w (cuts w) (enumComplete appop w)
                   (decCut Q T)

      -- ... and the whole layer: search the rules with `dec-⊕ᴰ`, then
      -- transport the decision across the fixed point with `dec-map`.
      decStep : DecMot (P , w)
      decStep =
        dec-map (Layer P) (Deriv P) (rollD P) (unrollD P) w
          (dec-⊕ᴰ (Rule P) (RuleG P) (allRules P) (allComplete P) w decRule)

    -- the löb step, as a named term of the right type -- projections
    -- only, no match on the index
    step : G.▷ DecMot G.⊢ᴵ DecMot
    step i r = decStep (i .fst) (i .snd) r

    decIx : (i : G.Ix) → DecMot i
    decIx = G.löb step

    -- THE DECISION PROCEDURE, as a term of the calculus.  `Dec⟨ A ⟩` is
    -- `Result (¬G A) A` (TheoryGrammar.Result), so this has the same
    -- shape as `Search.parse` and is observed by the same `accepts?`.
    derives? : (P : V) → ⊤G ⊢ Dec⟨ Deriv P ⟩
    derives? P w _ = decIx (P , w)

    -- ... and the exclusion is free, so it packages as a `Decision`
    derivesDec : (P : V) → Decision (Deriv P) (¬G (Deriv P))
    derivesDec P = decDefault (Deriv P) (derives? P)
