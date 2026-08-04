{-
  A generic precedence parser.

  A `PrecedenceSpec` describes an expression language with `nLevels`
  right-associative binary operators, one per precedence level, plus a
  leaf grammar and a bracketing pair:

    L i        → L (i-1) | L (i-1) ⟨op i-1⟩ L i      (1 ≤ i ≤ nLevels)
    L 0        → Leaf | ⟨Open⟩ L nLevels ⟨Close⟩

  Levels are indexed by ℕ with `0` the atom level and `nLevels` the
  loosest-binding operator, which is the start symbol.  Levels above
  `nLevels` exist in the grammar but are never reachable, which is what
  lets the index type be plain ℕ — and hence lets the parser recurse
  structurally on the level rather than on a bounded index.

  The parser is a single Löb-guarded fixed point taken at the *indexed
  product* of one parser per level, `&[ i ∈ ℕ ] MaybeLeft (G i)`, since
  the levels are mutually recursive: level `i` needs level `i-1` before
  its operator, and level `0` needs the top level inside brackets.
  Guarded recursive calls are licensed by the operator (resp. opening
  bracket) being a literal, hence non-nullable.

  `Semantics` then packages the generic semantic action: give a value
  type, a reading of the leaf grammar, and a binary operation per level.
-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Parser.Precedence (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function using (uncurry)

open import Cubical.Data.Bool using (Bool ; true ; false ; isSetBool)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.List.Properties using (¬cons≡nil)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import Cubical.Data.Maybe as Mb
import Cubical.Data.Sum as Sum

open import Grammar Alphabet renaming (NIL to *NIL) hiding (Δ)
open import Grammar.Maybe.Base Alphabet hiding (μ)
open import Grammar.SemanticAction Alphabet
open import Grammar.Later.Base Alphabet
open import Grammar.Later.Properties Alphabet
open import Grammar.SequentialUnambiguity.Nullable Alphabet
open import Parser.Base Alphabet hiding (Parser)
open import Parser.RecursiveDescent Alphabet
open import Term Alphabet

open StrongEquivalence

private
  variable
    ℓA ℓB ℓY : Level
    A : Grammar ℓA
    B : Grammar ℓB

-- `▷ A x = ∀ y → y <ˢ x → A y` is a plain Π, so it is functorial.  Used
-- to project a single level's parser out of the guarded bundle.
▷-map : A ⊢ B → ▷ A ⊢ ▷ B
▷-map f w α y y<w = f y (α y y<w)

data OpTag : Type ℓ-zero where
  up app : OpTag

data AtomTag : Type ℓ-zero where
  leaf parens pre : AtomTag

isSetOpTag : isSet OpTag
isSetOpTag = isSetRetract enc dec retr isSetBool
  where
    enc : OpTag → Bool
    enc up = true
    enc app = false
    dec : Bool → OpTag
    dec true = up
    dec false = app
    retr : (t : OpTag) → dec (enc t) ≡ t
    retr up = refl
    retr app = refl

isSetAtomTag : isSet AtomTag
isSetAtomTag = isSetRetract enc dec retr (Sum.isSet⊎ isSetBool isSetUnit)
  where
    enc : AtomTag → (Bool Sum.⊎ Unit)
    enc leaf = Sum.inl true
    enc parens = Sum.inl false
    enc pre = Sum.inr tt
    dec : (Bool Sum.⊎ Unit) → AtomTag
    dec (Sum.inl true) = leaf
    dec (Sum.inl false) = parens
    dec (Sum.inr tt) = pre
    retr : (t : AtomTag) → dec (enc t) ≡ t
    retr leaf = refl
    retr parens = refl
    retr pre = refl

------------------------------------------------------------------------------
-- The specification of a precedence language
------------------------------------------------------------------------------

record PrecedenceSpec : Type (ℓ-suc ℓ-zero) where
  field
    -- Number of binary-operator levels; `opG i` is the operator grammar
    -- of the level immediately above level `i`, so the levels used are
    -- `opG 0` (tightest) up to `opG (nLevels - 1)` (loosest).
    nLevels : ℕ
    opG : ℕ → Grammar ℓ-zero
    LeafG OpenG CloseG : Grammar ℓ-zero
    -- Unary operators, binding tighter than every binary level.  Use
    -- `⊥*` for a language without them.
    PrefixG : Grammar ℓ-zero

    isSetGrammarOp : ∀ i → isSetGrammar (opG i)
    isSetGrammarLeaf : isSetGrammar LeafG
    isSetGrammarOpen : isSetGrammar OpenG
    isSetGrammarClose : isSetGrammar CloseG
    isSetGrammarPrefix : isSetGrammar PrefixG

    -- One-token lookahead, consulted in the order leaf, open, prefix.
    asOp : (c : ⟨ Alphabet ⟩) (i : ℕ) → Mb.Maybe (＂ c ＂ ⊢ opG i)
    asLeaf : (c : ⟨ Alphabet ⟩) → Mb.Maybe (＂ c ＂ ⊢ LeafG)
    asOpen : (c : ⟨ Alphabet ⟩) → Mb.Maybe (＂ c ＂ ⊢ OpenG)
    asClose : (c : ⟨ Alphabet ⟩) → Mb.Maybe (＂ c ＂ ⊢ CloseG)
    asPrefix : (c : ⟨ Alphabet ⟩) → Mb.Maybe (＂ c ＂ ⊢ PrefixG)

module Precedence (S : PrecedenceSpec) where
  open PrecedenceSpec S

  ----------------------------------------------------------------------------
  -- The grammar
  ----------------------------------------------------------------------------

  Ty : ℕ → SPFunctor ℕ
  Ty zero =
    ⊕e AtomTag
      λ where
        leaf → k LeafG
        parens → k OpenG ⊗e Var nLevels ⊗e k CloseG
        pre → k PrefixG ⊗e Var 0
  Ty (suc i) =
    ⊕e OpTag
      λ where
        up → Var i
        app → Var i ⊗e k (opG i) ⊗e Var (suc i)

  G : ℕ → Grammar ℓ-zero
  G = μ Ty

  TOP : Grammar ℓ-zero
  TOP = G nLevels

  UP : ∀ i → G i ⊢ G (suc i)
  UP i = roll ∘g σ up ∘g liftG

  APP : ∀ i → G i ⊗ opG i ⊗ G (suc i) ⊢ G (suc i)
  APP i = roll ∘g σ app ∘g liftG ,⊗ liftG ,⊗ liftG

  LEAF : LeafG ⊢ G 0
  LEAF = roll ∘g σ leaf ∘g liftG

  PARENS : OpenG ⊗ TOP ⊗ CloseG ⊢ G 0
  PARENS = roll ∘g σ parens ∘g liftG ,⊗ liftG ,⊗ liftG

  PRE : PrefixG ⊗ G 0 ⊢ G 0
  PRE = roll ∘g σ pre ∘g liftG ,⊗ liftG

  isSetValuedTy : ∀ i → isSetValued (Ty i)
  isSetValuedTy zero =
    isSetAtomTag , λ { leaf → isSetGrammarLeaf
                     ; parens → isSetGrammarOpen , (tt* , isSetGrammarClose)
                     ; pre → isSetGrammarPrefix , tt* }
  isSetValuedTy (suc i) =
    isSetOpTag , λ { up → tt* ; app → tt* , (isSetGrammarOp i , tt*) }

  isSetGrammarG : ∀ i → isSetGrammar (G i)
  isSetGrammarG i = isSetGrammarμ Ty isSetValuedTy i

  ----------------------------------------------------------------------------
  -- The parser
  ----------------------------------------------------------------------------

  -- One parser per level, bundled so that a single Löb fixed point ties
  -- all the mutual recursion.
  P : Grammar ℓ-zero
  P = &[ i ∈ ℕ ] MaybeLeft (G i)

  ▷at : ∀ i → ▷ P ⊢ ▷ (MaybeLeft (G i))
  ▷at i = ▷-map (π i)

  -- Level 0: a leaf token, or a bracketed top-level expression.
  atomStep : (▷ P) & string ⊢ MaybeLeft (G 0)
  atomStep =
    ⊕-elim
      (nothing ∘g ⊤-intro)
      (⊕ᴰ-elim perChar
       ∘g &⊕ᴰ-distR≅ .fun
       ∘g id ,&p ⊕ᴰ-distL .fun)
    ∘g &⊕-distL
    ∘g id ,&p unroll-string≅ .fun
    where
      -- The opening bracket is a literal, hence a nonempty known prefix:
      -- peel it and the residual is a strict suffix, where `▷` delivers
      -- the top-level parser.
      parenAtom : (c : ⟨ Alphabet ⟩) → (＂ c ＂ ⊢ OpenG)
        → (▷ P) & (literal c ⊗ string) ⊢ MaybeLeft (G 0)
      parenAtom c inj =
        ⊕-elim
          postInner
          (nothing ∘g ⊤-intro)
        ∘g &⊕-distL
        ∘g id ,&p Maybe⊗r
        ∘g id ,&p (⊗-unit-r ,⊗ id)
        ∘g id ,&p (id ,⊗ π₂)
        ∘g id ,&p ▷-app-NE-keep-⌈⌉ ((c ∷ []) , ¬cons≡nil)
        ∘g id ,&p ((⊗-assoc ∘g id ,⊗ ⊗-unit-l⁻) ,&p id)
        ∘g π₁ ,& (&-swap ∘g ▷at nLevels ,&p id)
        where
          -- The inner expression parsed; the leftover must start with a
          -- closing bracket.
          postInner : (▷ P) & (＂ c ＂ ⊗ TOP ⊗ string) ⊢ MaybeLeft (G 0)
          postInner =
            ⊕-elim
              (nothing ∘g ⊤-intro)
              (⊕ᴰ-elim closeChar
               ∘g &⊕ᴰ-distR≅ .fun
               ∘g id ,&p ⊕ᴰ-distR .fun
               ∘g id ,&p (id ,⊗ ⊕ᴰ-distR .fun)
               ∘g id ,&p (id ,⊗ id ,⊗ ⊕ᴰ-distL .fun))
            ∘g &⊕-distL
            ∘g id ,&p ⊗⊕-distL
            ∘g id ,&p (id ,⊗ ⊗⊕-distL)
            ∘g id ,&p (id ,⊗ id ,⊗ unroll-string≅ .fun)
            where
              closeChar : (d : ⟨ Alphabet ⟩) →
                (▷ P) & (＂ c ＂ ⊗ TOP ⊗ literal d ⊗ string) ⊢ MaybeLeft (G 0)
              closeChar d = go (asClose d)
                where
                  go : Mb.Maybe (＂ d ＂ ⊢ CloseG) →
                    (▷ P) & (＂ c ＂ ⊗ TOP ⊗ literal d ⊗ string)
                    ⊢ MaybeLeft (G 0)
                  go Mb.nothing = nothing ∘g ⊤-intro
                  go (Mb.just cinj) =
                    just
                    ∘g (PARENS ∘g inj ,⊗ id ,⊗ cinj) ,⊗ id
                    ∘g ⊗-assoc
                    ∘g id ,⊗ ⊗-assoc
                    ∘g π₂

      -- A unary prefix operator: consume it and recurse (later) at the
      -- atom level, which is guarded because the operator is a literal.
      preAtom : (c : ⟨ Alphabet ⟩) → (＂ c ＂ ⊢ PrefixG)
        → (▷ P) & (literal c ⊗ string) ⊢ MaybeLeft (G 0)
      preAtom c inj =
        fmap (PRE ,⊗ id
              ∘g (inj ,⊗ id) ,⊗ id
              ∘g ⊗-assoc)
        ∘g Maybe⊗r
        ∘g ▷-app-NE (disjoint-ε-literal c)
        ∘g &-swap
        ∘g ▷at 0 ,&p (id ,⊗ ⊤-intro)

      perChar : (c : ⟨ Alphabet ⟩) →
        (▷ P) & (literal c ⊗ string) ⊢ MaybeLeft (G 0)
      perChar c = go (asLeaf c) (asOpen c) (asPrefix c)
        where
          go : Mb.Maybe (＂ c ＂ ⊢ LeafG) → Mb.Maybe (＂ c ＂ ⊢ OpenG)
             → Mb.Maybe (＂ c ＂ ⊢ PrefixG) →
            (▷ P) & (literal c ⊗ string) ⊢ MaybeLeft (G 0)
          go (Mb.just inj) _ _ = just ∘g (LEAF ∘g inj) ,⊗ id ∘g π₂
          go Mb.nothing (Mb.just inj) _ = parenAtom c inj
          go Mb.nothing Mb.nothing (Mb.just inj) = preAtom c inj
          go Mb.nothing Mb.nothing Mb.nothing = nothing ∘g ⊤-intro

  -- Level i+1: having parsed a level-i operand, peek at the leftover.
  -- On the level's operator, consume it and recurse (later) at level
  -- i+1; otherwise promote the operand.
  stepLv : (i : ℕ) → (▷ P) & (G i ⊗ string) ⊢ MaybeLeft (G (suc i))
  stepLv i =
    ⊕-elim
      (just ∘g (UP i ,⊗ *NIL) ∘g π₂)
      (⊕ᴰ-elim nextChar
       ∘g &⊕ᴰ-distR≅ .fun
       ∘g id ,&p ⊕ᴰ-distR .fun
       ∘g id ,&p (id ,⊗ ⊕ᴰ-distL .fun))
    ∘g &⊕-distL
    ∘g id ,&p ⊗⊕-distL
    ∘g id ,&p (id ,⊗ unroll-string≅ .fun)
    where
      nextChar : (c : ⟨ Alphabet ⟩) →
        (▷ P) & (G i ⊗ literal c ⊗ string) ⊢ MaybeLeft (G (suc i))
      nextChar c = go (asOp c i)
        where
          go : Mb.Maybe (＂ c ＂ ⊢ opG i) →
            (▷ P) & (G i ⊗ literal c ⊗ string) ⊢ MaybeLeft (G (suc i))
          go Mb.nothing = just ∘g UP i ,⊗ string-intro ∘g π₂
          go (Mb.just inj) =
            fmap (APP i ,⊗ id
                  ∘g (id ,⊗ inj ,⊗ id) ,⊗ id
                  ∘g ⊗-assoc
                  ∘g id ,⊗ ⊗-assoc
                  ∘g ⊗-assoc⁻)
            ∘g Maybe⊗r
            ∘g ▷-app-NE (¬Nullable⊗r (disjoint-ε-literal c))
            ∘g &-swap
            ∘g ▷at (suc i) ,&p reshape
            where
              reshape : G i ⊗ literal c ⊗ string ⊢ (G i ⊗ literal c) ⊗ ⊤
              reshape = id ,⊗ ⊤-intro ∘g ⊗-assoc

  -- Structural recursion on the level: parse everything tighter first,
  -- then climb one level.
  parseAt : (i : ℕ) → (▷ P) & string ⊢ MaybeLeft (G i)
  parseAt zero = atomStep
  parseAt (suc i) =
    ⊕-elim (stepLv i) (nothing ∘g ⊤-intro)
    ∘g &⊕-distL
    ∘g π₁ ,& parseAt i

  step : ▷ P ⊢ P
  step = &ᴰ-intro parseAt ∘g id ,& string-intro

  isSetGrammarP : isSetGrammar P
  isSetGrammarP = isSetGrammar&ᴰ (λ i → isSetMaybeLeft (isSetGrammarG i))

  parsers : ⊤ ⊢ P
  parsers = lob isSetGrammarP step

  parseTOP : Parser TOP
  parseTOP = π nLevels ∘g parsers ∘g ⊤-intro

  recognize : string ⊢ Maybe TOP
  recognize = parse parseTOP

  ----------------------------------------------------------------------------
  -- The generic semantic action
  ----------------------------------------------------------------------------

  -- The operators are *read*, not just matched, so a level whose
  -- operator grammar carries data — say `⊕[ p ∈ W ] ＂ mix p ＂` for a
  -- weight-indexed choice — can act on that data.
  module Semantics {ℓY} (Y : Type ℓY)
    (leafSem : SemanticAction LeafG Y)
    (preSem : SemanticAction PrefixG (Y → Y))
    (opSem : (i : ℕ) → SemanticAction (opG i) (Y → Y → Y))
    where

    semAlg : ∀ i → ⟦ Ty i ⟧ (λ _ → Δ Y) ⊢ Δ Y
    semAlg zero = ⊕ᴰ-elim λ where
      leaf → semact-lift leafSem
      parens → semact-right (semact-left (semact-lift semact-Δ))
      pre →
        semact-map (λ (f , v) → f v)
          (semact-concat
            (semact-lift preSem)
            (semact-lift semact-Δ))
    semAlg (suc i) = ⊕ᴰ-elim λ where
      up → semact-lift semact-Δ
      app →
        semact-map (λ (a , (f , b)) → f a b)
          (semact-concat
            (semact-lift semact-Δ)
            (semact-concat
              (semact-lift (opSem i))
              (semact-lift semact-Δ)))

    eval : TOP ⊢ Δ Y
    eval = semact-rec semAlg nLevels

    -- Parse a whole string and evaluate.
    evaluate : string ⊢ Maybe (Δ Y)
    evaluate = fmap eval ∘g recognize

    -- Parse a prefix and evaluate, returning the leftover input.
    partial : string ⊢ Maybe (Δ (Y × String))
    partial = fmap (semact-concat eval semact-string) ∘g parseTOP
