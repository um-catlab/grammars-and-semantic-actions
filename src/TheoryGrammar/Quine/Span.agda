{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{-
  A SELF-PARSING REGION -- the quine, in the theory of SPANS.

  `Quine.Base` is a quine over STRINGS: a program is a whole word, and
  `⌈ src ⌉` pins that word.  Here a program is a REGION `(i , n)` of one
  ambient text, and the index carries WHERE IT SITS.  Two things follow,
  and the second is the reason this file exists.

  (1) A quine can be a FRAGMENT.  `⌈ (i , n) ⌉` pins a span, so
      "this region prints itself" is a statement about a piece of a
      longer text -- and the longer text need not derive from `S` at
      all.  In the string theory there is nothing to say here: the
      program is the input.

  (2) SELF-REFERENCE CAN BE POSITIONAL.  The terminal alternative of the
      span CYK is

          UnitG P = ⊕ᴰ ℕ (λ j → ⌈ (j , 1) ⌉ & (λ _ → unitR P j))

      so a leaf of a parse tree knows its own ABSOLUTE POSITION `j`, and
      a semantic action may use it.  The interpreter below does: the
      value of a terminal is `(the letter , where it sits)`, and the
      root reads the offset off its leftmost leaf.  Nothing about this
      is available in the string theory, where a leaf knows only its
      letter.

  ------------------------------------------------------------------
  THE LANGUAGE.  Three letters, `0`, `1`, `#`.  A region is a program
  when it reads

      c₀ c₁ … c_k  #  e            the CODE, a hash, and the DATA

  with the code a nonempty bit string and the data a nonempty string of
  BIT PAIRS.  As in `Quine.Base`, the data is a QUOTED bit string --
  `x y` decodes to `x`, so `dec (enc a) = a` -- and the decoding is the
  GRAMMAR'S doing (the productions `E → B O`, `O → B E`), not a function
  on strings.

  THE INTERPRETER -- and this is where the theories part.  A program at
  offset `i` with decoded data `d` prints

      emit i d  =  patch i d  ++  "#"  ++  enc (patch i d)

  where `patch i` OVERWRITES THE FIRST LETTER with `addr i`, the parity
  of the offset.  So the interpreter is the classical quine
  construction -- "print the data, then print it quoted" -- composed
  with one position-dependent edit.

  WHEN IS A REGION A QUINE?  Write the region as `C # E` and put
  `d = dec E`.  The output is `patch i d ++ "#" ++ enc (patch i d)`, so
  the region prints itself exactly when

      C = patch i d          and         E = enc C

  The second forces `d = dec (enc C) = C`, and then the first says
  `patch i C = C`, i.e.

      THE FIRST LETTER OF THE CODE IS THE PARITY OF THE OFFSET.

  A program is therefore an ASSERTION ABOUT ITS OWN ADDRESS, and it is a
  quine exactly when that assertion is TRUE.  Consequences, all of them
  checked by evaluation in `Quine.SpanTests`:

    * `0#00` is a quine at every EVEN offset and at no odd one;
      `1#11` is a quine at every ODD offset and at no even one.
    * at the wrong offset each prints THE OTHER: relocating a quine by
      one character does not break it into nonsense, it turns it into
      its sibling.  The pair is a 2-cycle under relocation.
    * so THE SAME FOUR CHARACTERS ARE A QUINE AT ONE POSITION AND NOT AT
      ANOTHER, inside one ambient text.  This is the fact with no
      string-theory analogue.

  NESTING AND OVERLAP.  Since the quines are `C # enc C`, and a subspan
  quine must reuse the one `#`, a quine `C # enc C` at `p` contains a
  shorter quine at `p + j` exactly when `C` has period `j` with
  `0 < j < |C|` and `j` EVEN (even, because the sub-code starts with
  `C j = C 0` and must match the parity of `p + j`).  The smallest case
  is `C = 010`:

      010#001100   at an even offset   contains   0#00   two to its right

  and both are quines.  Overlap without containment needs two `#`s and
  is also available -- `0#00#0000` has quines at `(p , 4)` and
  `(p+2 , 7)`, neither inside the other.

  THE GRAMMAR, in Chomsky normal form and right-linear, as in
  `Quine.Base` (a one-letter left slot keeps the cut scan cheap):

      S → B R            R → B R | H E          H → '#'
      B → '0' | '1'      E → B O                O → '0' | '1' | B E
-}
module TheoryGrammar.Quine.Span where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool hiding (_⊕_; _≤_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.List
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
import Cubical.Data.Equality as Eq

open import TheoryGrammar.Enumerable
open import TheoryGrammar.SemanticAction

open import TheoryGrammar.Instances.Spans.CYK public

-- ==================================================================
-- §0  THE ALPHABET, and the two letter classes as TYPES -- so that
--     "P → any bit" is ONE unit rule and not two.
-- ==================================================================

data Chr : Type₀ where
  c0 c1 c# : Chr

String : Type₀
String = List Chr

Bit? : Chr → Type₀
Bit? c0 = Unit
Bit? c1 = Unit
Bit? c# = ⊥

Hash? : Chr → Type₀
Hash? c0 = ⊥
Hash? c1 = ⊥
Hash? c# = Unit

-- ==================================================================
-- §1  THE GRAMMAR'S SHAPE.  Only `unitR` mentions the ambient text, so
--     the nonterminals and the binary rules live out here, shared by
--     every text.
-- ==================================================================

data NT : Type₀ where ntS ntR ntH ntB ntE ntO : NT

binR : NT → NT → NT → Type₀
binR ntS ntB ntR = Unit      -- S → B R
binR ntR ntB ntR = Unit      -- R → B R
binR ntR ntH ntE = Unit      -- R → H E
binR ntE ntB ntO = Unit      -- E → B O
binR ntO ntB ntE = Unit      -- O → B E
binR _   _   _   = ⊥

-- ==================================================================
-- §2  THE INTERPRETER'S ARITHMETIC.  Three total functions on strings
--     and one on positions; none of them looks at the ambient text.
-- ==================================================================

-- QUOTING -- the classical quine's `quote`, and the only string
-- function in the interpreter.
enc : String → String
enc []      = []
enc (c ∷ s) = c ∷ c ∷ enc s

-- THE ADDRESS, as a letter: the parity of an offset.  This is the whole
-- of the position dependence, and it is the smallest thing that can be
-- said about a position in a two-letter alphabet.
addr : ℕ → Chr
addr zero          = c0
addr (suc zero)    = c1
addr (suc (suc n)) = addr n

-- ... and the edit it drives: overwrite the FIRST letter with the
-- address bit.  `patch i s ≡ s` says "s tells the truth about i".
patch : ℕ → String → String
patch i []      = []
patch i (_ ∷ s) = addr i ∷ s

-- THE ROOT'S MEANING.  What a program sitting at offset `i`, whose data
-- decodes to `d`, prints.
emit : ℕ → String → String
emit i d = patch i d ++ (c# ∷ enc (patch i d))

-- ==================================================================
-- §3  THE AMBIENT TEXT.  Everything from here down is parameterised by
--     ONE function `charAt : ℕ → Chr` -- the whole of "there is a text"
--     in the span theory (`Spans.CYK`: the word enters only through
--     `unitR`).  Instantiating it is what `Quine.SpanTests` does.
-- ==================================================================

module Text (charAt : ℕ → Chr) where

  -- Reading a region back out as a string.  This is the only place a
  -- span is turned into text, and it is what the quine equation's right
  -- hand side is: "the source, at this region".
  textFrom : ℕ → ℕ → String
  textFrom i zero    = []
  textFrom i (suc n) = charAt i ∷ textFrom (suc i) n

  textOf : Span → String
  textOf (i , n) = textFrom i n

  -- THE LEXICAL RULES: "P derives the terminal at position j".
  unitR : NT → ℕ → Type₀
  unitR ntS j = ⊥
  unitR ntR j = ⊥
  unitR ntH j = Hash? (charAt j)
  unitR ntB j = Bit?  (charAt j)
  unitR ntE j = ⊥
  unitR ntO j = Bit?  (charAt j)

  open CYK NT unitR binR public

  -- ================================================================
  -- §3.1  The grammar is FINITE.  Mechanical: for each nonterminal,
  --       every pair that is not a right-hand side reduces to `⊥`.
  -- ================================================================

  allRules : (P : NT) → List (Rule P)
  allRules ntS = inl tt ∷ inr (ntB , ntR , tt) ∷ []
  allRules ntR = inl tt ∷ inr (ntB , ntR , tt) ∷ inr (ntH , ntE , tt) ∷ []
  allRules ntH = inl tt ∷ []
  allRules ntB = inl tt ∷ []
  allRules ntE = inl tt ∷ inr (ntB , ntO , tt) ∷ []
  allRules ntO = inl tt ∷ inr (ntB , ntE , tt) ∷ []

  allComplete : (P : NT) (r : Rule P) → r ∈L allRules P
  allComplete ntS (inl tt)               = here
  allComplete ntS (inr (ntS , _   , ()))
  allComplete ntS (inr (ntR , _   , ()))
  allComplete ntS (inr (ntH , _   , ()))
  allComplete ntS (inr (ntE , _   , ()))
  allComplete ntS (inr (ntO , _   , ()))
  allComplete ntS (inr (ntB , ntS , ()))
  allComplete ntS (inr (ntB , ntR , tt)) = there here
  allComplete ntS (inr (ntB , ntH , ()))
  allComplete ntS (inr (ntB , ntB , ()))
  allComplete ntS (inr (ntB , ntE , ()))
  allComplete ntS (inr (ntB , ntO , ()))
  allComplete ntR (inl tt)               = here
  allComplete ntR (inr (ntS , _   , ()))
  allComplete ntR (inr (ntR , _   , ()))
  allComplete ntR (inr (ntE , _   , ()))
  allComplete ntR (inr (ntO , _   , ()))
  allComplete ntR (inr (ntB , ntS , ()))
  allComplete ntR (inr (ntB , ntR , tt)) = there here
  allComplete ntR (inr (ntB , ntH , ()))
  allComplete ntR (inr (ntB , ntB , ()))
  allComplete ntR (inr (ntB , ntE , ()))
  allComplete ntR (inr (ntB , ntO , ()))
  allComplete ntR (inr (ntH , ntS , ()))
  allComplete ntR (inr (ntH , ntR , ()))
  allComplete ntR (inr (ntH , ntH , ()))
  allComplete ntR (inr (ntH , ntB , ()))
  allComplete ntR (inr (ntH , ntE , tt)) = there (there here)
  allComplete ntR (inr (ntH , ntO , ()))
  allComplete ntH (inl tt)               = here
  allComplete ntH (inr (_ , _ , ()))
  allComplete ntB (inl tt)               = here
  allComplete ntB (inr (_ , _ , ()))
  allComplete ntE (inl tt)               = here
  allComplete ntE (inr (ntS , _   , ()))
  allComplete ntE (inr (ntR , _   , ()))
  allComplete ntE (inr (ntH , _   , ()))
  allComplete ntE (inr (ntE , _   , ()))
  allComplete ntE (inr (ntO , _   , ()))
  allComplete ntE (inr (ntB , ntS , ()))
  allComplete ntE (inr (ntB , ntR , ()))
  allComplete ntE (inr (ntB , ntH , ()))
  allComplete ntE (inr (ntB , ntB , ()))
  allComplete ntE (inr (ntB , ntE , ()))
  allComplete ntE (inr (ntB , ntO , tt)) = there here
  allComplete ntO (inl tt)               = here
  allComplete ntO (inr (ntS , _   , ()))
  allComplete ntO (inr (ntR , _   , ()))
  allComplete ntO (inr (ntH , _   , ()))
  allComplete ntO (inr (ntE , _   , ()))
  allComplete ntO (inr (ntO , _   , ()))
  allComplete ntO (inr (ntB , ntS , ()))
  allComplete ntO (inr (ntB , ntR , ()))
  allComplete ntO (inr (ntB , ntH , ()))
  allComplete ntO (inr (ntB , ntB , ()))
  allComplete ntO (inr (ntB , ntE , tt)) = there here
  allComplete ntO (inr (ntB , ntO , ()))

  -- ================================================================
  -- §3.2  THE ONE EXTERNAL INPUT: the lexical table.  Exactly as in
  --       `Spans.Tests.termProbe` -- external decidability enters once,
  --       at a named place, as an INTERNAL probe, and nothing below
  --       ever looks at a span again.
  -- ================================================================

  decBit : (c : Chr) → Bit? c ⊎ No (Bit? c)
  decBit c0 = inl tt
  decBit c1 = inl tt
  decBit c# = inr λ ()

  decHash : (c : Chr) → Hash? c ⊎ No (Hash? c)
  decHash c0 = inr λ ()
  decHash c1 = inr λ ()
  decHash c# = inl tt

  decUnitR : (P : NT) (j : ℕ) → unitR P j ⊎ No (unitR P j)
  decUnitR ntS j = inr λ ()
  decUnitR ntR j = inr λ ()
  decUnitR ntE j = inr λ ()
  decUnitR ntH j = decHash (charAt j)
  decUnitR ntB j = decBit  (charAt j)
  decUnitR ntO j = decBit  (charAt j)

  -- PRIMITIVE (phase 1).  The file's one carrier-destructuring
  -- definition: a terminal lives at a span of length exactly one.
  termProbe : (P : NT) → Probe (UnitG P)
  termProbe P (i , zero)        _ = dec-no (UnitG P) _ λ { (j , () , _) }
  termProbe P (i , suc (suc n)) _ = dec-no (UnitG P) _ λ { (j , () , _) }
  termProbe P (i , suc zero)    _ = pick (decUnitR P i)
    where
      pick : unitR P i ⊎ No (unitR P i) → Dec⟨ UnitG P ⟩ (i , 1)
      pick (inl u) = dec-yes (UnitG P) _ (i , Eq.refl , u)
      pick (inr k) = dec-no  (UnitG P) _ λ { (j , Eq.refl , u) → k u }

  open Decide allRules allComplete termProbe public

  -- ================================================================
  -- §4  THE INTERPRETER, as a semantic action.
  --
  -- One meaning per nonterminal, one metalanguage combination per
  -- production -- which is what a `Δ`-valued algebra IS.  The single
  -- difference from `Quine.Base` is the meaning of `B`:
  --
  --     STRINGS:  Val B = Chr              the letter
  --     SPANS:    Val B = Chr × ℕ          the letter, AND ITS ADDRESS
  --
  -- and that is exactly what `UnitG`'s `⊕ᴰ ℕ` makes available.  The
  -- root reads the address off the opcode leaf; every other production
  -- is unchanged.
  -- ================================================================

  module AI = ActInd spanFib ℓ-zero NT (λ _ → tt)

  Val : NT → Type₀
  Val ntS = String                  -- THE OUTPUT
  Val ntR = String                  -- dec of the data
  Val ntH = Unit
  Val ntB = Chr × ℕ                 -- the letter, and where it sits
  Val ntE = String                  -- dec of the data below
  Val ntO = String                  -- dec of the data below

  -- A terminal's meaning is a function of its POSITION -- the ambient
  -- text supplies the letter, the span supplies the address.  (`S`, `R`
  -- and `E` derive no terminal; their clauses are unreachable, in the
  -- same sense as the unreachable `binVal` clauses below.)
  unitVal : (P : NT) (j : ℕ) → Val P
  unitVal ntS j = []                          -- unreachable
  unitVal ntR j = []                          -- unreachable
  unitVal ntE j = []                          -- unreachable
  unitVal ntH j = tt
  unitVal ntB j = (charAt j , j)              -- THE LETTER AND ITS ADDRESS
  unitVal ntO j = []                          -- a pair's second bit: dropped

  binVal : (P Q T : NT) → binR P Q T → Val Q → Val T → Val P
  binVal ntS ntB ntR tt b d = emit (b .snd) d  -- S → B R : RUN, AT ITS OFFSET
  binVal ntR ntB ntR tt _ d = d                -- R → B R : skip a code bit
  binVal ntR ntH ntE tt _ d = d                -- R → H E : the data
  binVal ntE ntB ntO tt b d = b .fst ∷ d       -- E → B O : KEEP the first bit
  binVal ntO ntB ntE tt _ d = d                -- O → B E : DROP the second
  binVal ntS _ _ _ _ _ = []                    -- (unreachable)
  binVal ntR _ _ _ _ _ = []
  binVal ntH _ _ _ _ _ = tt
  binVal ntB _ _ _ _ _ = (c0 , 0)
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
      branch (inl _) =
        ⊕ᴰ-E {Y = ℕ} {A = λ j → ⌈ (j , 1) ⌉ & (λ _ → unitR P j)}
             (λ j → pureA (Val P) (unitVal P j))
        ∘g lowerg
      branch (inr (Q , T , pf)) =
        mapA (λ f → binVal P Q T pf (f true) (f false))
             (⊗A cat {A = λ a → G.⟦ binSlot Q T a ⟧c Mot} (slotX Q T)
                 (λ { true  → &ᴰA Bool true idA
                    ; false → &ᴰA Bool true idA }))

  -- THE INTERPRETER: a parse tree, run.
  interp : (P : NT) → Deriv P ⊢ Δ (Val P)
  interp = AI.recA alg

  -- ================================================================
  -- §5  THE PIPELINE, still a term.  `mapR` applies the interpreter on
  --     the success branch and leaves the refutation alone, so `outD`
  --     is `⊤G ⊢ Result (¬G Deriv P) (Δ (Val P))` and nothing has been
  --     externalised.
  -- ================================================================

  outD : (P : NT) → ⊤G ⊢ Result (¬G Deriv P) (Δ (Val P))
  outD P = mapR (¬G Deriv P) (Δ (Val P)) (interp P) ∘g derives? P

  derives! : (P : NT) → ⊤G ⊢ Δ Bool
  derives! P = okA (Deriv P) (¬G Deriv P) ∘g derives? P

  -- the only externalisations, and they belong in `refl` lines
  runOut : (P : NT) → Span → Maybe (Val P)
  runOut P = runΔ (Val P) (¬G Deriv P) (outD P)

  -- ================================================================
  -- §6  THE QUINE EQUATION, stated in the calculus.
  --
  -- `witness` EXTRACTS the parse tree from the decision -- the tree is
  -- a theorem, not a report -- and `⌈⌉-E` PINS it to the region: `⌈ s ⌉`
  -- holds at one world and that world IS the span, so
  --
  --     ⌈ s ⌉  --selfLit-->  Deriv S  --interp-->  Δ String
  --
  -- is "the region at `s`, parsed and run".  `IsQuineAt s` says that
  -- composite, at the point `⌈⌉-pt s`, is the ambient text of `s`.
  --
  -- By `⌈⌉-UP` a map `⌈ s ⌉ ⊢ Δ String` is just a string, so this is an
  -- equation between two strings -- and, unlike the string theory's, its
  -- right hand side depends on `s` in TWO ways at once: which letters,
  -- and (through `interp`) which offset.
  -- ================================================================

  selfDeriv : (s : Span) → run (derives! ntS) s ≡ true → Deriv ntS s
  selfDeriv = witness (Deriv ntS) (¬G Deriv ntS) (derives? ntS)

  selfLit : (s : Span) → run (derives! ntS) s ≡ true → ⌈ s ⌉ ⊢ Deriv ntS
  selfLit s pf = ⌈⌉-E (selfDeriv s pf)

  IsQuineAt : (s : Span) → run (derives! ntS) s ≡ true → Type₀
  IsQuineAt s pf = (interp ntS ∘g selfLit s pf) s (⌈⌉-pt s) ≡ (textOf s , tt)

  -- ... and a negative answer is a REFUTATION, because the error grammar
  -- is `¬G _`: `noDeriv s refl` is a proof that NO parse tree of the
  -- region exists, not a report that none was found.
  noDeriv : (s : Span) → run (derives! ntS) s ≡ false → (¬G Deriv ntS) s
  noDeriv = refute (Deriv ntS) (¬G Deriv ntS) (derives? ntS)
